// Copyright Istio Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"strconv"
	"strings"

	matcher "github.com/cncf/xds/go/xds/type/matcher/v3"
	cluster "github.com/envoyproxy/go-control-plane/envoy/config/cluster/v3"
	core "github.com/envoyproxy/go-control-plane/envoy/config/core/v3"
	listener "github.com/envoyproxy/go-control-plane/envoy/config/listener/v3"
	tcp "github.com/envoyproxy/go-control-plane/envoy/extensions/filters/network/tcp_proxy/v3"
	wrappers "google.golang.org/protobuf/types/known/wrapperspb"

	networking "istio.io/api/networking/v1alpha3"
	"istio.io/istio/pilot/pkg/features"
	"istio.io/istio/pilot/pkg/model"
	istionetworking "istio.io/istio/pilot/pkg/networking"
	"istio.io/istio/pilot/pkg/networking/core/match"
	istio_route "istio.io/istio/pilot/pkg/networking/core/route"
	"istio.io/istio/pilot/pkg/networking/core/tunnelingconfig"
	"istio.io/istio/pilot/pkg/networking/plugin/authz"
	"istio.io/istio/pilot/pkg/networking/util"
	"istio.io/istio/pilot/pkg/util/protoconv"
	xdsfilters "istio.io/istio/pilot/pkg/xds/filters"
	"istio.io/istio/pkg/config/host"
	"istio.io/istio/pkg/config/protocol"
	"istio.io/istio/pkg/log"
	"istio.io/istio/pkg/slices"
	"istio.io/istio/pkg/util/sets"
	"istio.io/istio/pkg/wellknown"
)

// gatewayWildcardTLSInternalName is the name of the internal listener of all wildcard DYNAMIC_DNS destinations of
// ISTIO_MUTUAL gateway servers, and of the cluster that sends to it.
const gatewayWildcardTLSInternalName = "wildcard_tls_internal"

// gatewayWildcardTLSTarget is a wildcard DYNAMIC_DNS destination of an ISTIO_MUTUAL gateway server. As on a
// waypoint, the real host is only visible on an internal listener, after the gateway terminates the mTLS.
type gatewayWildcardTLSTarget struct {
	service *model.Service
	// port is the upstream port of the destination.
	port int
	// dfpCluster is the dynamic forward proxy cluster of the destination.
	dfpCluster string
	// subset is the route destination subset.
	subset string
	// sniHosts are the SNIs that the server hosts allow, under the wildcard host.
	sniHosts []string
}

// name is the name of the filter chain of the target on the internal listener.
func (t gatewayWildcardTLSTarget) name() string {
	return model.BuildSubsetKey(model.TrafficDirectionOutboundWildcardTLS, t.subset, t.service.Hostname, t.port)
}

// key identifies the target to the internal listener, as "<host>:<port>", or "<host>:<port>/<subset>" for a subset.
// When the server hosts allow only some SNIs under the wildcard host, they are added as "|<sni>,<sni>".
func (t gatewayWildcardTLSTarget) key() string {
	key := string(t.service.Hostname) + ":" + strconv.Itoa(t.port)
	if t.subset != "" {
		key += "/" + t.subset
	}
	if len(t.sniHosts) != 1 || t.sniHosts[0] != string(t.service.Hostname) {
		key += "|" + strings.Join(t.sniHosts, ",")
	}
	return key
}

// gatewayWildcardDestination returns the wildcard DYNAMIC_DNS service and upstream port when wildcard TLS is
// enabled and the routes send to a single such service, as the chain has one SNI dynamic forward proxy filter.
func gatewayWildcardDestination(
	node *model.Proxy, routes []*networking.RouteDestination, serverPort int,
) (*model.Service, int) {
	if !features.EnableWildcardHostServiceEntriesForTLS || len(routes) != 1 {
		return nil, 0
	}
	svc := node.SidecarScope.GetService(host.Name(routes[0].Destination.Host))
	if svc == nil || !svc.Hostname.IsWildCarded() || svc.Resolution != model.DynamicDNS {
		return nil, 0
	}
	// Must match the port of the destination cluster.
	_, _, _, port := model.ParseSubsetKey(istio_route.GetDestinationCluster(routes[0].Destination, svc, serverPort))
	return svc, port
}

// gatewayWildcardServerSNIHosts returns the SNIs under the wildcard host that the server hosts allow for a
// VirtualService in the given namespace: a server host under the wildcard host, or the wildcard host itself when a
// server host covers it.
func gatewayWildcardServerSNIHosts(server *networking.Server, namespace string, wildcardHost host.Name) []string {
	allowed := sets.New[string]()
	for _, h := range server.Hosts {
		if ns, name, ok := strings.Cut(h, "/"); ok {
			// Gateway merging leaves only "<namespace>/<host>".
			if ns != namespace {
				continue
			}
			h = name
		}
		switch {
		case wildcardHost.SubsetOf(host.Name(h)):
			return []string{string(wildcardHost)}
		case host.Name(h).SubsetOf(wildcardHost):
			allowed.Insert(h)
		}
	}
	return sets.SortedList(allowed)
}

// sniHostsUnder returns true if there are SNI hosts and all of them are under one of the allowed hosts.
func sniHostsUnder(sniHosts []string, allowed []string) bool {
	return len(sniHosts) > 0 && !slices.ContainsFunc(sniHosts, func(h string) bool {
		return !slices.ContainsFunc(allowed, func(a string) bool { return host.Name(h).SubsetOf(host.Name(a)) })
	})
}

// gatewayWildcardTLSTargetForServer returns the target of an ISTIO_MUTUAL TLS server whose routes, from a
// VirtualService in the given namespace, send to a wildcard DYNAMIC_DNS service.
func gatewayWildcardTLSTargetForServer(
	node *model.Proxy, server *networking.Server, routes []*networking.RouteDestination, namespace string,
) (gatewayWildcardTLSTarget, bool) {
	if server.GetTls().GetMode() != networking.ServerTLSSettings_ISTIO_MUTUAL || protocol.Parse(server.GetPort().GetProtocol()) != protocol.TLS {
		return gatewayWildcardTLSTarget{}, false
	}
	svc, port := gatewayWildcardDestination(node, routes, int(server.GetPort().GetNumber()))
	if svc == nil {
		return gatewayWildcardTLSTarget{}, false
	}
	sniHosts := gatewayWildcardServerSNIHosts(server, namespace, svc.Hostname)
	if len(sniHosts) == 0 {
		log.Warnf("server hosts %v allow no SNI under the destination host %s, so the gateway does not forward to it",
			server.Hosts, svc.Hostname)
		return gatewayWildcardTLSTarget{}, false
	}
	return gatewayWildcardTLSTarget{
		service:    svc,
		port:       port,
		dfpCluster: istio_route.GetDestinationCluster(routes[0].Destination, svc, int(server.GetPort().GetNumber())),
		subset:     routes[0].Destination.GetSubset(),
		sniHosts:   sniHosts,
	}, true
}

// gatewayWildcardTLSSNIPredicate matches the SNIs of the target: exact for a host, and by suffix under a wildcard.
func gatewayWildcardTLSSNIPredicate(sniHosts []string) *matcher.Matcher_MatcherList_Predicate {
	predicates := slices.Map(sniHosts, func(h string) *matcher.Matcher_MatcherList_Predicate {
		value := &matcher.StringMatcher{MatchPattern: &matcher.StringMatcher_Exact{Exact: h}}
		if host.Name(h).IsWildCarded() {
			value = &matcher.StringMatcher{MatchPattern: &matcher.StringMatcher_Suffix{Suffix: strings.TrimPrefix(h, "*")}}
		}
		return &matcher.Matcher_MatcherList_Predicate{
			MatchType: &matcher.Matcher_MatcherList_Predicate_SinglePredicate_{
				SinglePredicate: &matcher.Matcher_MatcherList_Predicate_SinglePredicate{
					Input:   match.SNI,
					Matcher: &matcher.Matcher_MatcherList_Predicate_SinglePredicate_ValueMatch{ValueMatch: value},
				},
			},
		}
	})
	if len(predicates) == 1 {
		return predicates[0]
	}
	return &matcher.Matcher_MatcherList_Predicate{
		MatchType: &matcher.Matcher_MatcherList_Predicate_OrMatcher{
			OrMatcher: &matcher.Matcher_MatcherList_Predicate_PredicateList{Predicate: predicates},
		},
	}
}

// buildGatewayWildcardTLSFilters builds the network filters of the ISTIO_MUTUAL gateway chain, and records the target
// for the internal listener. The chain hands the peer identity, the original addresses and the target to the internal
// listener and has no authorization filters: on this chain, the SNI is the mesh mTLS SNI, so AuthorizationPolicy is
// applied on the internal listener instead.
func (lb *ListenerBuilder) buildGatewayWildcardTLSFilters(target gatewayWildcardTLSTarget, port *model.Port) []*listener.Filter {
	key := target.key()
	if lb.gatewayWildcardTLSTargetKeys == nil {
		lb.gatewayWildcardTLSTargetKeys = sets.New[string]()
	}
	if !lb.gatewayWildcardTLSTargetKeys.InsertContains(key) {
		lb.gatewayWildcardTLSTargets = append(lb.gatewayWildcardTLSTargets, target)
	}
	tcpProxy := &tcp.TcpProxy{
		// The internal chain counts the connection under the destination cluster, so this chain uses its own prefix.
		StatPrefix:       gatewayWildcardTLSInternalName,
		ClusterSpecifier: &tcp.TcpProxy_Cluster{Cluster: gatewayWildcardTLSInternalName},
		// The internal listener applies the idle timeout, as on waypoints. A timeout here could close the connection
		// before the one configured for the destination.
		IdleTimeout: istio_route.Notimeout,
		// The peer identity and the target are only set once the downstream TLS handshake completes. No application
		// data is read before then, so no early data needs to be buffered.
		UpstreamConnectMode: tcp.UpstreamConnectMode_ON_DOWNSTREAM_TLS_HANDSHAKE,
		MaxEarlyDataBytes:   wrappers.UInt32(0),
	}
	class := model.OutboundListenerClass(lb.node.Type)
	// The internal chain logs the connection, so this chain only logs failures to connect to it, as the waypoint
	// connect forwarder does.
	accessLogBuilder.setHboneOriginationAccessLog(lb.push, lb.node, tcpProxy, class)
	tcpFilter := &listener.Filter{
		Name:       wellknown.TCPProxy,
		ConfigType: &listener.Filter_TypedConfig{TypedConfig: protoconv.MessageToAny(tcpProxy)},
	}
	return lb.buildCompleteNetworkFiltersWithAuthz(class, port.Port, []*listener.Filter{
		xdsfilters.GatewayDownstreamPeerFilter,
		xdsfilters.BuildGatewayWildcardTLSTargetFilter(key),
		tcpFilter,
	}, true, nil, nil, nil)
}

// buildGatewayWildcardTLSInternalListener builds the internal listener of all targets, as the waypoint main_internal
// listener. It restores the original addresses, reads the SNI of the application TLS, and selects the chain of the
// target set by the gateway chain. Each target accepts only the SNIs its server hosts allow, applies AuthorizationPolicy
// with the peer identity from filter state, and resolves the SNI with the dynamic forward proxy. A connection without
// a known target or with another SNI matches no chain and is closed.
func (lb *ListenerBuilder) buildGatewayWildcardTLSInternalListener() *listener.Listener {
	chains := make([]*listener.FilterChain, 0, len(lb.gatewayWildcardTLSTargets))
	targets := make(map[string]*matcher.Matcher_OnMatch, len(lb.gatewayWildcardTLSTargets))
	// The authorization filters do not depend on the target, so they are built once for all chains.
	authzFilters := authz.NewBuilder(authz.Custom, lb.push, lb.node, true).BuildTCP()
	authzFilters = append(authzFilters, authz.NewBuilder(authz.Local, lb.push, lb.node, true).BuildTCP()...)
	chainNames := sets.New[string]()
	for _, target := range lb.gatewayWildcardTLSTargets {
		// Servers with different hosts send to the same chain, as its filters only depend on the destination.
		if !chainNames.InsertContains(target.name()) {
			chains = append(chains, &listener.FilterChain{
				Name:    target.name(),
				Filters: lb.buildGatewayWildcardTLSInternalFilters(target, authzFilters),
			})
		}
		// Only SNIs under the wildcard host that the server hosts allow are forwarded.
		targets[target.key()] = match.ToMatcher(&matcher.Matcher{
			MatcherType: &matcher.Matcher_MatcherList_{MatcherList: &matcher.Matcher_MatcherList{
				Matchers: []*matcher.Matcher_MatcherList_FieldMatcher{{
					Predicate: gatewayWildcardTLSSNIPredicate(target.sniHosts),
					OnMatch:   match.ToChain(target.name()),
				}},
			}},
		})
	}
	return &listener.Listener{
		Name:              gatewayWildcardTLSInternalName,
		ListenerSpecifier: &listener.Listener_InternalListener{InternalListener: &listener.Listener_InternalListenerConfig{}},
		ListenerFilters:   []*listener.ListenerFilter{xdsfilters.OriginalDestination, xdsfilters.TLSInspector},
		TrafficDirection:  core.TrafficDirection_OUTBOUND,
		FilterChains:      chains,
		FilterChainMatcher: &matcher.Matcher{
			MatcherType: &matcher.Matcher_MatcherTree_{MatcherTree: &matcher.Matcher_MatcherTree{
				Input:    match.GatewayWildcardTLSTargetFilterStateInput,
				TreeType: &matcher.Matcher_MatcherTree_ExactMatchMap{ExactMatchMap: &matcher.Matcher_MatcherTree_MatchMap{Map: targets}},
			}},
		},
	}
}

// buildGatewayWildcardTLSInternalFilters builds the network filters of the internal chain of a target, after the
// authorization filters shared by all chains.
func (lb *ListenerBuilder) buildGatewayWildcardTLSInternalFilters(
	target gatewayWildcardTLSTarget, authzFilters []*listener.Filter,
) []*listener.Filter {
	destinationRule := CastDestinationRule(lb.node.SidecarScope.DestinationRule(
		model.TrafficDirectionOutbound, lb.node, target.service.Hostname).GetRule())
	tcpPool := destinationRule.GetTrafficPolicy().GetConnectionPool().GetTcp()
	tcpProxy := &tcp.TcpProxy{
		StatPrefix:                      target.dfpCluster,
		ClusterSpecifier:                &tcp.TcpProxy_Cluster{Cluster: target.dfpCluster},
		IdleTimeout:                     tcpPool.GetIdleTimeout(),
		MaxDownstreamConnectionDuration: tcpPool.GetMaxConnectionDuration(),
	}
	if tcpProxy.IdleTimeout == nil {
		tcpProxy.IdleTimeout = parseDuration(lb.node.Metadata.IdleTimeout)
	}
	maybeSetHashPolicy(destinationRule, tcpProxy, target.subset)
	tunnelingconfig.Apply(tcpProxy, destinationRule, target.subset)
	tcpFilter := setAccessLogAndBuildTCPFilter(lb.push, lb.node, tcpProxy, istionetworking.ListenerClassGateway, nil)

	return append(lb.copyFilters(authzFilters),
		buildSNIDFPFilter(target.port, target.service, util.SelectDNSLookupFamily(lb.node.IPAddresses)),
		tcpFilter)
}

// buildGatewayWildcardTLSInternalCluster builds the cluster that sends the ISTIO_MUTUAL gateway chains to the internal
// listener. As the waypoint main_internal cluster, it does not depend on the targets, so it never changes with them.
func buildGatewayWildcardTLSInternalCluster() *cluster.Cluster {
	return buildInternalUpstreamCluster(gatewayWildcardTLSInternalName, gatewayWildcardTLSInternalName, false)
}

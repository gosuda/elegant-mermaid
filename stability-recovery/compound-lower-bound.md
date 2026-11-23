# Compound-layout lower-bound audit

This is a read-only diagnostic, not a quality gate or an optimizer. It counts fixtures for which the current literal ordinary-group layout rules alone force a soft cost above the existing per-fixture baseline allowance. Unsupported fixtures contribute zero to the count.

## Run

After the recovery collector has completed, run:

~~~sh
node stability-recovery/compound-lower-bound.mjs --self-test
node stability-recovery/compound-lower-bound.mjs --repo . --metrics recovery-results/baseline-metrics.json --dumps recovery-results/baseline > recovery-results/baseline-lower-bounds.json
node stability-recovery/compound-lower-bound.mjs --repo . --metrics recovery-results/trial-metrics.json --dumps recovery-results/trial > recovery-results/trial-lower-bounds.json
~~~

The analyzer writes only standard output. It neither executes a layout engine nor changes a source, cache, metric, threshold, or fixture list.

Required inputs:

- The exact fixture list at corpus/quality-corpus.txt.
- The fixture sources relative to the repository root.
- The current spec/data/layout-constants.json.
- The metric array selected by --metrics, with each row shaped as:
  {path, ours: {nodes, mean_node_extent, soft_cost, ...}, dagre: {...}, elk: {...}}.
- Native vector dumps at <dumps>/<corpusPath>.ours.json.
- Both baseline dumps at corpus/.cache/quality/<corpusPath>.dagre.json and .elk.json.

The optional --baseline-cache and --corpus arguments change those input locations. The metric array must cover the fixture list exactly once. For every analyzed fixture, both baseline dumps must retain the native ordered box identities, hierarchy, exclusive flags, real-node dimensions, route identities/endpoints, and complete label identities/text/dimensions. Group output sizes and all positions may differ. Metric N and M must agree with those fixed node dimensions.

JSON numbers used in arithmetic must be exact safe integers. Computed quantities use BigInt and appear as decimal strings in the report. The algorithm runs in O(V + E) per supported fixture, plus input reading and emitted evidence; it performs no layout search.

## Supported subset and why it is safe

A fixture must be a vector flowchart with at least one real node and at least one nonempty ordinary group. Groups must all be top-level. Every real node must be exclusive and either a direct group child or a root node. Routes must connect real nodes. The directed real-node graph must be acyclic. Any occurrence of the word direction in the source, even in a comment or text label, excludes the fixture conservatively.

Under these conditions, each synthetic group-top anchor is a source and each group-bottom anchor is a sink. Adding the protected hierarchy constraints cannot create a cycle in the acyclic real-node graph. Thus no semantic route can be reversed by the compound cycle rule. An absent subgraph direction denotes an ordinary cluster (layered-58).

The report distinguishes one group containing a simple directed chain from the larger flat-group DAG subset. It deliberately does not infer bounds for nested groups, independently directed groups, empty groups with unknown intrinsic titles, cycles, group endpoints, or other diagram families.

## Lower-bound derivation

All extents are in units of 1/64 px. Let G be rank_gap, p be cluster_pad, b be cluster_border_w, and l be line_h. Let h(v) and w(v) be the fixed real-node extents on the internal rank and cross axes. LR/RL swap the output dimensions (layered-08).

For each group, use its induced real-node DAG and compute:

    D(v) = h(v) + max(0, max over internal edges u -> v of (D(u) + G)).

D is a weighted longest-path lower bound. Path nodes occupy strictly increasing ranks (layered-15). Every rank in a group span has borders (layered-34), so none is an all-dummy label rank: each intervening gap is at least G (layered-50/51). Ignoring other nodes, extra ranks, channel slots, and labels only decreases this bound.

A nonempty group has a top anchor strictly before every member and a bottom anchor strictly after every member (layered-16). Its frame starts at the top anchor's rank top and ends at the bottom anchor's rank bottom (layered-52). Its top rank reserves the title (layered-10). Therefore:

    H(group) >= q + 2G + max over group nodes v of D(v).

For TB/BT, q = l + p, because at least one title line is reserved even for an empty title. For LR/RL, q = 0 is a conservative bound on the swapped measured title width; the analyzer does not guess private title measurements.

The weaker cross-axis bound is W >= max w(v), using parent containment. The literal border-separation bound is:

    W >= max over group nodes v of
         max(w(v), 2 floor(w(v)/2) + 2 floor(b/2) + b + 2p).

This follows by telescoping the adjacent separations from the left border through a member to the right border (layered-34/37), then adding the outer border edges. Straight border chains identify those outer edges with the frame edges at every rank (layered-107/108). The formula deliberately retains the possible one-unit loss for odd node widths. Other intervening members only add nonnegative widths/gaps.

Top-level groups have disjoint interiors and are disjoint from root nodes by HardConstraints C8a. Exclusive root nodes have disjoint interiors by C2. Hence the global bounding area K is at least the sum of the group area lower bounds plus the actual areas of root nodes. Group members are not added a second time.

Every semantic edge between nodes in one group has endpoints separated by at least one full rank gap, so T >= G times the number of such edges. Other routes contribute a conservative zero. Orthogonal routing makes this exact projection argument immediate; floor square-root segment length is also at least the integer rank-axis projection.

For N fixed real nodes, compute M by quality-metrics-08. Since crossings, bends, and against-flow counts are nonnegative:

    soft_cost >= floor(T_min / M) + floor(K_min / (M * M * N)).

The report computes this twice, using the containment-only width and the literal border width. A fixture is counted only when:

    100 * lower_bound > 120 * min(dagre.soft_cost, elk.soft_cost).

The allowed number of exceptions remains floor(fixture_count / 20). The report says that its supported subset exceeds that budget only if the proven count actually does so. A smaller count does not establish feasibility of the remaining fixtures.

## Verified example

For graph TB, one ordinary group containing A -> B, with fixed sizes A = 2188 by 2304 and B = 2127 by 2304:

- N = 2 and M = 2230.
- H >= 16128.
- Containment width >= 2188; literal border width >= 5260.
- T >= 3072.
- The containment-width cost bound is 4.
- The literal border-width cost bound is 9.
- The observed baseline scores were Dagre 5 and ELK 2, so even the weaker bound exceeds the allowance.

Both corresponding corpus copies were verified before the outage. The full-corpus count remains unknown until this analyzer runs on the collected inputs.

## Interpretation and limits

The bound includes the current mandatory title/rank bands. A new post-layout refinement that deliberately changes those bands requires an explicit new shared algorithm contract. Merely passing the geometric validator does not imply compliance with every literal layered pipeline rule. The report separately lists observed layouts below its literal size or cost bounds so such a mismatch is investigated instead of hidden.

The current baseline contract explicitly uses zero padding and supplies no intrinsic group title reservation. Its engines recompute compound frames. Passing the already-expanded native group size is not equivalent to providing those intrinsic requirements. Also, common translation cannot change the metric, but internal group padding changes K and can change T.

The principled input correction is to supply the same intrinsic title dimensions and per-side required clearances to all engines, independently of any engine's resulting positions or wasted frame size. Pinning baseline groups to the native output frame would import native layout waste into the comparator. Deleting the native title/padding requirement would change the rendering contract. Neither is justified by a score target.

This script establishes only the listed lower-bound claims. It does not prove that a layout optimizer is optimal, certify rendered primitive correspondence, or alter the native hard constraints.

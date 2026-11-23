# Cell routing investigation checkpoint

This recovery-only material is based on 4f18d67. It changes no runtime behavior.
Do not treat it as a completed fix or publish the Go probe in the production tree.

## Observed before executor failure

Immutable config-emd-go and config-ci-binaries/bin/emd-rs agree on the original
weave metric: hard_ok false, crossings 172, bends 88, route length 2916595,
canvas area 7854622080, soft cost 3170.

Actual Rust text output contains only five complete feedback labels although the
scene has six. The first label is x32..39,y150; later reverse endruns e17..e21
pass through x32..36,y150. Their canonical axis-conflict count is zero: the defect
is label refusal, not same-axis route overlap.

170 native render probes reduced this to cell-label-minimal.mmd. Its first label
e4.label occupies x12..19,y24; e5 has a vertical run on x12 through y24. Actual
native text contains one complete feedback label instead of two.

All nine other failing flow fixtures have short unrelated same-axis overlaps:
- lanes_crossfeed e14/e12: (84,28),(85,28)
- path_occlusion_maze e5/e3: x110..112,y51
- path_occlusion_maze e22/e14: x51..54,y9
- port_alignment_matrix e30/e5: (98,10),(99,10)
- dense e13/e8: (19,12),(20,12)
- flowchart~0085 e2/e1: (4,5),(4,6)
- shape-themes01/11/21/31 e8/e2: (42,23),(42,24)

The smallest route fixture is:
flowchart TB
A --> C
A --> D
B --> C
B --> D

Its routes:
e0 A-C: (2,4),(2,9)
e1 A-D: (4,4),(4,6),(8,6),(8,9)
e2 B-C: (8,4),(8,5),(4,5),(4,9)
e3 B-D: (10,4),(10,9)

Swapping middle channel order moves the same problem from x4 to x8. Keeping
the exact ports and endpoint directions therefore requires another detour.
An illustrative e2 candidate is
(8,4),(8,5),(3,5),(3,8),(4,8),(4,9).
It has no canonical unrelated-axis conflicts by direct cell enumeration.
It has not yet been verified by the actual renderer.

The parent normalized-chain reverse-route prototype makes actual weave hard_ok
true, with crossings64/softcost1366; this likely removes the feedback-label
mechanism through its already-existing proper label channel. It does not solve
K2,2. It remains a separate unpaired Go prototype, not a Rust behavior change.

## Proposed segment-local repair, awaiting runtime experiment

Precondition: an orthogonal cell scene with fixed canonical route endpoints.
Do not change the conflict definition or exempt unrelated pairs.

1. Identify every same-axis conflicting pair and each affected maximal straight
   segment. Search both routes. The later route can have an unavoidable fixed
   first unit-stub collision; maze e22/e14 is an example, so earlier e14 must move.
2. Translate a conflicting segment to a nearby parallel clear lane. Extend its
   adjacent perpendicular runs to meet it. At an authored endpoint keep the exact
   port and a one-cell stub in the original direction, inserting two bends.
3. Preserve source/target identifiers, route order, markers, forced faces,
   semantic scopes and group/region containment. Keep all labels and boxes fixed.
   Do not silently discard semantic label-channel constraints when coalescing
   geometric collinear points.
4. Reject new intersections with occupied label cells, exclusive box ink,
   protected text/markers, invalid endpoint stubs or unrelated same-axis runs.
   Orthogonal crossings remain allowed; shared-endpoint trunks remain allowed
   under the existing predicate.
5. Full acceptance requires C1-C8 plus the actual projected cells.Render result.
   Accept a step only if the global conflict-cell count strictly decreases and
   refused clusters do not increase. This gives a finite descent measure.
6. Choose candidates deterministically using fixed route/segment order and
   integer lane coordinates. Candidate lanes can come from existing obstacle/
   route boundaries plus or minus one, rather than scanning huge integer canvases.
   A local search can report no admissible move; that is unresolved, never a reason
   to label the incumbent hard-valid or relax the fixture.

The nearest-segment prototype was being drafted but was NOT written or run:
executor disconnected before apply_patch could read the scratch Python file.

## Actual renderer probe

main.go.txt is the exact initial temporary Go probe (before any successful build).
Copy to tools/cell-repair-probe/main.go only for an isolated experiment.

It uses the real parser, model and family scene, then applies route patches with
an exact before-points guard. It edits both canonical routes and matching display
polylines, performs final cell attachment projection once, and invokes cells.Render.
The report separates C1-C8, refused_clusters and route_conflicts, with actual text.
For refused labels it renders growing prefixes of the real Text items while
retaining all non-text primitives, attributing the refused count to each owner.

A patch JSON maps route IDs to {"before":[[x,y],...],"after":[[x,y],...]}.
The caller must preserve endpoint directions; the probe itself checks endpoints.
A missing or mismatching canonical polyline is an error, not a skipped patch.

To isolate the original baseline while parent prototypes stay in the worktree,
use go build -overlay. Restore component.go, pipeline.go, portfolio.go from the
published HEAD into scratch files, and map newly added compact.go,
port_alignment.go, port_alignment_test.go, port_compaction.go to empty strings
in the overlay Replace map. No source or manifest needs modification.

Last attempted command (no completion was observed):
go build -overlay /workspace/scratch/176b36824d83/cell-probe-overlay.json \
  -o /workspace/scratch/176b36824d83/cell-repair-probe-baseline \
  ./tools/cell-repair-probe

Next: run the expanded real-cell audit for the parent comparison's 46 paths.
The 45 previously failing paths among those include agentflow/state/swimlane;
do not presume all are route overlap. Separate vector-only invalidity from
cell C1-C8, mask refusal and axis conflicts before selecting a repair.

## Rust regressions

cell_routing.rs.proposed contains two real-renderer regressions, ready to copy into
crates/elegant-mermaid/tests/cell_routing.rs. They were not compiled. Public API
names were checked against the published source. Their native repro sources were
observed red, so no additional failure discovery is needed before implementation.

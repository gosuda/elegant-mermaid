# Lean reference implementation

This file fixes the scope, project layout, gates, proof hygiene, fuel scheme, work packet, and kernel theorems of the Lean 4 reference that `proofs/` holds.

## Purpose and claim

- lean-reference-01: The Lean project `proofs/` MUST be a third implementation of the measurement, layout, scene, and cell-render stages. [just proofs]
- lean-reference-02: Each algorithm of those stages MUST be a total Lean function with theorems. [just proofs]
- lean-reference-03: The reference MUST NOT cover source reading, syntax, model resolution, `diag`, `lint`, `svg`, `raster`, `markdown`, `termgfx`, `tui`, or `cli`, so SVG serialisation, PNG rasterisation, and terminal graphics stay outside the proofs. [just proofs]
- lean-reference-04: For every phase the proofs MUST show that it terminates, that it keeps its stated invariants, and that it never returns a result worse than its input by the phase's own measure. [just proofs]
- lean-reference-05: No theorem MUST claim optimality, because crossing minimisation is NP-hard, and the quality comparison with dagre and ELK MUST stay a measured gate. [just quality]
- lean-reference-06: Go output MUST match the reference byte for byte under `kernel-diff` for the kernel and `lean-parity` for layouts and text, and Rust output MUST match Go under `parity`. [just lean-parity]
- lean-reference-07: The shipped Go and Rust code MUST carry no proof of its own, and the claim MUST cover the Lean reference only. [just lean-parity]

## Toolchain and arithmetic

- lean-reference-08: `proofs/lean-toolchain` MUST pin `leanprover/lean4:v4.35.0`, and the project MUST import only the toolchain libraries `Init`, `Std`, and `Lean`, so no Mathlib and no Batteries. [just proofs]
- lean-reference-09: `Lean.Json` MUST be used for reading the model-stage dump and for writing the layout dump, and that parsing and writing MUST count as I/O shell code outside the theorems, checked by `lean-parity` rather than by a proof. [just lean-parity]
- lean-reference-10: Arithmetic MUST be on `Int`, and `floor_div` and `floor_mod` MUST be `Int.fdiv` and `Int.fmod`, so the code uses no `/` or `%` on `Int`. [just proofs]
- lean-reference-11: Every operation that Go and Rust check for overflow MUST return `Except LayoutError` with the same int32 result range and the same int64 intermediate range, so an overflow is `LayoutError.overflow` in Lean, `geom.ErrOverflow` in Go, and `GeomError::Overflow` in Rust. [just kernel-diff]
- lean-reference-12: The domain error MUST be `LayoutError.domain` in Lean, `geom.ErrDomain` in Go, and `GeomError::Domain` in Rust, and `LayoutError` MUST be defined in `ElegantGeometry/Basic.lean` with the constructors `overflow` and `domain`. [just kernel-diff]

## Project layout

- lean-reference-13: The project MUST hold these files, and a module MUST be created by the step that proves it, never as an empty module. [just proofs]

    ```
    proofs/lean-toolchain            leanprover/lean4:v4.35.0
    proofs/lakefile.toml             package `elegant`; libraries `ElegantGeometry`, `Elegant`; executable `geomcheck` (root `Main`)
    proofs/ElegantGeometry/Basic.lean       Point, Size, Rect, Interval, Axis, LayoutError, translate, inflate, union, intersects, contains, placeAfter, bbox, isqrt
    proofs/ElegantGeometry/Disjoint.lean    Disjoint, placeAfter_disjoint, Rect.disjoint_comm, Rect.disjoint_translate
    proofs/ElegantGeometry/Compaction.lean  compact and its three theorems
    proofs/ElegantGeometry/Crossings.lean   Segment, segments_cross, count_inversions, inversions_eq_crossings
    proofs/ElegantGeometry/Route.lean       Polyline, is_orthogonal, polyline_hits_rect
    proofs/ElegantGeometry/Trig.lean        sin_q15, cos_q15 over the generated table `proofs/Elegant/Gen/Sine.lean`, imported as `Elegant.Gen.Sine`
    proofs/ElegantGeometry/Validator.lean   LayoutDump, WellFormed of a layout dump, the seven clauses, validate, check, Validator.sound
    proofs/ElegantGeometry/DumpReader.lean  parses the canonical layout dump (`Lean.Json`) into `LayoutDump`; used by `geomcheck validate`
    proofs/Elegant/Gen/*.lean        generated tables: advances, Unicode widths, grapheme classes, glyph join, layout constants, sine (Sine.lean), themes needed by cells
    proofs/Elegant/Model.lean        model-stage dump types, `WellFormed` and `WithinLimits` of a model
    proofs/Elegant/Measure.lean      advances, cell widths, grapheme segmentation, wrapping
    proofs/Elegant/Layered/{Cycles,Rank,Normalize,Order,Coords,Route,Labels,Loops,Pack,Portfolio,Pipeline}.lean
    proofs/Elegant/{Sequence,Grid,Tree,Lanes,Railroad}.lean
    proofs/Elegant/Chart/{Scale,Gantt,XY,Quadrant,Treemap,Wardley,Pie,Radar,Sankey,Venn,Cynefin,Info}.lean
    proofs/Elegant/Kinds/<Kind>.lean one adapter per kind: model to family input
    proofs/Elegant/Text/{Canvas,Join,Place,Braille,Render}.lean
    proofs/Elegant/Dump.lean         reads the model-stage dump (`Lean.Json`), writes the layout dump (`toDump`)
    proofs/Elegant/Scene.lean         scene primitives, roles, and the shared `softCost` function
    proofs/Main.lean                 `geomcheck validate | eval | layout | text`
    proofs/theorems.txt              one fully qualified theorem name per line; the list that `audit.sh` checks
    proofs/scripts/audit.sh
    ```

- lean-reference-14: The kernel library `ElegantGeometry` MUST import the generated module `Elegant.Gen.Sine`, and that module MUST import nothing from `ElegantGeometry`, so no import cycle exists. [just proofs]
- lean-reference-15: `proofs/theorems.txt` MUST hold one fully qualified theorem name per line, and every theorem name of every theorem table in `spec/` MUST be listed there. [just proofs]

## Subcommands

- lean-reference-16: The executable `geomcheck` MUST have exactly four subcommands: `validate`, `eval`, `layout`, and `text`. [just proofs]
- lean-reference-17: `geomcheck validate` MUST read a canonical layout dump from stdin and behave as `spec/layout-dump.md` states: print `valid` and exit 0, print `invalid <clause-id>: <message>` and exit 1, or print `malformed dump: REASON` and exit 2. [just validate]
- lean-reference-18: `geomcheck eval FILE` MUST read the kernel case file and write one result line per case, with the grammar, result tokens, and `bad case line N` error of `spec/geometry-kernel.md`, and its output MUST equal that of `emd kernel-eval FILE` on the same file. [just kernel-diff]
- lean-reference-19: `geomcheck layout` MUST read the model-stage dump of `spec/model-dump.md` from stdin and print the canonical layout dump, and `geomcheck text --charset unicode|ascii` MUST read the same dump and print the cell rendering under the cell profile with colour off. [just lean-parity]
- lean-reference-20: Where a layout rule emits `layout/budget-exhausted` (info) at a cap, the Lean function MUST return the same diagnostic in its result, and `geomcheck layout` MUST write it to stderr as Go and Rust do. [just go-check]
- lean-reference-21: `lean-parity` MUST compare stdout and the exit status only, so it MUST NOT compare that diagnostic. [just lean-parity]

## The `lean-parity` gate

- lean-reference-22: For every accepted corpus file, and for `P` in `vector` and `cell`, `bin/emd-go layout --stage model --profile P FILE | geomcheck layout` MUST equal `bin/emd-go layout --profile P FILE`; the recipe takes the parameters `KIND`, `SAMPLE`, `JOBS`, and `FILES` that `spec/cli.md` defines. [just lean-parity]
- lean-reference-23: For every accepted corpus file, and for `C` in `unicode` and `ascii`, `bin/emd-go layout --stage model --profile cell FILE | geomcheck text --charset C` MUST equal `bin/emd-go render -e text --charset C --color never FILE`. [just lean-parity]
- lean-reference-24: The gate MUST run those two comparisons on 2000 seeded random diagrams per layout family from `tools/randgraph`, written to `corpus/.cache/random/`. [just lean-parity]
- lean-reference-25: The random part MUST first run in the step that builds the family's first kind: `layered` when the flowchart adapter lands, `sequence`, `grid`, `tree`, and `lanes` in their own steps, and the chart kinds and `railroad` in theirs. [just lean-parity]
- lean-reference-26: The gate MUST take its file list through `FILES`, the family path list that `tools/randgraph` writes to `corpus/.cache/random/<F>.txt`. [just lean-parity]
- lean-reference-27: `parity` MUST already tie `emd-rs` to `emd-go`, so the Lean comparison MUST use one binary. [just parity]
- lean-reference-28: A negative control MUST be run once and not committed: change one tie-break in the Lean ordering phase and observe `lean-parity` fail. [just lean-parity]

## Random diagrams (`tools/randgraph`)

- lean-reference-29: Each file in `corpus/.cache/random/` MUST be Mermaid source of one kind, and Go, Rust, and Lean MUST accept every file. [just lean-parity]
- lean-reference-30: `tools/randgraph` MUST be a Go program of `package main` with no flags, and it MUST write cases 0 to 1999 for each family in this order: `layered`, `sequence`, `grid`, `tree`, `lanes`, `chart`, `railroad`. [just lean-parity]
- lean-reference-31: The program MUST overwrite a file of the same name, MUST delete nothing, and MUST also write `corpus/.cache/random/<F>.txt`, the list of that family's paths in case order, which the gate recipes take through `FILES`. [just lean-parity]
- lean-reference-32: The draw rules of each family MUST live in the Go package `tools/randgraph/gen`, which Go tests import. [just go-check]
- lean-reference-33: Rust tests MUST repeat the `layered` rule in `crates/elegant-mermaid/tests/support/randgraph.rs`, and a Rust test MUST compare its first 200 layered cases with the files that the tool wrote, when those files exist. [just rust-check]
- lean-reference-34: Case `i` of family `F` MUST be written to `corpus/.cache/random/<F>/<i>.mmd`, where `<i>` is decimal with four digits and leading zeros. [just lean-parity]
- lean-reference-35: Each family MUST write one kind, and line 1 MUST be the header of this list. [just lean-parity]

    - `layered`: `flowchart TD`, kind `flowchart`.
    - `sequence`: `sequenceDiagram`.
    - `grid`: `block-beta`.
    - `tree`: `mindmap`.
    - `lanes`: `gitGraph`.
    - `chart`: `xychart-beta`.
    - `railroad`: `railroad-beta`.

- lean-reference-36: For family `F` and case `i`, the stream state MUST start as `s = i + 1` in 32 bits, and a draw MUST run `s ^= s << 13`, then `s ^= s >> 17`, then `s ^= s << 5`, each step in 32 bits, where `>>` is a logical shift; the draw MUST return the new `s`, the stream MUST depend on `i` only, and the state MUST never become 0. [just go-check]
- lean-reference-37: `draw(lo, hi)` MUST return `lo + floor_mod(s, hi - lo + 1)` on the unsigned value of the stream, with `lo <= hi`, and each draw of a family rule MUST be one call made in the order written. [just go-check]
- lean-reference-38: The fixed list `WORDS` MUST hold these 16 words at indices 0 to 15: `amber`, `birch`, `cedar`, `delta`, `ember`, `fjord`, `garnet`, `harbor`, `iris`, `juniper`, `kelp`, `lumen`, `maple`, `nectar`, `onyx`, `pine`. [just go-check]
- lean-reference-39: `label(k)` MUST call `draw(0, 15)` to get `w` and MUST return `WORDS[w]` followed by the decimal `k`, with no space, where `k` is the 0-based index of the element in its file, so a label holds only ASCII letters and digits. [just go-check]
- lean-reference-40: Each file MUST use LF line endings, ASCII only, and one final LF, with no blank line, no tab, and no trailing space, each statement on one line, and at most 30 nodes or items. [just lean-parity]
- lean-reference-41: A file of the `layered` family MUST draw `n = draw(2, 30)`, then `L_i = label(i)` for `i` from 0 to `n - 1`, then `e = draw(1, n)`, then for `j` from 0 to `e - 1`, `a_j = draw(0, n - 2)` and `b_j = draw(a_j + 1, n - 1)`. Its lines MUST be `flowchart TD`, then `n{i}[{L_i}]` for each `i`, then `n{a_j} --> n{b_j}` for each `j`. Every edge MUST run from a lower index to a higher one, so the graph MUST hold no cycle, self-loop, subgraph, or edge label, and a repeated edge MUST be kept. [just lean-parity]
- lean-reference-42: The example below MUST show the shape of the `layered` family, not the output of case 0. [just go-check]

    ```
    flowchart TD
    n0[amber0]
    n1[birch1]
    n2[cedar2]
    n0 --> n2
    n1 --> n2
    ```

- lean-reference-43: A file of the `sequence` family MUST draw `a = draw(2, 8)`, then `m = draw(1, 20)`, then for `k` from 0 to `m - 1`: `f = draw(0, a - 1)`, `d = draw(1, a - 1)`, `t = floor_mod(f + d, a)`, `x = draw(0, 3)`, and `T_k = label(k)`, where the arrow is `->>` for `x` 0, `-->>` for 1, `->` for 2, and `-->` for 3. [just go-check]
- lean-reference-44: The lines of a `sequence` file MUST be `sequenceDiagram`, then `participant n{i}` for `i` from 0 to `a - 1`, then `n{f}{arrow}n{t}: {T_k}` for each `k`. `t` MUST never equal `f`, because `d` is between 1 and `a - 1`. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    sequenceDiagram
    participant n0
    participant n1
    participant n2
    n0->>n1: amber0
    n1-->>n2: birch1
    ```

- lean-reference-45: A file of the `grid` family MUST draw `c = draw(1, 4)`, then `n = draw(2, 30)`, then for `i` from 0 to `n - 1` the pair `L_i = label(i)` and `s_i = draw(1, 2)`, then `e = draw(0, n - 1)`, then for `j` from 0 to `e - 1`, `a_j = draw(0, n - 1)`, `d_j = draw(1, n - 1)`, and `b_j = floor_mod(a_j + d_j, n)`. [just go-check]
- lean-reference-46: The lines of a `grid` file MUST be `block-beta`, then `columns {c}`, then `n{i}["{L_i}"]:{s_i}` for each `i`, then `n{a_j} --> n{b_j}` for each `j`. No edge line MUST follow when `e` is 0. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    block-beta
    columns 2
    n0["amber0"]:1
    n1["birch1"]:2
    n0 --> n1
    ```

- lean-reference-47: A file of the `tree` family MUST draw `n = draw(2, 30)`, then `L_i = label(i)` for `i` from 0 to `n - 1`, then `p_i = draw(0, i - 1)` for `i` from 1 to `n - 1`, where node 0 is the root and `p_i` is the parent of node `i`. [just go-check]
- lean-reference-48: The lines of a `tree` file MUST be `mindmap`, then every node in depth-first preorder, visiting the children of each node in increasing index. A node at depth `d` MUST be written as `2 + 2 * d` spaces followed by `L_i`, where the root has depth 0. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    mindmap
      amber0
        birch1
        cedar2
          delta3
    ```

- lean-reference-49: A file of the `lanes` family MUST draw `t = draw(3, 30)`, then for `q` from 0 to `t - 1` a value `r = draw(0, 9)` followed by the action for `r`. [just go-check]
- lean-reference-50: The state of the `lanes` family MUST be: the branch list starts with `main`, whose head is none, and `current` is `main`. A commit MUST record the branch that was `current` when it was made, and a branch head MUST be its latest commit, or none. [just go-check]
- lean-reference-51: For `r` from 0 to 4, and for every fallback of the rules below, the action MUST be a commit: add a commit to `current`, set its head, and emit `commit`. [just go-check]
- lean-reference-52: For `r` equal to 5, the action MUST be: when the list holds fewer than 4 branches and `head(current)` is set, draw `w = draw(0, 15)`, name the new branch `WORDS[w]` followed by the number of branches in the list, append it with head `head(current)`, make it `current`, and emit `branch {name}`. Otherwise the action MUST be a commit. [just go-check]
- lean-reference-53: For `r` equal to 6, the action MUST be: let `others` be the branches other than `current` in list order. When `others` is not empty, draw `j = draw(0, len(others) - 1)`, make `others[j]` `current`, and emit `checkout {name}`. Otherwise commit. [just go-check]
- lean-reference-54: For `r` from 7 to 9, the action MUST be: let `eligible` be the branches `B` other than `current`, in list order, where `head(B)` is set, `head(current)` is set, `head(B)` differs from `head(current)`, and the branch of `head(current)` is not `B`. When `eligible` is not empty, draw `j = draw(0, len(eligible) - 1)`, emit `merge {name}` for `B = eligible[j]`, and add a commit to `current`. Otherwise commit. [just go-check]
- lean-reference-55: The lines of a `lanes` file MUST be `gitGraph`, then one line per action, in order. Mermaid's `branch` MUST make the new branch current. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    gitGraph
    commit
    branch birch1
    commit
    checkout main
    merge birch1
    ```

- lean-reference-56: A file of the `chart` family MUST draw `n = draw(2, 12)`, then `L_i = label(i)` for `i` from 0 to `n - 1`, then `v_i = draw(0, 100)` for each `i`, then `u_i = draw(0, 100)` for each `i`. [just go-check]
- lean-reference-57: The lines of a `chart` file MUST be `xychart-beta`, `x-axis [L_0, L_1, ..., L_{n-1}]`, `y-axis 0 --> 100`, `bar [v_0, ..., v_{n-1}]`, and `line [u_0, ..., u_{n-1}]`, with items separated by a comma and one space. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    xychart-beta
    x-axis [amber0, birch1, cedar2]
    y-axis 0 --> 100
    bar [12, 40, 7]
    line [30, 3, 88]
    ```

- lean-reference-58: A file of the `railroad` family MUST draw `R = draw(1, 3)`, then for `i` from 0 to `R - 1` a value `k = draw(0, 7)` followed by the body that the rules below fix. [just go-check]
- lean-reference-59: For `k` from 0 to 2 the body MUST be one leaf of kind `k`, for `k` equal to 3 or 4 it MUST be a `sequence` for 3 or a `choice` for 4 with `c = draw(2, 3)` leaf children, and for `k` from 5 to 7 it MUST be `optional` for 5, `oneOrMore` for 6, or `zeroOrMore` for 7 with one leaf child. [just go-check]
- lean-reference-60: A leaf child MUST first draw its kind `q = draw(0, 2)`, then its payload: `terminal('{WORDS[draw(0, 15)]}')` for kind 0, `nonterminal('r{draw(0, R - 1)}')` for kind 1, and `special('{WORDS[draw(0, 15)]}')` for kind 2, where railroad words carry no index. [just go-check]
- lean-reference-61: The lines of a `railroad` file MUST be `railroad-beta`, then `r{i} = {body} ;` for each `i`. Each body MUST hold at most 4 nodes, and a file MUST hold at most 12. The example below MUST show the shape of the family, not the output of case 0. [just lean-parity]

    ```
    railroad-beta
    r0 = sequence(terminal('amber'), nonterminal('r1')) ;
    r1 = optional(special('birch')) ;
    ```

## Proof hygiene

- lean-reference-62: `proofs/scripts/audit.sh` MUST fail when a name in `proofs/theorems.txt` does not exist, or when `#print axioms` for a listed theorem shows an axiom other than `propext`, `Classical.choice`, or `Quot.sound`. [just proofs]
- lean-reference-63: The script MUST fail when a file under `proofs/ElegantGeometry/` or `proofs/Elegant/` contains `sorry`, `partial def`, `unsafe`, `implemented_by`, `extern`, `native_decide`, or a line that starts with `axiom`. [just proofs]
- lean-reference-64: The script MUST generate a scratch file under `proofs/.lake/` that imports `ElegantGeometry` and `Elegant` and prints the axioms of each listed name, and it MUST run that file with `lake env lean`. [just proofs]
- lean-reference-65: `just proofs` MUST run `lake build --wfail` in `proofs/`, so a warning fails the build, and then `scripts/audit.sh`. [just proofs]
- lean-reference-66: If a listed theorem resists proof, the statement MUST be kept, the open goal MUST be reported, and `just proofs` MUST stay red, so the statement is never weakened, no axiom is added, no name leaves `proofs/theorems.txt`, and a red `proofs` gate blocks publication. [just proofs]

## Theorem scheme

- lean-reference-67: Every theorem MUST be stated over the Lean functions that `geomcheck` runs, and names MUST follow `<phase>_<property>`. [just proofs]
- lean-reference-68: Each family MUST end with a validity theorem of this form: for every well-formed model within `Limits`, if the family layout returns a scene, the scene satisfies `HardConstraints`, so `Validator.check` returns true. [just proofs]
- lean-reference-69: The per-family theorem tables, of theorem name, statement, and proof approach, MUST be the `## Theorems` sections of `spec/layout/layered.md`, `spec/layout/sequence.md`, `spec/layout/grid.md`, `spec/layout/tree.md`, and `spec/layout/lanes.md`, and the `## Proofs` sections of `spec/layout/charts.md` and `spec/layout/railroad.md`, and this file MUST NOT restate them. [just proofs]
- lean-reference-70: The shared names `Validator.check`, `WellFormed`, `WithinLimits`, `toDump`, and `softCost` MUST be used across the families. [just proofs]
- lean-reference-71: `Layered.initRank g` MUST be the longest-path ranking of `g`, `Layered.initOrder g` MUST be the declaration-order layer assignment, and `cost r` MUST be the sum over edges `e` of `(r e.head - r e.tail)` with unit weight for every edge. [just proofs]

## Loop fuel

- lean-reference-72: Every iterative phase MUST take a `fuel : Nat` argument, each iteration MUST decrement it, and at zero the phase MUST return its current state, so Go, Rust, and Lean stop at the same iteration. [just lean-parity]
- lean-reference-73: Reaching the fuel MUST be a normal return, never an error. [just proofs]
- lean-reference-74: The network simplex pivots MUST have `fuel = pivot_factor * nodes`, with `pivot_factor` 50, and each applied pivot lowers the cost, so a capped run still satisfies `simplex_cost_le_init`. [just proofs]
- lean-reference-75: The layer sweeps MUST have `fuel = sweep_max`, which is 24, and the loop MUST also stop after `sweep_stall`, which is 4, sweeps without improvement. [just proofs]
- lean-reference-76: The transpose passes MUST have, per transpose call, `fuel = c0 + 1`, where `c0` is the crossing count of the layer with its fixed neighbour layers when the call starts; each pass that swaps lowers that count by at least 1, so a clean pass ends the loop before the fuel is spent, and this MUST be the only fuel that depends on the input. [just proofs]
- lean-reference-77: The portfolio candidates MUST have `fuel = min(thoroughness, portfolio_max)`, with `portfolio_max` 5. [just proofs]
- lean-reference-78: Cycle breaking MUST recurse on the depth-first search over unvisited nodes, and feasible-tree growth MUST add one node per step, so it takes at most `nodes - 1` steps. [just proofs]
- lean-reference-79: `sweep_max`, `sweep_stall`, `pivot_factor`, and `portfolio_max` MUST be keys of `spec/data/layout-constants.json`. [just gen-check]
- lean-reference-80: The other caps MUST be the keys `architecture.bfs_cap` (2000), `mindmap.contour_cap` (2000), `chart.scan_cap` (40), `treemap.squarify_cap` (2000), `sankey.iterations` (6), `venn.acos_iterations` (16), `venn.bisect_iterations` (32), and `cynefin.wave_segments` (7), and a phase with no loop MUST recurse structurally on a list whose length `WithinLimits` bounds. [just proofs]

## Kernel and validator theorems

- lean-reference-81: The proofs of this table MUST hold, in the files that the table names under `proofs/`. [just proofs]

    |Theorem|File (under `proofs/`)|Statement|
    |---|---|---|
    |`Rect.disjoint_comm`|`ElegantGeometry/Disjoint.lean`|`Disjoint a b <-> Disjoint b a`|
    |`Rect.disjoint_translate`|`ElegantGeometry/Disjoint.lean`|for successful `translate a dx dy = a'` and `translate b dx dy = b'`: `Disjoint a b <-> Disjoint a' b'`|
    |`Rect.contains_translate`|`ElegantGeometry/Basic.lean`|for successful translations `a'` and `b'` by the same `(dx, dy)`: `contains a b <-> contains a' b'`|
    |`Rect.contains_trans`|`ElegantGeometry/Basic.lean`|`contains a b -> contains b c -> contains a c`|
    |`Rect.bbox_contains`|`ElegantGeometry/Basic.lean`|`bbox rs = .ok b -> forall r in rs, valid r -> contains b r`, where `bbox : List Rect -> Except LayoutError Rect` folds `union` from the first element of `rs` and returns `.error domain` for `[]`|
    |`placeAfter_disjoint`|`ElegantGeometry/Disjoint.lean`|`0 <= gap -> placeAfter axis a gap s = .ok p -> Disjoint a p`|
    |`compact_pairwise_disjoint`|`ElegantGeometry/Compaction.lean`|`0 <= gap -> compact axis gap items = .ok out -> List.Pairwise Disjoint out`|
    |`compact_preserves_order`|`ElegantGeometry/Compaction.lean`|`compact axis gap items = .ok out -> forall i < j, p_i(out) <= p_j(out)`, and `out[i]` has the cross coordinates of `items[i]`|
    |`compact_respects_gaps`|`ElegantGeometry/Compaction.lean`|`compact axis gap items = .ok out -> forall i, p_i(items) <= p_i(out)` and `p_{i+1}(out) >= p_i(out) + len_i(out) + gap`|
    |`Segment.cross_comm`|`ElegantGeometry/Crossings.lean`|`Segment.cross s t = Segment.cross t s`|
    |`Segment.cross_iff_common_interior_point`|`ElegantGeometry/Crossings.lean`|`Segment.cross s t = true <-> exists p with rational coordinates, p in interior s and p in interior t`|
    |`inversions_eq_crossings`|`ElegantGeometry/Crossings.lean`|for edges `e_k = (top_k, bot_k)` between two layers with position maps `P` and `Q`: let `n` be the number of unordered edge pairs `{e, f}` with `(P e.top - P f.top) * (Q e.bot - Q f.bot) < 0`; `countInversions` of the bottom positions, taken in the order sorted by `(P top, Q bot)`, is `.ok n` when `n <= I32_MAX` and `.error LayoutError.overflow` otherwise; the statement has no side hypothesis|
    |`Validator.sound`|`ElegantGeometry/Validator.lean`|`WellFormed d -> Validator.check d = true -> HardConstraints d`|

- lean-reference-82: `Validator.sound` MUST be proved by unfolding `check`, rewriting each Boolean test to its predicate, and closing the conjunction with `simp` over `Int`, using only the Lean core library. [just proofs]
- lean-reference-83: `just kernel-diff` MUST run `go run ./tools/kernelgen > corpus/.cache/kernel/cases.txt`, then `geomcheck eval`, `bin/emd-go kernel-eval`, and `bin/emd-rs kernel-eval` on that file, and it MUST fail on any byte difference. [just kernel-diff]
- lean-reference-84: Unit tests MUST NOT call Lean, and they MUST use naive in-language oracles. [just go-check]

## Work packet and contingency

- lean-reference-85: The work packet for one kind MUST have four workers, the spec worker first, then the Go, Rust, and Lean workers. [just proofs]
- lean-reference-86: The Lean worker MUST write `proofs/Elegant/Kinds/<Kind>.lean`, extend the family module when the kind is the family's first, prove the theorems the packet names, and report the theorem names to the parent, which appends them to `proofs/theorems.txt` because one file serves every kind. [just proofs]
- lean-reference-87: The packet gates MUST add `just proofs` and `just lean-parity KIND=<kind>`. [just lean-parity]
- lean-reference-88: If `lean-parity` finds a difference, the specification MUST decide which side is wrong, that side MUST be fixed, and the gate MUST NOT change. [just lean-parity]
- lean-reference-89: The product claim table MUST carry the Lean row, whose gates are `just proofs` and `just lean-parity`: the Lean reference proves that each layout and text heuristic terminates, keeps its invariants, and never worsens its own measure, and that every layout satisfies the hard constraints, while Go and Rust match that reference byte for byte on the corpus and the shipped Go and Rust code carries no proof of its own. [just proofs]

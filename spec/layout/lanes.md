# Lanes layout family

This file defines the lanes layout family: its entry points and inputs, the gitgraph, eventmodeling, timeline, and journey rules, and its proofs.

## Entry and inputs

- lanes-01: The Go entry points MUST be `func GitGraph`, `func EventModeling`, `func Timeline`, and `func Journey`, each with the signature `(ctx context.Context, in <Kind>Input, p params.Params) (*scene.Scene, error)`, in package `internal/layout/lanes`. [just parity]
    Rust: `layout::lanes::{gitgraph, eventmodeling, timeline, journey}`.
- lanes-02: The kind adapter MUST pass these inputs to the family. [just go-check]
    `GitGraphInput` holds branches (name, optional `order`, declaration index), commits in declaration order (user `id` or none, branch index, parents as commit indices, kind `normal | merge | cherry-pick`, label lines), and `head`.
    `EventModelingInput` holds swimlanes (index, lines) and boxes `(lane index, lines)`, plus relations `(source box, target box)`.
    `TimelineInput` holds sections (lines, period indices) and periods (lines, events with lines).
    `JourneyInput` holds sections (lines) and tasks `(section index, lines, score)`.
- lanes-03: The family MUST receive items and relations in declaration order, with integer indices, every label as measured `lines` with widths and heights in profile units, and no coordinates. [just lean-parity]
    A family never measures text. Its entry point also receives `params.Params` (package `internal/layout/params`; Rust `layout::params`), which holds the profile, the constants generated for that profile, `thoroughness`, `max_width`, and `limits`. Every tie-break uses declaration index as the last key. Divisions use `floor_div` unless a rule says otherwise, and `ceil_div(a, b)` is `floor_div(a + b - 1, b)` for `a >= 0` and `b > 0`. A vector value is in px and is stored as 1/64 px (px × 64). A cell value is in cells, and a vertical cell value is in rows.
- lanes-04: Every named lanes constant MUST be a key `<kind>.<name>` of `spec/data/layout-constants.json`, so a bare name `name` in one kind's rules means the key `<kind>.name` of that kind. [just gen-check]

## Gitgraph

- lanes-05: The gitgraph constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`gitgraph.commit_step`|40|2560|4|
    |`gitgraph.lane_pitch`|50|3200|2 rows|
    |`gitgraph.label_rotation_extra`|40|2560|0|
    |`gitgraph.label_offset`|10|640|1|
    |`gitgraph.commit_radius`|8|512|1|
    `commit_step` is upstream `COMMIT_STEP`, `label_offset` is `LAYOUT_OFFSET`, and `commit_radius` is this plan's own choice. `label_rotation_extra` is added only when the config key `gitGraph.rotateCommitLabel` is true: the renderer honours this key (`gitGraphRenderer.ts` lines 991 to 994 and 1008), and its default is `true` (`config.schema.yaml` lines 1067 to 1069). Upstream: `gitGraphRenderer.ts` lines 527 to 563, 614 to 620, 992 to 995 and `git/gitGraphAst.ts`.
- lanes-06: Lane order MUST sort branches ascending by the key `(order, declaration index)`. [just lean-parity]
    `order` is the branch's `order:` value, or 0 when it has none. The declaration index counts `main` as 0 and the other branches in declaration order, and it breaks ties. `main` has order 0; upstream's `mainBranchOrder` key (default 0, `config.schema.yaml` lines 1058 to 1060) is not read. This is upstream's rule. The parser sets `order: branch.order ?? 0` (`gitGraphParser.ts` line 63). `getBranchesAsObjArray` sorts by `order` with a stable sort (`gitGraphAst.ts` line 468), and `main` is seeded first in the branch map (`gitGraphAst.ts` line 57). The branch order is an integer (`gitGraph.langium` lines 35 to 37). The test 'should handle new branch checkout with and without order' (`gitGraph.spec.ts` from line 672) expects `main, test2, test3, test1` for `test1 order: 1`, `test2`, `test3`.
- lanes-07: Lane `k` MUST start at `y_k = sum of (lane_pitch + label_rotation_extra)` over the lanes before it. [just lean-parity]
- lanes-08: A root commit MUST have `x = 0`, and any other commit MUST have `x = max(parent x) + commit_step`. [just lean-parity]
    A merge has parents `[current head, merged head]`. A cherry-pick has parent `[current head]`, and it draws a dotted link from the picked commit that does not affect `x`. A branch created from a non-HEAD commit `s` has its first commit's parent set to `s`.
- lanes-09: A commit's y MUST be its branch's lane y, and its label MUST sit at `(x, lane_y + label_offset)`. [just lean-parity]
- lanes-10: A connector from parent `p` to child `c` in another lane MUST be orthogonal, with the points `(x_p, y_p)`, `(x_c - floor_div(commit_step, 2), y_p)`, `(x_c - floor_div(commit_step, 2), y_c)`, and `(x_c, y_c)`. [just lean-parity]
    In the same lane the connector is a straight segment.
- lanes-11: A commit id MUST be the user's `id:` value when given, and otherwise `<branch>-<n>`, where `n` is the 0-based index of the commit in declaration order over all commits. [just lean-parity]
    A generated id is unique because `n` contains no `-`, so the last `-` separates it. Upstream draws a random 7-character id here (`gitGraphAst.ts` lines 66 to 67); this plan removes the randomness. When `showCommitLabel` is on, the label is the id.
- lanes-12: A commit MUST land on the lane of the branch it lands on, so a merge commit sits on the lane of the branch it merges into and a cherry-picked commit sits on the lane of the branch it is picked onto, at the next step on that lane. [just lean-parity]
    A branch created from a non-HEAD commit keeps its lane in the lane order of requirement lanes-06, and its first commit's parent is that commit.

## Event modeling

- lanes-13: The eventmodeling constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`eventmodeling.swimlane_min_height`|70|4480|5|
    |`eventmodeling.swimlane_padding`|15|960|1|
    |`eventmodeling.swimlane_gap`|10|640|1|
    |`eventmodeling.box_padding`|10|640|1|
    |`eventmodeling.box_overlap`|90|5760|9|
    |`eventmodeling.box_min_width`|80|5120|10|
    |`eventmodeling.box_max_width`|450|28800|56|
    |`eventmodeling.box_min_height`|80|5120|5|
    |`eventmodeling.box_max_height`|750|48000|47|
    |`eventmodeling.content_start_x`|250|16000|25|
    Diagram `padding` default 30 (`config.schema.yaml` line 2825). Upstream: `eventmodeling/db.ts` lines 153 to 165, 425 to 436, 460 to 495 and `renderer.ts`.
- lanes-14: Lanes MUST be the entity types in swimlane index order, with lane `k` at `y = prev_y + prev_height + swimlane_gap` (first lane `y = 0`) and `height = max(swimlane_min_height, max box height in lane) + 2 * swimlane_padding`. [just lean-parity]
- lanes-15: A box MUST take `w = clamp(text_w, box_min_width, box_max_width) + 2 * box_padding` and `h = clamp(text_h, box_min_height, box_max_height) + 2 * box_padding`, at `y = lane_y + swimlane_padding`. [just lean-parity]
- lanes-16: A box x MUST follow `calculateX`: the first box starts at `content_start_x`, a box in the same lane as the previous box starts at `lane_right + box_padding`, and otherwise a box starts at `prev_box_right - box_overlap + box_padding`. [just lean-parity]
    A box's right is `x + w + box_padding`, and the lane's right is the last box's right.
- lanes-17: A relation MUST run from source x `src_x + floor_div(2 * w_src, 3)` to target x `tgt_x + floor_div(w_tgt, 3)`. [just lean-parity]
    It is upward when the source lane is lower: it starts at the source top and ends at the target bottom. Otherwise it starts at the source bottom and ends at the target top. Vector: one straight segment (upstream `renderer.ts` lines 61 to 96). Cell: a vertical segment from the source, then a horizontal segment to the target.

## Timeline

- lanes-18: The timeline constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`timeline.card_width`|150|9600|18|
    |`timeline.column_gap`|50|3200|6|
    |`timeline.event_gap`|10|640|1|
    |`timeline.section_gap`|50|3200|3|
    |`timeline.card_padding`|20|1280|1|
    |`timeline.left_margin`|50|3200|6|
    `card_padding` applies on each side. Upstream: `timelineRenderer.ts` lines 34, 73, 87 to 93, 150, 181, 333, 354 to 375.
- lanes-19: Period `k` (0-based) MUST have column left `left_margin + k * (card_width + column_gap)`, with column pitch 200 px / 24 cells. [just lean-parity]
- lanes-20: A section band MUST span its periods, with width `pitch * n - column_gap` (`200 n - 50`), starting at x of its first period's column. [just lean-parity]
- lanes-21: Events MUST stack in their period's column in order, event `k` MUST have height `text_h + 2 * card_padding`, and event `k + 1` MUST start `event_gap` below event `k`'s bottom. [just lean-parity]
    Section bands are `section_gap` apart vertically (upstream `masterY += maxSectionHeight + 50`).

## Journey

- lanes-22: The journey constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`journey.task_width`|150|9600|18|
    |`journey.task_height`|50|3200|3 rows|
    |`journey.column_gap`|50|3200|6|
    |`journey.score_step`|30|1920|2 rows|
    |`journey.score_min`|1|1|1|
    |`journey.score_max`|5|5|5|
    |`journey.band_height`|50|3200|3 rows|
    |`journey.face_radius`|10|640|1|
    `task_width` is upstream `width` default 150 (`config.schema.yaml` journey `$defs`). Upstream config `height` 50 and `diagramMarginX` 50 (`config.schema.yaml` lines 1846 to 1868). Upstream: `user-journey/svgDraw.js` lines 171 to 227.
- lanes-23: Task `k` MUST have column left `k * (task_width + column_gap)`. [just lean-parity]
- lanes-24: A section band MUST span its tasks, with width `n * task_width + (n - 1) * column_gap` and height `band_height`, placed at the top. [just lean-parity]
- lanes-25: A face MUST be centred at `y = band_bottom + (score_max - score) * score_step + score_step`. [just lean-parity]
    This matches upstream's `cy = 300 + (5 - score) * 30` (`svgDraw.js` line 218) with the origin moved to the band bottom. The task box top is `band_bottom + (score_max - score_min + 2) * score_step` (180 px), below all faces.
- lanes-26: A score outside `score_min` to `score_max` MUST raise the error `journey/score-out-of-range`. [just go-check]
    Upstream does not check.

## Integer rules for the proofs

- lanes-27: The proof MUST take the gitgraph lane key as `(order, index)`, where `order` is the `order:` value, or 0 for a branch without one and for `main`, and `index` is the declaration index with `main` at 0. [just proofs]
    Lanes are the branches sorted by this key. A commit's x is 0 for a root and `max(parent x) + gitgraph.commit_step` otherwise.
- lanes-28: The proof MUST take gitgraph lane `k` at `y_k = sum over j < k of (gitgraph.lane_pitch + gitgraph.label_rotation_extra)`, and eventmodeling lane `k` at `y_k = y_(k-1) + height_(k-1) + eventmodeling.swimlane_gap`, with the first lane at `y = 0`. [just proofs]
    Timeline columns use the pitch of requirement lanes-19, not bands.
- lanes-29: The proof MUST take a journey score `s` in `[journey.score_min, journey.score_max]` as `y(s) = band_bottom + (journey.score_max - s) * journey.score_step + journey.score_step`, so a higher score is higher on the page. [just proofs]
    The map is linear with negative slope; no scale call is used.

## Theorems

- lanes-30: The proof `gitgraph_lanes_sorted` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: `List.Pairwise keyLt lanes` and `lanes` is `List.mergeSort` of the branches by the lane key.
    Proof approach: `List.pairwise_mergeSort`; the key is strict because `index` is unique.
- lanes-31: The proof `gitgraph_one_lane_per_branch` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: `lanes` is a permutation of the branches, so each branch has exactly one lane.
    Proof approach: `List.mergeSort_perm`; `List.Nodup` transfers through the permutation.
- lanes-32: The proof `gitgraph_commit_steps_increasing` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: each non-root commit has `x` strictly greater than the `x` of each parent.
    Proof approach: definitional; `omega`.
- lanes-33: The proof `eventmodeling_timeframes_ordered` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: box x positions are strictly increasing in declaration order.
    Proof approach: each step adds at least `eventmodeling.box_min_width + 2 * eventmodeling.box_padding - eventmodeling.box_overlap > 0`.
- lanes-34: The proof `eventmodeling_entity_lanes_disjoint` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: the entity-type lane bands are pairwise disjoint.
    Proof approach: `compact_pairwise_disjoint`.
- lanes-35: The proof `timeline_period_columns_disjoint` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: period columns are pairwise disjoint and in declaration order.
    Proof approach: `compact_pairwise_disjoint` and `compact_preserves_order`.
- lanes-36: The proof `timeline_events_stack_disjoint` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: events of one period are pairwise disjoint, in declaration order.
    Proof approach: induction on the event list; `placeAfter_disjoint`.
- lanes-37: The proof `journey_task_columns_ordered` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: tasks `i < j` have `x i < x j`.
    Proof approach: `compact_preserves_order`.
- lanes-38: The proof `journey_score_antitone` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: `s <= s'` implies `y s' <= y s`.
    Proof approach: linear with negative slope; `omega`.
- lanes-39: The proof `journey_section_bands_disjoint` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: section bands are pairwise disjoint.
    Proof approach: `compact_pairwise_disjoint`.
- lanes-40: The proof `journey_task_inside_section` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: `contains section.rect task.rect` for each task.
    Proof approach: `omega` on the band bounds.
- lanes-41: The proof `lanes_valid` MUST hold in `proofs/Elegant/Lanes.lean`. [just proofs]
    Statement: `WellFormed m -> WithinLimits m -> Lanes.layout m = .ok s -> HardConstraints s` for the four kinds.
    Proof approach: combines the rows above.
- lanes-42: The lanes family MUST have no fuel loop. [just proofs]
    The sort is `List.mergeSort`, which is total. Every other phase is a fold over a declaration list.
- lanes-43: The Lean reference module MUST be `proofs/Elegant/Lanes.lean`, serving the kinds `gitgraph` (header `gitGraph`), `eventmodeling`, `timeline`, and `journey`, with the functions `Lanes.gitgraph`, `Lanes.eventmodeling`, `Lanes.timeline`, `Lanes.journey`, and `Lanes.layout`. [just proofs]
    The `gitgraph` packet MUST build this family module, because `gitgraph` is the family's first kind. The other lanes kinds wait for it. Every packet gates on `just proofs` and `just lean-parity KIND=<kind>`.

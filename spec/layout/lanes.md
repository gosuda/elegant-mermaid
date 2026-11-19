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
    `order` is the branch's `order:` value, or 0 when it has none. The declaration index counts the main branch as 0 and the other branches in declaration order, and it breaks ties. The main branch has order 0 unless `gitGraph.mainBranchOrder` sets another integer (requirement lanes-48). This is upstream's rule. The parser sets `order: branch.order ?? 0` (`gitGraphParser.ts` line 63). `getBranchesAsObjArray` sorts by `order` with a stable sort (`gitGraphAst.ts` line 468), and the main branch is seeded first in the branch map (`gitGraphAst.ts` line 57). The branch order is an integer (`gitGraph.langium` lines 35 to 37). The test 'should handle new branch checkout with and without order' (`gitGraph.spec.ts` from line 672) expects `main, test2, test3, test1` for `test1 order: 1`, `test2`, `test3`.
- lanes-07: Lane `k` of the lane order MUST start at the lane-axis coordinate `L_k = L_(k-1) + gap_k`, with `L_0 = 0`. [just lean-parity]
    The lane axis is y under `LR` and x under `TB` and `BT`. Under `LR`, `gap_k` follows requirement lanes-50. Under `TB` and `BT`, `gap_k` is the lane pitch of requirement lanes-47, which starts at `lane_pitch + label_rotation_extra`.
- lanes-08: A commit MUST have level `max(parent level + 1, previous level + 1)`, where `previous level` is the level of the commit declared last before it on the same lane, and each term MUST count as 0 when it does not exist. A commit MUST sit at the commit-axis position `axis[level]`, with `axis[0] = 0` and `axis[l] = axis[l - 1] + gap(l)` under the commit gap of requirement lanes-49. [just lean-parity]
    The commit axis is x under `LR` and y under `TB` and `BT`. Only a link from an earlier-declared commit to a later one gives a parent, and a cherry-pick link never gives one. The `previous level` term never raises a level when every commit's parent is its lane's previous commit, which holds for every graph without a duplicate commit id. A duplicate id (`spec/grammar/gitgraph.md`, requirement gitgraph-27) can leave a commit whose only parent link runs backward, and this term keeps it right of the earlier commits of its lane, so two commits of one lane never share a level and their labels never overlap.
    A merge has parents `[current head, merged head]`. A cherry-pick has parent `[current head]`, and it draws a dotted link from the picked commit that does not affect `x`. A branch created from a non-HEAD commit `s` has its first commit's parent set to `s`.
- lanes-09: A commit's y MUST be its branch's lane y, and its label MUST sit at `(x, lane_y + label_offset)`. [just lean-parity]
- lanes-10: A connector from parent `p` to child `c` in another lane MUST be orthogonal, with the points `(x_p, y_p)`, `(x_c - turn_back(c), y_p)`, `(x_c - turn_back(c), y_c)`, and `(x_c, y_c)`. [just lean-parity]
    In the same lane the connector is a straight segment. The turn is taken `turn_back(c) = floor_div(commit_step, 2)` before the child under `TB` and `BT`. Under `LR`, `turn_back(c) = max(floor_div(commit_step, 2), floor_div(reach(level(c)), 2) + floor_div(label_gap + 1, 2))`, so the vertical segment of the connector runs in the clear strip left of the labels of the child's level and never crosses the label text of the cell renderer. The points are written for `LR`; `TB` and `BT` transpose the two axes by requirement lanes-47.
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
- lanes-14: Lanes MUST be the entity types in swimlane index order, with lane `k` at `y = prev_y + prev_height + swimlane_gap` (first lane `y = 0`) and `height = max(swimlane_min_height, max box height in lane, lane label height) + 2 * swimlane_padding`. [just lean-parity]
- lanes-15: A box MUST take `w = clamp(text_w, box_min_width, box_max_width) + 2 * box_padding` and `h = clamp(text_h, box_min_height, box_max_height) + 2 * box_padding`, at `y = lane_y + swimlane_padding`. [just lean-parity]
- lanes-16: A box x MUST follow `calculateX` in this integer form. [just lean-parity]
    Let `r = x + w + box_padding` for a placed box, and let `lane_r` be the `r` of the latest earlier box in the same lane, or 0 when there is none. The first box starts at `gutter`. Every other box starts at `max(prev_r - box_overlap + box_padding, lane_r)`, where `prev_r` is the `r` of the previous box in declaration order. `gutter = max(content_start_x, 2 * label_inset + widest lane label width)` and `label_inset = 2 * swimlane_padding`. The canvas adds `canvas_margin` on every side.
- lanes-17: A relation MUST run from source x `src_x + floor_div(2 * w_src, 3)` to target x `tgt_x + floor_div(w_tgt, 3)`. [just lean-parity]
    It is upward when the source lane is lower on the page: it starts at the source top and ends at the target bottom. Otherwise it starts at the source bottom and ends at the target top. Vector: the segment between those two points, when no other frame has its interior on it; otherwise the corridor route of requirement lanes-31 (upstream `renderer.ts` lines 61 to 96 draw the segment only).
- lanes-30: A lane MUST span `x = 0` to `x = max_r + swimlane_padding`, where `max_r` is the largest `r` of any box. [just lean-parity]
    A lane label MUST be a `label` role text at `(label_inset, lane_y + swimlane_padding)`, wrapped at `content_start_x - 2 * label_inset`. A frame name MUST wrap at `box_max_width`. A frame data block follows the name after a gap of `line_h`, in the `body` role. The frame text block sits at the vertical centre of the box inside `box_padding`, and its top is never above the box content area.
- lanes-31: Corridors MUST be the horizontal gaps between lanes. [just lean-parity]
    The corridor above the first lane is at `y = floor_div(swimlane_padding, 2)`. The corridor below the lane at position `k` is at `lane_bottom + floor_div(swimlane_gap, 2)`. A corridor route runs source port, source corridor, column, target corridor, target port. When the source lane is above the target lane, the source corridor is the one below the source lane and the target corridor is the one above the target lane. When the source lane is below the target lane, the source corridor is the one above the source lane and the target corridor is the one below the target lane. In one lane both corridors are the one above that lane, and both ports are on the box top edges. The column is the first of the source port x and the target port x whose vertical run between the two corridors meets no other frame, and otherwise `max_r`. Repeated points and collinear middle points are removed. Under the cell profile every relation uses the corridor route.

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

- lanes-27: The proof MUST take the gitgraph lane key as `(order, index)`, where `order` is the `order:` value, or 0 for a branch without one, and for the main branch the value of `gitGraph.mainBranchOrder`, or 0 when the key is absent, and `index` is the declaration index with the main branch at 0. [just proofs]
    Lanes are the branches sorted by this key. A commit's commit-axis position is `axis[level]` of requirement lanes-08.
- lanes-28: The proof MUST take gitgraph lane `k` at `L_k = L_(k-1) + gap_k` with the gaps of requirement lanes-07, and eventmodeling lane `k` at `y_k = y_(k-1) + height_(k-1) + eventmodeling.swimlane_gap`, with the first lane at `y = 0`. [just proofs]
    Timeline columns use the pitch of requirement lanes-19, not bands.
- lanes-29: The proof MUST take a journey score `s` in `[journey.score_min, journey.score_max]` as `y(s) = band_bottom + (journey.score_max - s) * journey.score_step + journey.score_step`, so a higher score is higher on the page. [just proofs]
    The map is linear with negative slope; no scale call is used.

## Theorems

- lanes-57: The proof `gitgraph_lanes_sorted` MUST hold in `proofs/Elegant/LanesFacts.lean`. [just proofs]
    Statement: `List.Pairwise keyLt lanes` and `lanes` is `List.mergeSort` of the branches by the lane key.
    Proof approach: `List.pairwise_mergeSort`; the key is strict because `index` is unique.
- lanes-58: The proof `gitgraph_one_lane_per_branch` MUST hold in `proofs/Elegant/LanesFacts.lean`. [just proofs]
    Statement: `lanes` is a permutation of the branches, so each branch has exactly one lane.
    Proof approach: `List.mergeSort_perm`; `List.Nodup` transfers through the permutation.
- lanes-32: The proof `gitgraph_commit_steps_increasing` MUST hold in `proofs/Elegant/LanesFacts.lean`. [just proofs]
    Statement: each non-root commit has a commit-axis position strictly greater than that of each parent.
    Proof approach: the level of a commit is at least one more than the level of each parent, and the commit axis is strictly increasing in the level.
- lanes-59: The proof `gitgraph_lane_steps_increasing` MUST hold in `proofs/Elegant/LanesFacts.lean`. [just proofs]
    Statement: of two commits of one lane, the later-declared has the greater commit-axis position.
    Proof approach: strong induction on the commit index; the level of a commit is at least one more than the level of its lane's previous commit, which by the induction hypothesis has the greatest level on the lane so far.
- lanes-60: The proof `gitgraph_rejects_rl` MUST hold in `proofs/Elegant/LanesFacts.lean`. [just proofs]
    Statement: the gitgraph planner returns the domain error for the direction `RL`, which is not a gitgraph direction (requirement gitgraph-02 and gitgraph-29 of `spec/grammar/gitgraph.md`); the Go and Rust planners return their domain errors for it too. The adapters name every direction other than `LR`, `TB`, and `BT` as `RL`.
    Proof approach: the planner tests the direction before it loads the constants; unfolding.
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
- lanes-41: The proof `Elegant.Lanes.lanes_valid` MUST hold in `proofs/Elegant/FamilyValidity.lean`. [just proofs]
    Statement: `WellFormed m -> WithinLimits m -> m.kind ∈ ["gitgraph", "eventmodeling", "timeline", "journey"] -> Elegant.kindLayout m = some (.ok result) -> HardConstraints result.scene.layoutDump`.
    Proof approach: dispatch on the family membership and apply the public kind validity proofs, which combine the geometry rows above.
- lanes-42: The lanes family MUST have no fuel loop. [just proofs]
    The sort is `List.mergeSort`, which is total. Every other phase is a fold over a declaration list.
- lanes-43: The per-kind geometry reference module MUST remain `proofs/Elegant/Lanes.lean`, serving the kinds `gitgraph` (header `gitGraph`), `eventmodeling`, `timeline`, and `journey`. Unified model-stage dispatch MUST use `Elegant.kindLayout` in `proofs/Elegant/KindLayout.lean`; family validity MUST use `Elegant.Lanes.lanes_valid` in `proofs/Elegant/FamilyValidity.lean` over the explicit family domain in lanes-41. [just proofs]
    The `gitgraph` packet MUST build this family module, because `gitgraph` is the family's first kind. The other lanes kinds wait for it. Every packet gates on `just proofs` and `just lean-parity KIND=<kind>`.

## Gitgraph geometry details

- lanes-44: The gitgraph planner MUST also read these constants. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`gitgraph.tag_offset`|16|1024|0|
    |`gitgraph.tag_pad`|4|256|0|
    |`gitgraph.label_gap`|24|1536|2|
    |`gitgraph.branch_pad_x`|12|768|0|
    |`gitgraph.branch_pad_y`|8|512|0|
    `tag_offset` is the gap between a commit and its lowest tag box, `tag_pad` pads a tag plate and separates stacked tags, `label_gap` is how far a lane line starts before the commit axis origin and the least clear distance between the labels of adjacent commit levels under `LR` (requirement lanes-49), and `branch_pad_x` and `branch_pad_y` pad the branch label plate. These are this plan's own choices; upstream has no counterpart.
- lanes-45: Every commit box MUST have zero width and height, and every lane frame MUST be a zero-thickness segment from `-label_gap` to `max_step + floor_div(commit_step, 2)` along the commit axis, through the lane's commits. [just validate]
    A frame with area would contain foreign commits and labels, which the `frame-clearance` clause of the validator forbids.
- lanes-46: Under `LR`, a commit's id label MUST be centred on the commit x at `y + label_offset`, and its tags MUST be centred on the commit x above the commit: the first tag at `y - tag_offset - h`, each next tag raised by its height plus `2 * tag_pad`. [just lean-parity]
- lanes-47: Under `TB` and `BT`, the commit axis MUST be y (`BT` at `y = max_step - step`) and the lane axis x, and the lane pitch MUST grow by the widest side-text extent and MUST be at least the widest branch label plate width plus `label_gap`. [just lean-parity]
    The side text of a commit is its id label, then its tags, each placed right of the commit at `label_offset` after the previous one and centred on the commit y. The extent is the right edge of the last box relative to the commit x. Under `BT`, a branch label plate starts 1 cell below the lane end in the cell profile, and at the lane end in the vector profile, so the plate does not cover the last cell of its lane.
- lanes-48: The main branch MUST take its name and its order from `gitGraph.mainBranchName` and `gitGraph.mainBranchOrder` when the frontmatter config or a `%%{init}%%` directive sets them, and otherwise it MUST be named `main` with order 0. [just oracle]
    The rules of `spec/grammar/gitgraph.md`, requirement gitgraph-28, define which values the keys accept. The main branch keeps the declaration index 0 whatever its name and order.
- lanes-49: Under `LR`, the commit gap `gap(l)` between level `l - 1` and level `l` MUST be `max(commit_step, ceil_div(reach(l - 1) + reach(l), 2) + label_gap)`, in the units of the profile. [just lean-parity]
    `reach(l)` is the largest text width of a commit of level `l`: the width of its id label, or the width of one of its tags plus `2 * tag_pad`, whichever is wider, and 0 for a commit with neither. `ceil_div(a, b)` is `floor_div(a + b - 1, b)`. The labels, and the tags, of adjacent levels therefore stay at least `label_gap` apart, and the cell renderer never overwrites label text. Under `TB` and `BT` the gap is `commit_step`, because side labels do not meet along the commit axis.
- lanes-50: Under `LR`, the gap `gap_k` between lane `k - 1` (`upper`) and lane `k` (`lower`) MUST be `max(P, below(upper) + above(lower))`, with `P = lane_pitch + label_rotation_extra`. [just lean-parity]
    `below(b)` is `label_offset` plus the largest label height among the commits of lane `b` that have a label, and 0 when none has one. `above(b)` is `tag_offset + tag_pad` plus the largest value of `sum of tag heights + 2 * tag_pad * (n - 1)` among the commits of lane `b` that have `n >= 1` tags, and 0 when none has tags. The label band of the upper lane and the tag band of the lower lane therefore never meet.

## Timeline geometry details

- lanes-51: Every section, period, and event card MUST have the width `card_w = max(timeline.card_width, widest period or event text + 2 * card_padding, section need)`. [just lean-parity]
    A section needs `ceil_div(text_w + 2 * card_padding - (n - 1) * column_gap, n)`, where `n` is the number of slots its band spans under `LR` and 1 under `TB`. Period and event text wraps at `card_width - 2 * card_padding`, and section text wraps at `n * card_width + (n - 1) * column_gap - 2 * card_padding`. Every period card is as tall as the tallest period text plus `2 * card_padding`, every section card is as tall as the tallest section text plus `2 * card_padding`, and an event card is its text height plus `2 * card_padding`.
- lanes-52: Periods MUST take consecutive slots in declaration order: first the periods that precede the first section, then the periods of each section in section order. A section with no period MUST keep one slot. [just lean-parity]
    The left edge of slot `s` is `left_margin + s * (card_w + column_gap)`, and the band of a section that spans `n` slots is `n * (card_w + column_gap) - column_gap` wide. A period without a section has no band. Its series index is the series index rule of requirement lanes-55.
- lanes-53: Under `LR`, the sections MUST sit at the top of the content, the periods `section_gap` below the section bands (at the top of the content when there are no sections), and the events of a period MUST start `section_gap` below the period row and stack in its column with `event_gap` between cards. [just lean-parity]
    The title, when present, is centred over the content and sits `event_gap` above it. The time axis runs from `x = 0` to the right edge of the last column plus `column_gap`, at `y = period_bottom + floor_div(section_gap, 2)`, with the marker `point` at its end towards `+x`. An event link is a straight vertical segment from the bottom of the card above it (the period for the first event) to the top of the event, in the profile's dotted line style, with no marker.
- lanes-54: Under `TB` and `BT`, the periods MUST stand in one column at `x = left_margin`, the events in a second column at `x = left_margin + card_w + column_gap`, and the axis MUST run down the gutter at `x = left_margin + card_w + floor_div(column_gap, 2)`. [just lean-parity]
    A section band is `card_w` wide over the period column. Rows are separated by `section_gap`, and a row is as tall as its period card or its event stack, whichever is taller. Each event link runs from the right-middle of its period to the axis and on to the left-middle of its event; when the two middles share a `y`, the link is one straight segment. The axis marker points towards `+y`, and the axis ends `section_gap` below the last row.
- lanes-55: A period card and a section band MUST use the style `series-tint` with the series index of the section (section `s` has index `s % 12`), and with the period index `i % 12` when the diagram has no section. An event card MUST use the style `node`. [just validate]
    A period before the first section of a diagram with sections has series 0. A section band is drawn with the `emphasis` width. In the cell profile a section band and an event are `Rect` items, a period is a `RoundRect`. Every text takes the style `text`, because the style `text-on-series` can need a plate that this layout does not draw.
- lanes-56: The model stage MUST name the boxes `title`, `s<k>` for section `k`, `p<i>` for period `i`, and `p<i>.e<k>` for event `k` of period `i`, and the routes `e<n>` in declaration order. A box whose text equals its id MUST take the id with the suffix `~`. [just parity]
    A period box has the shape `period`, or `period:<k>` when it belongs to section `k`. The shapes of the other boxes are `title`, `section`, and `event`. Under `LR`, an event link joins the event to the previous card of its period (the period for the first event). Under `TB` and `BT`, every event link starts at the period.

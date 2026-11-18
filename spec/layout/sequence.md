# Sequence layout family

This file defines the sequence layout family: its inputs, its constants, its actors, notes, rows, fragments, numbering, line kinds, markers, labels, and its proofs.

## Entry and inputs

- sequence-01: The Go entry point MUST be `func Layout(ctx context.Context, in Input, p params.Params) (*scene.Scene, error)` in package `internal/layout/sequence`, and the Rust entry point MUST be `layout::sequence::layout(input: &Input, params: &Params) -> Result<Scene, LayoutError>`. [just parity]
- sequence-02: The kind adapter MUST pass this `Input` to the family. [just go-check]
    `Actors` (declaration order; label lines; `wrap`; `CreatedAt` and `DestroyedAt` event index or none; `Box` index or none).
    `Events` (declaration order): `Message{From, To, Lines, Dotted, Number, Creates, Destroys}`, `Note{Placement: left_of | right_of | over, Actors, Lines}`, `FragmentStart{Kind: loop | alt | opt | par | critical | break | rect, Lines}`, `FragmentElse{Lines}` (`else`, `and`, `option`), `FragmentEnd`, `ActivateStart{Actor}`, `ActivateEnd{Actor}`.
    `Boxes` (actor index range; `Lines`).
- sequence-03: The family MUST receive its items and relations in declaration order, with integer indices into those lists, every label as measured `lines` with a width and a height in profile units, and no coordinates. [just lean-parity]
    A family never measures text. Its entry point also receives `params.Params` (package `internal/layout/params`; Rust `layout::params`), which holds the profile, the constants generated for that profile, `thoroughness`, `max_width`, and `limits`. Every tie-break uses declaration index as the last key. Divisions use `floor_div` unless a rule says otherwise, and `ceil_div(a, b)` is `floor_div(a + b - 1, b)` for `a >= 0` and `b > 0`. A vector value is in px and is stored as 1/64 px (px × 64). A cell value is in cells, and a vertical cell value is in rows.

## Constants

- sequence-04: Every named sequence constant MUST be a key `<kind>.<name>` of `spec/data/layout-constants.json`, so a bare name `name` in this file means `sequence.name`. [just gen-check]
    The body line height `L1` is not a key: it is the `label` role line height of spec/text-measurement.md, 20 px / 1 row.
- sequence-05: The sequence constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`sequence.actor_width`|150|9600|12|
    |`sequence.actor_height`|65|4160|3|
    |`sequence.actor_margin`|50|3200|4|
    |`sequence.wrap_padding`|10|640|1|
    |`sequence.box_margin`|10|640|1|
    |`sequence.box_text_margin`|5|320|1|
    |`sequence.note_margin`|10|640|1|
    |`sequence.message_top`|10|640|1|
    |`sequence.self_loop_depth`|30|1920|2|
    |`sequence.self_loop_min_dx`|30|1920|3|
    |`sequence.activation_width`|10|640|1|
    |`sequence.activation_top`|2|128|0|
    |`sequence.label_box_width`|50|3200|8|
    |`sequence.label_box_height`|20|1280|1|
    |`sequence.dash_on`|3|192|1|
    |`sequence.dash_off`|3|192|1|
    |`sequence.autonumber_radius`|6|384|1|
    |`sequence.diagram_margin_x`|50|3200|2|
    |`sequence.diagram_margin_y`|10|640|1|
- sequence-06: The default values of the upstream sequence keys MUST be recorded with the constants, and upstream `messageMargin` MUST NOT be a key. [just gen-check]
    Upstream defaults: `actorMargin` 50, `width` 150, `height` 65, `boxMargin` 10, `boxTextMargin` 5, `noteMargin` 10, `messageMargin` 35, `activationWidth` 10, `diagramMarginX` 50, `diagramMarginY` 10, `labelBoxWidth` 50, `labelBoxHeight` 20 (`config.schema.yaml`, sequence `$defs` at lines 2211 to 2376); `wrapPadding` 10 (line 874). The message row rule of the rows section replaces `messageMargin`. Nested activation bars move right by `floor_div(sequence.activation_width, 2)` per level, so no separate step key exists. Fragment frames extend `sequence.box_margin` beyond their members on the left, right, and bottom, and their top is the fragment's first row.

## Actors and canvas

- sequence-07: Lifelines MUST follow actor declaration order, except that an actor declared in a participant `box` MUST follow the last earlier actor of the same box, so that the actors of one box have adjacent lifelines. Every actor box MUST have the height `h = max(actor_height, text_h + 2 * box_text_margin)`, for a wrapped actor and for an unwrapped actor, in the vector profile and in the cell profile. [just lean-parity]
    Actor width `w` is `actor_width` when the actor is wrapped. Otherwise it is `max(actor_width, text_w + 2 * wrap_padding)`. `text_h` is `n * L1`, where `n` is the number of measured lines of the actor label. A one-line label gives `h = actor_height` in both profiles. In the cell profile, a two-line label gives `h = 4`. The centre `c` is the centre of the box.
- sequence-08: The family MUST translate every x so that the leftmost drawn point sits at `diagram_margin_x`, then add `diagram_margin_x` on the right and `diagram_margin_y` at the top and bottom. [just lean-parity]
    The leftmost drawn point includes left notes and frames.

## Column gaps

- sequence-09: The centre distance `d_g` between adjacent lifelines `g` and `g+1` MUST start at `floor_div(w_g + w_(g+1), 2) + actor_margin`. [just lean-parity]
- sequence-10: A message from lifeline `i` to lifeline `j > i` MUST widen the gaps it spans so that their sum covers its label. [just lean-parity]
    The label width is `m = text_w + 2 * wrap_padding`, where `text_w` is the widest measured line. Messages and notes are processed in event order. Let `k = j - i` and `D = m + actor_margin - sum(d_g for g in [i, j))`. When `D > 0`, add `floor_div(D, k)` to each `d_g` in `[i, j)`, then add 1 to the first `D mod k` gaps in index order. For `k = 1` this gives `d >= m + actor_margin`.
- sequence-11: A self message on lifeline `a` MUST set `dx = max(floor_div(m, 2), self_loop_min_dx)` and MUST require `d_a >= dx + actor_margin` when lifeline `a + 1` exists. [just lean-parity]
    The loop draws `dx` to the right of `c_a`. Upstream draws the loop to `max(text_w / 2, width / 2)` (`svgDraw.js`, self-message branch near line 433); this family uses the smaller `dx`, so the loop cannot overlap the next lifeline.
- sequence-12: A created actor MUST add `floor_div(w, 2)` to the gap to its left neighbour. [just lean-parity]
    Upstream: `sequenceRenderer.ts` lines 786 to 788.

## Notes

- sequence-13: A note `over` one lifeline `a` MUST take width `max(w_a, text_w + 2 * note_margin)`, centred on `c_a`, and MUST require `floor_div(width, 2) + actor_margin` for each existing adjacent gap. [just lean-parity]
- sequence-14: A note `over` lifelines `a..b` (two or more) MUST span from `min(c) - floor_div(actor_margin, 2)` to `max(c) + floor_div(actor_margin, 2)`, with width at least `text_w + 2 * note_margin`, and its span MUST widen gaps by the message rule with `m` equal to the note width. [just lean-parity]
- sequence-15: A note `right of a` MUST have left `= c_a + floor_div(w_a, 2) + floor_div(actor_margin, 2)` and width `max(w_a, text_w + 2 * note_margin)`, and a note `left of a` MUST have right `= c_a - floor_div(w_a, 2) - floor_div(actor_margin, 2)` and the same width. [just lean-parity]
    A `right of a` note requires `d_a >= floor_div(w_a, 2) + 2 * floor_div(actor_margin, 2) + width`. A `left of a` note requires `d_(a-1) >= floor_div(w_a, 2) + 2 * floor_div(actor_margin, 2) + width`.
- sequence-16: A note MUST have row height `box_margin + text_h + 2 * note_margin` and top `row_top + box_margin`. [just lean-parity]
    Note text of `n` lines has `text_h = n * L1`. Upstream: `drawNote`, `sequenceRenderer.ts` lines 243 to 285.

## Rows

- sequence-17: A message row MUST have height `message_top + L + box_margin`, with the label in `[row_top + message_top, row_top + message_top + L)` and the arrow at `y = row_top + message_top + L`. [just lean-parity]
    `n` is the line count and `L = n * L1`. Vector: `20n + 20` px. Cell: `n + 2` rows. Upstream `boundMessage` (`sequenceRenderer.ts` lines 407 to 449) gives the same single-line proportions.
- sequence-18: A self message row MUST have height `message_top + L + box_margin + self_loop_depth`, and the loop MUST leave at `y` and return at `y + self_loop_depth`. [just lean-parity]
    Cell: `n + 4` rows.
- sequence-19: A create message MUST take the message row and then `h + box_margin` more, where `h` is the actor height of the created actor (sequence-07), with the created box top at the arrow `y`. [just lean-parity]
    The created box has the width `w` and the height `h` of sequence-07, and it is centred on the lifeline of the created actor. Upstream: lines 845 to 847.
- sequence-20: A destroy message MUST draw one scene-only `crosshead` marker on the lifeline of the destroyed actor at the arrow `y`, and the lifeline MUST end at that `y`. [just lean-parity]
    The destroyed actor keeps its one header box. The layout dump holds one box for each actor, and it holds no separate destroyed box. The marker is a `MarkerRef` named `crosshead` with axis `+y` at `(c, y)`, where `c` is the lifeline centre of the destroyed actor and `y` is the arrow `y` of the destroy message. The marker is in the `node` group of the destroyed actor, after the lifeline. It is not a dump box, route, or label. The cell profile draws the glyph `×`, and the ASCII charset draws `x` (sequence-35). The destroy message takes its normal row height, and no advance follows the row. Upstream draws a second actor box centred on the arrow (lines 1010 to 1034); this family MUST NOT.
- sequence-21: `ActivateStart` MUST take zero height, and the bar MUST start at `row_top + activation_top` and end at the row top of its `ActivateEnd`. [just lean-parity]
    Bar x is `c + (depth - 1) * floor_div(activation_width, 2)`, where `depth` counts open activations on that lifeline including this one. Bar width is `activation_width`. Upstream: `sequenceRenderer.ts` lines 151 to 156.
- sequence-22: The first message row MUST start at `actor_top + band_h + 2 * box_margin`, where `band_h` is the greatest actor height `h` of sequence-07 over all actors. [just lean-parity]
    `actor_top` is the top of the actor header boxes. It is the header height of the tallest participant `box` group (sequence-30), or 0 when the diagram has no such group.

## Fragments

- sequence-23: A fragment header MUST have height `section_h = max(box_margin + box_text_margin + label_box_height, box_margin + box_text_margin + n * L1)`, where `n` is the number of measured lines of the title label (35 px for a one-line title; cell 3 rows), and its content MUST start at `top + section_h`. [just lean-parity]
- sequence-24: `FragmentElse` MUST draw a dotted divider at the current `y` across the frame, start a new section header at the divider with the height `section_h` of sequence-23 for the lines of the section title, and centre the section title horizontally at `divider_y + box_margin + box_text_margin`. [just lean-parity]
- sequence-25: `FragmentEnd` MUST set the frame bottom to `y + box_margin`. [just lean-parity]
- sequence-26: A frame MUST have natural left `= min(member left) - box_margin` and natural right `= max(member right) + box_margin`, and sequence-27 MUST set its final width. [just lean-parity]
    Members are message spans (a self loop spans `[c - dx, c + dx]`), note boxes, and nested frames. A nested frame is a member, so each nesting level sits `box_margin` inside its parent: the nesting step is `box_margin`.
- sequence-27: A frame of a kind other than `rect` MUST have a width of at least `label_box_width + 2 * box_margin`, at least `title_w + 2 * box_margin`, and at least `section_w + 2 * box_margin` for each of its `else` section titles. [just lean-parity]
    `title_w` is the width of `[text]` measured on one line. `section_w` is the width of the widest measured line of one `else`, `and`, or `option` section title, without brackets. `natural` is the natural right minus the natural left of sequence-26. The frame width is the greatest of `natural` and these minimums. When the frame width is more than `natural`, `extra = width - natural` is split: the left edge moves `floor_div(extra, 2)` left of the natural left, and the right edge moves `extra - floor_div(extra, 2)` right of the natural right. A `rect` frame has the width `natural`. Upstream: `calculateLoopBounds`, `sequenceRenderer.ts` near line 2094.
- sequence-28: The kind label box MUST sit at the frame top-left, `label_box_width` by `label_box_height`, and the bracketed title MUST be centred in the frame at `top + box_margin + box_text_margin`. [just lean-parity]
- sequence-29: A `rect` fragment MUST have no label box and no header, with a header and a footer of `box_margin` each, and a fill only. [just lean-parity]
- sequence-30: A `box` participant group MUST have header `text_h + box_margin`, and MUST span `[left of first actor, right of last actor]` plus `box_text_margin` on each side, widened symmetrically to `max(inner + 2 * box_text_margin, text_w + 2 * wrap_padding)`. [just lean-parity]
    This differs from upstream's `8 * box_margin` reservation (`sequenceRenderer.ts` lines 1673 to 1692). The right edge of an actor box is `c + (w - floor_div(w, 2))`; for an odd `w` it is one unit right of `c + floor_div(w, 2)`.
- sequence-58: A `box` participant group with no member actor MUST NOT be a box of the dump, and it MUST have no label. [just go-check: TestSequenceBoxWithoutMemberIsNotADumpBox]
    A frame around no actor has no extent to place.
- sequence-59: For each `box` participant group, the gap between the first member and its left neighbour, and the gap between the last member and its right neighbour, MUST be widened by the rule of sequence-10 until the frame, extended by `box_text_margin` and by its extra width, ends before the neighbouring actor box and before the frame of the neighbouring group. [just lean-parity]
    With `reach_right = box_text_margin + (extra - floor_div(extra, 2))` and `reach_left = box_text_margin + floor_div(extra, 2)`, the gap `g` between lifelines `a` and `a + 1` needs `(w_a - floor_div(w_a, 2)) + floor_div(w_(a+1), 2) + reach_right(a) + reach_left(a + 1)`, where a reach is 0 for an actor that is not the last or first member of a group. `extra` is the extra width of the title (sequence-30).
- sequence-57: A fragment box id MUST be `f` followed by the zero-based count of fragments that started earlier in declaration order, nested fragments included. When that id is already used, the fragment MUST take `<id>~N` for the least `N >= 1` whose id is free. [just go-check: TestSequenceFragmentIDsCountFragmentsInDeclarationOrder]
    An id is used when a participant group box (`box<n>`), an actor box, or an earlier fragment, note (`note<n>`), or message route (`e<n>`) already has it. Actor boxes are made before any event, so an actor named like the fragment id always keeps its name. Example: three fragments started before a fourth gives `f3`, whether they are nested or not; with an actor `f0`, the first fragment takes `f0~1`. The title label of a frame has the id `<id>.label`, and its `k`th `else`, `and`, or `option` section title (zero-based) has the id `<id>.s<k>`.

## Autonumber

- sequence-31: A `Number` message MUST take `k` equal to 1 plus the count of earlier numbered messages. [just lean-parity]
    Vector: a circle of radius `autonumber_radius` centred on the sender lifeline at the arrow `y`. Cell: no badge is drawn, and the label is `(k) ` followed by the message text, or `(k)` alone when the message has no text. The label is measured and placed with that prefix. Upstream places the badge at the sender (`sequenceRenderer.ts` lines 701 to 708).

## Line kinds

- sequence-32: A solid line MUST have no dash, and a dotted line MUST use `dash_on` on and `dash_off` off. [just lean-parity]
    Dotted lines are `-->`, `-->>`, and the other dotted kinds. Upstream uses `3, 3` (`sequenceRenderer.ts` line 564). Fragment dividers use the same pattern (`svgDraw.js` lines 1548 to 1551). Cell: horizontal dotted lines use `┄`, solid use `─`, and lifelines are solid (`│`).
- sequence-33: A message arrow token MUST be one of this closed list, and the listed `Line` value MUST set `Dotted` on the `Message` record. [just lean-parity]
    |Token|LINETYPE|Line|Arrowhead|
    |---|---|---|---|
    |`->>`|`SOLID`|solid|end: `arrowhead`|
    |`-->>`|`DOTTED`|dotted|end: `arrowhead`|
    |`<<->>`|`BIDIRECTIONAL_SOLID`|solid|start and end: `arrowhead`|
    |`<<-->>`|`BIDIRECTIONAL_DOTTED`|dotted|start and end: `arrowhead`|
    |`->`|`SOLID_OPEN`|solid|none|
    |`-->`|`DOTTED_OPEN`|dotted|none|
    |`-x`|`SOLID_CROSS`|solid|end: `crosshead`|
    |`--x`|`DOTTED_CROSS`|dotted|end: `crosshead`|
    |`-)`|`SOLID_POINT`|solid|end: `filled-head`|
    |`--)`|`DOTTED_POINT`|dotted|end: `filled-head`|
    |`-\|\`|`SOLID_TOP`|solid|end: `solidTopArrowHead`|
    |`-\|/`|`SOLID_BOTTOM`|solid|end: `solidBottomArrowHead`|
    |`-\\`|`STICK_TOP`|solid|end: `stickTopArrowHead`|
    |`-//`|`STICK_BOTTOM`|solid|end: `stickBottomArrowHead`|
    |`--\|\`|`SOLID_TOP_DOTTED`|dotted|end: `solidTopArrowHead`|
    |`--\|/`|`SOLID_BOTTOM_DOTTED`|dotted|end: `solidBottomArrowHead`|
    |`--\\`|`STICK_TOP_DOTTED`|dotted|end: `stickTopArrowHead`|
    |`--//`|`STICK_BOTTOM_DOTTED`|dotted|end: `stickBottomArrowHead`|
    |`/\|-`|`SOLID_ARROW_TOP_REVERSE`|solid|start: `solidBottomArrowHead`|
    |`\\|-`|`SOLID_ARROW_BOTTOM_REVERSE`|solid|start: `solidTopArrowHead`|
    |`//-`|`STICK_ARROW_TOP_REVERSE`|solid|start: `stickBottomArrowHead`|
    |`\\-`|`STICK_ARROW_BOTTOM_REVERSE`|solid|start: `stickTopArrowHead`|
    |`/\|--`|`SOLID_ARROW_TOP_REVERSE_DOTTED`|dotted|start: `solidBottomArrowHead`|
    |`\\|--`|`SOLID_ARROW_BOTTOM_REVERSE_DOTTED`|dotted|start: `solidTopArrowHead`|
    |`//--`|`STICK_ARROW_TOP_REVERSE_DOTTED`|dotted|start: `stickBottomArrowHead`|
    |`\\--`|`STICK_ARROW_BOTTOM_REVERSE_DOTTED`|dotted|start: `stickTopArrowHead`|

## Markers

- sequence-34: The `Message` record MUST carry `HeadStart` and `HeadEnd`, each `none` or one of the seven marker names of the sequence marker table. [just go-check]
    The seven sequence markers are rows of `spec/data/markers.json` as well, beside the 25 of `markers.js`. Their points are written by hand once from the marker definitions in upstream `packages/mermaid/src/diagrams/sequence/svgDraw.js`, by the two rules of the Markers bullet of spec/scene.md. Their other fields are the marker table of requirement sequence-35.
- sequence-35: The seven sequence markers MUST have these `paint`, `cell`, and `ascii` values in `spec/data/markers.json`. [just gen-check]
    |Marker|`paint`|`cell` (+x, -x, +y down, -y up)|`ascii`|
    |---|---|---|---|
    |`arrowhead`, `solidTopArrowHead`, `solidBottomArrowHead`|`filled`|▶ ◀ ▼ ▲|`> < v ^`|
    |`filled-head`, `stickTopArrowHead`, `stickBottomArrowHead`|`open`|`> < v ^`|`> < v ^`|
    |`crosshead`|`open`|× (U+00D7) for all four|`x`|

## Labels

- sequence-36: A label of `n` lines MUST take `n` lines of `L1`, MUST be centred between its end centres for a message or on its note, and MUST have the width of its widest line. [just lean-parity]

## Integer rules for the proofs

- sequence-37: The proofs MUST use `x_i` as the lifeline x of participant `i` in declaration order, and `gap_i = x_(i+1) - x_i` as the centre distance before widening. [just proofs]
    The base distance is `floor_div(w_i + w_(i+1), 2) + sequence.actor_margin`. A label width `m = text_w + 2 * sequence.wrap_padding` is the widest of its lines.
- sequence-38: A message that spans lifelines `i..j` MUST widen the gaps `i..j-1` so that their sum is at least `m + sequence.actor_margin`, splitting the extra with `floor_div` over the gaps and giving the remainder to the first gaps in index order. [just proofs]
- sequence-39: The proofs MUST use the recurrences `x_(i+1) = x_i + gap_i` and `y_k = y_(k-1) + row_h_(k-1)`, where row heights come from the notes, rows, and fragments sections and each is at least `sequence.message_top` (10 px), so `row_h >= 1`. [just proofs]
- sequence-40: The proof MUST use the activation bar x `x_i + (depth(a) - 1) * floor_div(sequence.activation_width, 2)` for activation `a` on a lifeline. [just proofs]
- sequence-41: The proof MUST use the span of a note over lifelines `i..j` as `x_i - floor_div(sequence.actor_margin, 2)` to `x_j + floor_div(sequence.actor_margin, 2)`. [just proofs]

## Theorems

- sequence-42: The proof `sequence_columns_ordered` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: `i < j -> x i < x j`.
    Proof approach: induction on the participant list; `gap_i >= 1`.
- sequence-43: The proof `sequence_columns_separated` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: `i + 1 < n -> x (i+1) - x i = gap i and gap i >= sequence.actor_margin`.
    Proof approach: definitional unfolding; `omega`.
- sequence-44: The proof `sequence_gap_covers_labels` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: every message between `i` and `i+1` has label width `m` with `m + sequence.actor_margin <= gap i`.
    Proof approach: induction on the message list; `le_max` over the fold.
- sequence-45: The proof `sequence_span_label_fits` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: every message spanning `i..j` has `m + sequence.actor_margin <= x j - x i` after widening.
    Proof approach: induction on the gap list; `omega` on the split sum.
- sequence-46: The proof `sequence_self_loop_clear` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: every self-message on `i` with loop extent `dx` has `x i + dx + sequence.actor_margin <= x (i+1)`.
    Proof approach: `gap i >= dx + sequence.actor_margin` by the widening rule plus the gap identity; `omega`.
- sequence-47: The proof `sequence_message_at_lifeline` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: a non-self message starts at `x (from m)` and ends at `x (to m)`; a self-message ends at `x (from m) + dx`, where `dx` is the loop extent of the self message rule.
    Proof approach: case split on message kind; `omega`.
- sequence-48: The proof `sequence_message_ends_on_headers` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: each message start lies on the bottom edge of its `from` header box, and each end lies on the bottom edge of its `to` header box.
    Proof approach: definitional; `omega` on the header bounds.
- sequence-49: The proof `sequence_rows_strictly_increasing` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: `forall k, y k < y (k+1)`.
    Proof approach: induction on the event list (messages, notes, fragment boundaries); `sequence.message_top >= 1`.
- sequence-50: The proof `sequence_activations_nest` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: under `BarInv` (the open bars of each lifeline are a stack: a lifeline whose counter is `d` has exactly one open bar at each depth `1` to `d`), for open bars `a` and `b` of one lifeline with `a.depth < b.depth`, the deactivation of that lifeline leaves `a` open, so the inner bar closes first.
    Proof approach: the deactivation closes the open bar of the greatest depth, and `BarInv` makes the depths of the open bars of one lifeline distinct.
    The statement over the opening and closing rows, `a.open <= b.open < a.close -> b.close <= a.close`, is false when two activations open on one row, because their opening rows tie.
- sequence-51: The proof `sequence_activation_depth_offset` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: for bars `a` and `b` of one lifeline with centre `c`, `a.x = c + (a.depth - 1) * h` and `b.x = c + (b.depth - 1) * h` with `h = floor_div(sequence.activation_width, 2)` and `0 < h`: `a.depth < b.depth -> a.x < b.x`.
    Proof approach: the product of the depth difference and `h` is positive; `omega`. `h` is positive under the vector profile (`vector_activation_step_pos`). Under the cell profile `h` is 0, so nested bars share one column and the statement does not apply.
- sequence-52: The proof `sequence_frames_contain_members` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: for each fragment `f`: `contains f.rect r` for each member row box `r`, and `contains f.rect g.rect` for each nested fragment `g`.
    Proof approach: structural recursion on the fragment tree; `Rect.bbox_contains`.
- sequence-53: The proof `sequence_notes_contain_span` MUST hold in `proofs/Elegant/SequenceFacts.lean`. [just proofs]
    Statement: for a note over two different lifelines `i < j`: `x i - floor_div(sequence.actor_margin, 2) <= note.x` and `note.right <= x j + floor_div(sequence.actor_margin, 2)`.
    Proof approach: the columns were widened to hold the note text (sequence-14), so `omega` on the bounds. A note over one lifeline is not covered: its width can exceed the margin.
- sequence-54: The proof `sequence_valid` MUST hold in `proofs/Elegant/SequenceValid.lean` over the executable `Sequence.layout` of `proofs/Elegant/Sequence.lean`. [just proofs]
    Statement: `WellFormed m -> WithinLimits m -> Sequence.layout m = .ok s -> HardConstraints s`.
    Proof approach: combines the rows above: message ends lie on header boxes, frames and notes contain their members, columns are ordered.
    Before the geometry walk, the Lean developer model input MUST pass the sequence-specific semantic consistency check: message events correspond to routes in declaration order and name their actor endpoints; note, created-actor, and fragment boxes are placed once in their declared scope; participant groups have consecutive member actors and consistent title labels. Participant header frames MUST contain their members and remain clear of other participant frames and actors outside their membership. A model dump that fails this check returns `LayoutError.domain`; this does not change the accepted Mermaid language. Parser-produced valid sequence models MUST continue to pass the check and the sequence parity gates. The validity theorem has no additional admissibility hypothesis, and the input check MUST NOT call the final layout validator.
- sequence-55: The sequence family MUST have no fuel loop. [just proofs]
    Every phase recurses structurally on the participant, message, or fragment list. The list lengths are bounded by `WithinLimits`.
- sequence-56: The Lean reference module MUST be `proofs/Elegant/Sequence.lean`, serving the kind `sequence` (header `sequenceDiagram`), with the functions `Sequence.columns` (lifeline centres), `Sequence.walk` (rows, notes, fragments, activation bars), and `Sequence.layout : Model -> Except LayoutError Scene`, and the theorems of sequence-42 to sequence-54 MUST be in `proofs/Elegant/SequenceFacts.lean` and `proofs/Elegant/SequenceValid.lean`. [just proofs]
    The `sequence` packet MUST build this family module, because `sequence` is the family's first kind. The packet gates MUST include `just proofs` and `just lean-parity KIND=sequence`.

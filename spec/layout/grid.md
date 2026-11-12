# Grid layout family

This file defines the grid layout family: its four entry points and inputs, the block, architecture, kanban, and packet rules, and its proofs.

## Entry and inputs

- grid-01: The Go entry points MUST be `func Block(ctx context.Context, in BlockInput, p params.Params) (*scene.Scene, error)`, `func Architecture(ctx context.Context, in ArchitectureInput, p params.Params) (*scene.Scene, error)`, `func Kanban(ctx context.Context, in KanbanInput, p params.Params) (*scene.Scene, error)`, and `func Packet(ctx context.Context, in PacketInput, p params.Params) (*scene.Scene, error)` in package `internal/layout/grid`. [just parity]
    Rust: `layout::grid::{block, architecture, kanban, packet}`.
- grid-02: The kind adapter MUST pass these inputs to the family. [just go-check]
    `BlockInput` is a tree of `Block{Columns (unset = -1), Children}` and `Child{Kind: block | space | arrow, Span (>= 1, default 1), Lines or nested Block}`.
    `ArchitectureInput` holds services and junctions (declaration order), groups with member indices, and edges `(from, from_side, to, to_side, lines)`, where a side is `L`, `R`, `T`, or `B`.
    `KanbanInput` holds sections in order, each with cards (`title lines`, optional `ticket`, `assigned`, `priority`).
    `PacketInput` holds blocks `(start, end, lines)` in declaration order plus `bits_per_row`, `bit_width`, `row_height`, `padding_x`, `padding_y`, `show_bits`, and `bit_order`.
- grid-03: The family MUST receive items and relations in declaration order, with integer indices, every label as measured `lines` with widths and heights in profile units, and no coordinates. [just lean-parity]
    A family never measures text. Its entry point also receives `params.Params` (package `internal/layout/params`; Rust `layout::params`), which holds the profile, the constants generated for that profile, `thoroughness`, `max_width`, and `limits`. Every tie-break uses declaration index as the last key. Divisions use `floor_div` unless a rule says otherwise, and `ceil_div(a, b)` is `floor_div(a + b - 1, b)` for `a >= 0` and `b > 0`. A vector value is in px and is stored as 1/64 px (px × 64). A cell value is in cells, and a vertical cell value is in rows.
- grid-04: Every named grid constant MUST be a key `<kind>.<name>` of `spec/data/layout-constants.json`, so a bare name `name` in one kind's rules means the key `<kind>.name` of that kind. [just gen-check]

## Block

- grid-05: `block.padding` MUST be 8 px / 1 cell. [just gen-check]
    The constant is a key of `spec/data/layout-constants.json`: `block.padding` is 8 px (512 units) and 1 cell.
    Upstream `padding` default 8, `config.schema.yaml` line 2813.
- grid-06: `Columns` unset or `-1` MUST give one row holding all children, and `Columns = N >= 1` MUST give N columns. [just lean-parity]
    A child that does not fit the rest of its row is clipped to the rest of the row (`span = columns - position mod columns`), and the next child starts the next row. Upstream: `block/layout.ts` lines 232 to 241 and 310 to 315.
- grid-07: Child `i` MUST take `position` in declaration order, with column `position mod columns` and row `floor_div(position, columns)`. [just lean-parity]
    `columns = 1` stacks children vertically.
- grid-08: A `space` child MUST take `span` columns, have no size, and add no row height. [just lean-parity]
    An `arrow` child is an ordinary leaf: it fills its span box with a directional polygon, and its height is the row height.
- grid-09: An intrinsic leaf size MUST be `w = text_w + 2 * padding` and `h = text_h + 2 * padding`, and a nested block's intrinsic size MUST be its own layout size, computed by the same rules. [just lean-parity]
- grid-10: The column unit `U` MUST be the maximum over leaves of `ceil_div(w, span)` in the block, and a child of span `s` MUST be `U * s + padding * (s - 1)` wide. [just lean-parity]
    A row's height is the maximum child height in that row, and every child in the row takes it. Upstream: `block/layout.ts` lines 61 to 117.
- grid-11: The block origin MUST start `x` at `padding`, add each child's width plus `padding` per child, start rows at `padding`, and add each row's height plus `padding` per row. [just lean-parity]
    The block size is the content plus `padding` on each side.

## Architecture

- grid-12: The architecture rules MUST replace the upstream cytoscape-fcose layout. [just lean-parity]
    Defaults: `padding` 40 (group padding), `iconSize` 80, `fontSize` 16 (`config.schema.yaml` lines 1150 to 1158). Upstream lays out with cytoscape-fcose (`architectureRenderer.ts` lines 297 to 310, 448 to 451).
- grid-13: Each architecture node MUST occupy one cell of an integer grid, with cell `(x, y)` at top-left `(x * pitch_x, y * pitch_y)`. [just lean-parity]
    The constants are keys of `spec/data/layout-constants.json`.
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`architecture.pitch_x`|120|7680|14 columns|
    |`architecture.pitch_y`|120|7680|6 rows|
    |`architecture.padding`|40|2560|2|
    |`architecture.junction_size`|8|512|1|
    |`architecture.icon_width`|80|5120|7 columns|
    |`architecture.icon_height`|80|5120|3 rows|
    |`architecture.label_wrap`|112|7168|13|
    |`architecture.bfs_cap`|2000|2000|2000|
    The group frame uses `line_height`, the layered `line_h` of `spec/data/layout-constants.json`: 1280 units and 1 cell. Upstream `iconSize` 80 and `fontSize` 16 are config defaults, not layout constants; text sizes come from the role table of `spec/text-measurement.md`.
- grid-14: The seed MUST be the first declared node (service or junction) at `(0, 0)`, the queue MUST be FIFO, nodes MUST be dequeued in placement order, and the incident edges of each dequeued node `u` MUST be scanned in declaration order. [just lean-parity]
- grid-15: For an unplaced neighbour `v` across edge `e`, the placement MUST try the side of `e` at `u` first, then the remaining sides in the order `L`, `R`, `T`, `B`. [just lean-parity]
    The step for `L` is `(-1, 0)`, `R` is `(+1, 0)`, `T` is `(0, -1)`, and `B` is `(0, +1)`. Take the first free cell whose group rule (requirement grid-17) holds. If all four are unavailable, take the free cell nearest to `u` by Manhattan distance, with ties by lower row, then lower column.
- grid-16: An unplaced node after the queue empties MUST seed a new component at `x = max_x + 2`, `y = 0`, where `max_x` is the largest occupied `x`. [just lean-parity]
- grid-17: A group frame MUST be the bounding rectangle of its member cells, inflated by `architecture.padding` (40 px / 2 cells) on each side and by one `line_height` at the top for the label. [just lean-parity]
    A cell is free for group `G` only when the bounding rectangle of `G`'s members plus that cell does not intersect any other group's frame. Frames are therefore disjoint.
- grid-18: A junction MUST occupy one cell with a `junction_size` (8 px / 1 cell) marker and four ports, and MUST have no label. [just lean-parity]
- grid-19: Labels MUST sit under the icon, wrapping at `architecture.label_wrap`, which is `pitch_x - 8` px, that is 112 px (7168 units) in vector and `pitch_x - 1` cell, that is 13 cells in cell. [just lean-parity]
    The icon box is `icon_width` by `icon_height` (80 by 80 px; 7 by 3 cells), centred in the cell. In the cell profile it is drawn as `spec/scene.md` states.
- grid-20: Edges MUST leave and enter at the side named at each end, with the ports and routes of requirements grid-21 to grid-23. [just lean-parity]
    The layered port and slot rules of `spec/layout/routing.md` do not apply to this kind.
- grid-21: A service box MUST be its icon box and a junction box MUST be its marker, and for cell `(x, y)` a box of size `w` by `h` MUST have top-left `x0 = x * pitch_x + floor_div(pitch_x - w, 2)` and `y0 = y * pitch_y + floor_div(pitch_y - h, 2)`. [just lean-parity]
    Its side points are `L` = `(x0, y0 + floor_div(h, 2))`, `R` = `(x0 + w, y0 + floor_div(h, 2))`, `T` = `(x0 + floor_div(w, 2), y0)`, and `B` = `(x0 + floor_div(w, 2), y0 + h)`.
- grid-22: Each service edge end MUST have its own port `p`. [just lean-parity]
    When `k` service ends use one side, end `i` (0-based) sits at offset `floor_div((i + 1) * len, k + 1)` from the start of that side, where `len` is `w` for `T` and `B` and `h` for `L` and `R`, and the start is `x0` for `T` and `B` and `y0` for `L` and `R`. The port `p` is the side point moved to that offset. For `k = 1` the offset is the midpoint. Ends sort by the other node's cell `y` on `L` and `R`, or cell `x` on `T` and `B`, then by edge declaration index. Every edge end on one junction side uses that side point. The offset formula applies for every `k`; with many ends the ports may be closer than `port_gap`. For a service that has a label, the `B` side point is moved down to the bottom edge of the label box, so the stub of a `B` port starts under the label and never crosses its text.
- grid-23: Grid routes MUST use these gutter lines and these three cases, in the first case that holds. [just lean-parity]
    For every integer `k`, the vertical gutter line `X_k` is at `k * pitch_x` in vector and `k * pitch_x - 1` in cell. The horizontal gutter line `Y_k` is at `k * pitch_y` in vector and `k * pitch_y - 1` in cell. These lines lie in the free gaps between cell boxes. For cell `(x, y)`, the line of its `L` side is `X_x`, of its `R` side `X_(x+1)`, of its `T` side `Y_y`, and of its `B` side `Y_(y+1)`.
    The gutter point `g` of a port `p` is `p` moved onto its side line: `g = (line, p.y)` for `L` and `R`, and `g = (p.x, line)` for `T` and `B`. Let `a` be the edge's first end and `b` its second.
    - Case 1, same line: the two side lines are equal, and the route is `p(a), g(a), g(b), p(b)`.
    - Case 2, same axis, different lines: if both lines are vertical, the route is `p(a), g(a), (line(a), Y_y), (line(b), Y_y), g(b), p(b)`, where `Y_y` is the top line of the cell of `a`; if both lines are horizontal, the route is `p(a), g(a), (X_x, line(a)), (X_x, line(b)), g(b), p(b)`, where `X_x` is the left line of the cell of `a`.
    - Case 3, perpendicular: the route is `p(a), g(a), (X, Y), g(b), p(b)`, where `X` is the vertical line and `Y` the horizontal line of the two ends.
    Remove any point equal to the point before it. The 8 perpendicular side pairs use case 3. The 8 same-axis pairs use case 1 or case 2, by their lines, whether or not the sides face each other. Routes that run on the same gutter line share that segment as a trunk and are drawn once.
- grid-24: The grid output MUST take the origin and canvas rule of the layered packing phase. [just lean-parity]
- grid-25: Service and junction boxes MUST be exclusive, and group frames MUST NOT be exclusive. [just lean-parity]
    A route is stubs from ports to gutter points, plus segments on gutter lines. No stub enters an icon or junction box, and no gutter line crosses one, so route-clearance holds for every grid route. Grid edges have no straight route through a cell, so no detour rule exists.

## Kanban
- grid-26: The kanban constants MUST have these values, and `kanban.gutter` MUST be 10 px / 1 cell on both axes, that is `round_half_up(10 / 8) = 1` column and `ceil_div(10, 16) = 1` row. [just gen-check]
    The constants are keys of `spec/data/layout-constants.json`.
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`kanban.section_width`|200|12800|25|
    |`kanban.padding`|8|512|1|
    |`kanban.gutter`|10|640|1 column, 1 row|
    |`kanban.label_band_min`|25|1600|1 row|
    |`kanban.card_pad_x`|20|1280|3 columns|
    |`kanban.card_pad_y`|10|640|0 rows|
    |`kanban.card_gap`|5|320|1 row|
    |`kanban.section_min_height`|50|3200|4 rows|
    Defaults: `sectionWidth` 200 and `padding` 8 (`config.schema.yaml` lines 1264 to 1268). The renderer hard-codes a gutter of 10 (`kanbanRenderer.ts` lines 41 to 42, "TODO set padding").
- grid-27: Section `k` (1-based) MUST have width `section_width` (200 px / 25 cells, `ceil_div(200, 8)`), and its centre x MUST be `section_width * k + floor_div((k - 1) * gutter, 2)` in the vector profile and `25 * k + (k - 1)` in the cell profile. [just lean-parity]
    Each gap is one gutter cell and `floor_div(1, 2)` is 0, so the `floor_div` form is a vector-profile fact only. Upstream positions a section by its centre (`kanbanRenderer.ts` line 51). The canvas is the bounding box of all sections plus `kanban.padding` on each side (8 px / 1 cell; this plan keeps the config value, while upstream `kanbanRenderer.ts` line 95 reads `mindmap.padding`, 10 px), so the offset of section 1 leaves no empty band.
- grid-28: The section header band MUST be `max(label_band_min, label_h)` (25 px / 1 row minimum), and card width MUST be `section_width - floor_div(3 * gutter, 2)` (185 px / 24 cells, which is `25 - floor_div(3, 2)` in cells and equals `ceil_div(185, 8)`). [just lean-parity]
    Upstream `kanbanRenderer.ts` line 79 computes `WIDTH - 1.5 * padding`.
- grid-29: Card text MUST be the title wrapped to card width minus `2 * card_pad_x`, then one line per present field in the order `ticket:`, `assigned:`, `priority:`. [just lean-parity]
    `kanban.card_pad_x` is 20 px / 3 columns: upstream `kanbanDb.ts` lines 101 to 106 double `mindmap.padding` (10 px) for rect-type nodes, `[...]` items are rect-type (`kanbanDb.ts` line 182), and `kanbanItem.ts` line 41 uses that padding as the text inset.
- grid-30: Card height MUST be `text_h + 2 * card_pad_y`, where `kanban.card_pad_y` is 10 px (`kanbanItem.ts` line 83, `labelPaddingY`). [just lean-parity]
    In cells `card_pad_y` is 0 rows, and the top and bottom border rows add 2 rows, so the cell height is `text_rows + 2`.
- grid-31: The first card's top MUST be at `section_top + header_band`, and each next card MUST start `card_gap` below the previous card's bottom. [just lean-parity]
    `card_gap` is 5 px / 1 row. The identity `card_gap = floor_div(gutter, 2)` holds in the vector profile only; in cells `floor_div(1, 2)` is 0, so the cell card gap is 1 row, stated directly. Upstream `kanbanRenderer.ts` line 84 uses `padding / 2`.
- grid-32: Section height MUST be `max(last_card_bottom + floor_div(gutter, 2) - first_card_top + 3 * gutter, kanban.section_min_height) + (label_band - 25)`, with `section_min_height` 50 px / 4 rows. [just lean-parity]
    In cells `floor_div(gutter, 2)` is 0 rows and `3 * gutter` is 3 rows. Sections share the top edge. Upstream `kanbanRenderer.ts` lines 65 to 89.
- grid-33: A `ticket` value MUST be shown as text, with no link. [just lean-parity]
    Upstream builds a link from `ticketBaseUrl` (config default empty string); this plan keeps the text and drops the link in cells.

## Packet

- grid-34: The packet constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`packet.row_height`|32|2048|3 rows|
    |`packet.bit_width`|32|2048|2 columns|
    |`packet.padding_x`|5|320|1 column|
    |`packet.padding_y`|5|320|1 row|
    |`packet.bits_per_row`|32|32|32|
    Defaults: `rowHeight` 32, `bitWidth` 32, `bitsPerRow` 32, `paddingX` 5, `paddingY` 5, `showBits` true, `bitOrder` ascending (`config.schema.yaml` lines 2755 to 2800). The cell column values follow from the column rule: two columns per bit and one border column between fields. `row_height` is 3 rows, not `ceil_div(32, 16)` = 2, because a 2-row rectangle has no interior row for its label (a `rect` draws its sides on its boundary cells).
- grid-35: Row pitch MUST be `row_height + padding_y`, row `r` MUST start at `y = r * pitch + padding_y`, and the drawing width MUST be `bit_width * bits_per_row + 2`, with `2 * bits_per_row` columns in cell. [just lean-parity]
- grid-36: A field whose bits cross a row boundary MUST be cut at each boundary, and each piece MUST keep the field's label and be a separate rectangle on its row. [just lean-parity]
    Fields are assigned to rows in declaration order. Upstream: `packet/parser.ts` lines 71 to 76.
- grid-37: The column of a piece MUST be `start mod bits_per_row`, and with `bit_order` `descending` it MUST be `bits_per_row - start_col - bits`. [just lean-parity]
    The piece's x is `column * bit_width + 1` in vector. In cells it is `2 * column`, with no offset. Its width is `bits * bit_width - padding_x`, so adjacent fields are `padding_x` apart. Cell: `2 * bits - 1` columns, with one border column between fields. Upstream: `packet/renderer.ts` lines 56 to 58.
- grid-38: Bit numbers MUST sit above each row, at a vector baseline 2 px above the row top and at one row above in cell. [just lean-parity]
    A single-bit field's number is centred; a wider field shows its leading bit at the left and its trailing bit at the right.

## Integer rules for the proofs

- grid-39: The proof MUST take block children in declaration order, with a child at position `p` in column `p mod N` and row `floor_div(p, N)`, and a child whose span does not fit the rest of its row clipped to `N - (p mod N)` columns, with the next child starting the next row. [just proofs]
    The column unit `U` and `block.padding` give the widths.
- grid-40: The proof MUST take the architecture seed as the first declared node at `(0, 0)`, dequeue nodes in placement order, scan edges in declaration order, try the side of the edge at the dequeued node first and then `L`, `R`, `T`, `B` for an unplaced neighbour, and, when the queue empties, seed the next component at `x = max_x + 2`, `y = 0`. [just proofs]
    A group frame is the bounding box of its members, padded by `architecture.padding` and one `line_height` on top.
- grid-41: The proof MUST take kanban as one column per section, with cards stacked top to bottom with `kanban.card_gap`. [just proofs]
- grid-42: The proof MUST take packet fields laid out in declaration order over bit positions `0, 1, 2, ...`, with `packet.bits_per_row` bits per row and a field that crosses a row boundary becoming one piece per row. [just proofs]

## Theorems

- grid-43: The proof `block_cells_disjoint` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: for children `i != j` of one group, `Disjoint (rect i) (rect j)`.
    Proof approach: induction on the child list; children of one row have disjoint column ranges by the position rule, and different rows have disjoint y ranges.
- grid-44: The proof `block_span_honoured` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `rect.w = U * span + block.padding * (span - 1)`.
    Proof approach: induction on the span; `omega`.
- grid-45: The proof `block_within_columns` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: every placed child has `col + span <= cols`.
    Proof approach: clipping rule `span = cols - (position mod cols)`; `omega`.
- grid-46: The proof `block_children_inside_group` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `contains group.rect child.rect` at every nesting level.
    Proof approach: structural recursion on the block tree; `Rect.bbox_contains`.
- grid-47: The proof `arch_cells_unique` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: the cells of placed architecture nodes form a `List.Nodup`.
    Proof approach: invariant of the breadth-first loop: each placement takes a free cell.
- grid-48: The proof `arch_pops_bounded` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: the number of queue pops is `<= nodes.length`.
    Proof approach: each node is enqueued at most once; invariant on the visited set.
- grid-49: The proof `arch_all_placed` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `WithinLimits m -> nodes.length <= architecture.bfs_cap -> every node of m is placed`.
    Proof approach: fuel-bounded loop; invariant: remaining fuel >= unplaced node count.
- grid-50: The proof `arch_group_frame_contains_members` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `contains group.frame node.rect` for each member `node`.
    Proof approach: `Rect.bbox_contains` plus the fixed padding.
- grid-51: The proof `arch_routes_orthogonal` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: each architecture edge route is orthogonal, and its ends lie on the port boundaries.
    Proof approach: reuses `route_orthogonal` and `route_endpoints_on_ports` of the layered family.
- grid-52: The proof `kanban_columns_disjoint` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: the column rects are `List.Pairwise Disjoint`.
    Proof approach: `compact_pairwise_disjoint` over the section x positions of requirement grid-27.
- grid-53: The proof `kanban_cards_stacked` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `card (i+1).y = card i .y + card i .h + kanban.card_gap`, and all card rects of one column are pairwise disjoint.
    Proof approach: induction on the card list; `placeAfter_disjoint`.
- grid-54: The proof `kanban_column_contains_cards` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `contains column.rect card.rect` for each card.
    Proof approach: `omega` on the height sum; induction on the card list.
- grid-55: The proof `packet_bits_partitioned` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: every bit `b < total` belongs to exactly one field.
    Proof approach: induction on the field list; `omega` on bit offsets.
- grid-56: The proof `packet_rows_fit` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: each piece lies in one row: its bit range is inside `[row * packet.bits_per_row, (row+1) * packet.bits_per_row)`.
    Proof approach: `Int.fdiv` and `Int.fmod` identities; `omega`.
- grid-57: The proof `packet_piece_widths_sum` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: the piece widths of one field sum to the field width.
    Proof approach: induction on the piece list.
- grid-58: The proof `grid_valid` MUST hold in `proofs/Elegant/Grid.lean`. [just proofs]
    Statement: `WellFormed m -> WithinLimits m -> Grid.layout m = .ok s -> HardConstraints s` for the four kinds.
    Proof approach: combines the rows above; the routes come from the architecture router theorems.
- grid-59: The architecture breadth-first loop MUST recurse on the fuel `architecture.bfs_cap` (`spec/data/layout-constants.json`, value 2000, equal to the node limit). [just proofs]
    Block nesting recurses on the tree depth, which the `limit/nesting-depth` cap of `spec/preprocessing.md` bounds. Kanban and packet have no loop.
- grid-60: The Lean reference module MUST be `proofs/Elegant/Grid.lean`, serving the kinds `block` (headers `block`, `block-beta`), `architecture` (`architecture`, `architecture-beta`), `kanban`, and `packet` (`packet`, `packet-beta`), with the functions `Grid.block`, `Grid.architecture`, `Grid.kanban`, `Grid.packet`, and `Grid.layout`. [just proofs]
    The `block` packet MUST build this family module, because `block` is the family's first kind. The other grid kinds wait for it. Every packet gates on `just proofs` and `just lean-parity KIND=<kind>`.

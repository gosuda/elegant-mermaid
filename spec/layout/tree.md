# Tree layout family

This file defines the tree layout family: its entry points and inputs, the mindmap, treeview, and ishikawa rules, and its proofs.

## Entry and inputs

- tree-01: The Go entry points MUST be `func Mindmap(ctx context.Context, in TreeInput, p params.Params) (*scene.Scene, error)`, `func TreeView(ctx context.Context, in TreeInput, p params.Params) (*scene.Scene, error)`, and `func Ishikawa(ctx context.Context, in IshikawaInput, p params.Params) (*scene.Scene, error)` in package `internal/layout/tree`. [just parity]
    Rust: `layout::tree::{mindmap, treeview, ishikawa}`.
- tree-02: The kind adapter MUST pass these inputs to the family. [just go-check]
    `TreeInput{Nodes}`, where each node has `Parent` (index or none), `Children` (declaration order), `Lines`, and for treeview `Icon` and `Description` lines.
    `IshikawaInput` holds the head text and a list of causes, each with `Lines` and child causes (declaration order).
- tree-03: The family MUST receive items in declaration order, with integer indices, every label as measured `lines` with widths and heights in profile units, and no coordinates. [just lean-parity]
    A family never measures text. Its entry point also receives `params.Params` (package `internal/layout/params`; Rust `layout::params`), which holds the profile, the constants generated for that profile, `thoroughness`, `max_width`, and `limits`. Every tie-break uses declaration index as the last key. Divisions use `floor_div` unless a rule says otherwise, and `ceil_div(a, b)` is `floor_div(a + b - 1, b)` for `a >= 0` and `b > 0`. A vector value is in px and is stored as 1/64 px (px × 64). A cell value is in cells, and a vertical cell value is in rows.
- tree-04: Every named tree constant MUST be a key `<kind>.<name>` of `spec/data/layout-constants.json`, so a bare name `name` in one kind's rules means the key `<kind>.name` of that kind. [just gen-check]

## Mindmap

- tree-05: The mindmap constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`mindmap.padding`|10|640|1|
    |`mindmap.max_node_width`|200|12800|24|
    |`mindmap.sibling_gap`|20|1280|1 row|
    |`mindmap.level_gap`|40|2560|4|
    |`mindmap.label_wrap`|180|11520|22|
    |`mindmap.contour_cap`|2000|2000|2000|
    Config defaults `padding` 10 and `maxNodeWidth` 200 (`config.schema.yaml` lines 1228 to 1234).
- tree-06: The mindmap MUST use van der Ploeg's non-layered tidy tree (2014), with the contour rule of requirement tree-10 as the specification. [just lean-parity]
    Upstream `layoutAlgorithm` is `cose-bilkent` (line 1231); this plan does not port it. The paper's linear-time method is not copied (`cwi-swat/non-layered-tidy-trees` has no licence).
- tree-07: A mindmap node box MUST take `w = min(max_node_width, text_w + 2 * padding)` and `h = n * L1 + 2 * padding`. [just lean-parity]
    Text wraps at `mindmap.label_wrap`, which is `max_node_width - 2 * padding`: 180 px (11520 units) and 22 cells. A text narrower than that does not wrap. Cell: `w = min(max_node_width, text_w + 2)` and `h = n + 2`. `L1` is the `label` role line height of spec/text-measurement.md.
- tree-08: The root MUST sit at `(0, 0)`, child `i` of the root (0-based, declaration order) MUST go right iff `i` is even, and every deeper node MUST stay on the side of its root child. [just lean-parity]
- tree-09: A child's box left MUST be its parent's box right plus `level_gap` on the right side, and its box right MUST be its parent's box left minus `level_gap` on the left side. [just lean-parity]
    Levels are not shared columns.
- tree-10: Each mindmap subtree MUST have a contour of its boxes, and each later sibling `B` MUST be placed below the union contour `A` of the earlier siblings on its side by the rule `y_B = max over every box a of A and every box b of B whose x-ranges overlap of (a.bottom - b.top) + sibling_gap`. [just lean-parity]
    A contour holds, for each node, its box y-range over its widened x-range. Measure x outward from the root: on the right side `u = x`, on the left side `u = -x`. A box with inner edge `i` (the edge that faces its parent) and outer edge `o` has the widened x-range `[i - level_gap, o]` in `u`. On the right side this is `[x - level_gap, x + w]`. On the left side it is `[x, x + w + level_gap]`. Two boxes overlap in x when their widened x-ranges share positive length. The first child of a parent sits at relative `y = 0`. `b.top` and `a.bottom` are relative to the sibling roots, with `top = y_ref - floor_div(h, 2)` and `bottom = top + h`.
    The widened range includes the level gap between a box and its parent, because the trunk of a route runs there (requirement tree-45). A range that holds the box only would let a trunk cross a box of an earlier sibling.
- tree-11: The parent y MUST be `floor_div(y_first + y_last, 2)` over its children. [just lean-parity]
- tree-12: Each side's stack MUST be centred on the root, shifted by `-floor_div(y_first + y_last, 2)`. [just lean-parity]
- tree-13: The box top MUST be `y - floor_div(h, 2)`, and every division in mindmap MUST be `floor_div`. [just lean-parity]
    Implementations MUST compute the contour rule exactly. A faster method is conforming only when it returns the same integers on every tree in `tools/randgraph`.
- tree-45: A mindmap route MUST run from the outer edge of its parent box at the parent reference line, to the trunk, along the trunk to the child reference line, and to the inner edge of the child box. [just validate]
    The trunk lies at the outer edge of the parent plus `floor_div(level_gap, 2)` in the outward direction. On the right side the route points are `(x_p + w_p, y_p)`, `(x_p + w_p + floor_div(level_gap, 2), y_p)`, `(x_p + w_p + floor_div(level_gap, 2), y_c)`, and `(x_c, y_c)`. On the left side they are `(x_p, y_p)`, `(x_p - floor_div(level_gap, 2), y_p)`, `(x_p - floor_div(level_gap, 2), y_c)`, and `(x_c + w_c, y_c)`. When `y_p = y_c`, the route has the first and last point only. `y_p` and `y_c` are the reference lines `y_ref` of the parent and the child.
- tree-46: The mindmap adapter MUST name box `i` (declaration order) `n<i>`, and route `k` (declaration order of the child) `e<k>` from the parent box to the child box, with a plain end marker `none` and the line kind `normal`. [just parity]
    A label record `n<i>.label` exists only when the node text differs from the box id.

## Treeview

- tree-14: A treeview node at depth `d` MUST have `indent = d * (row_indent + padding_x)`, 15 px per level with the default values. [just lean-parity]
    The constants are keys of `spec/data/layout-constants.json`.
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`treeview.row_indent`|10|640|1|
    |`treeview.padding_x`|5|320|1|
    |`treeview.padding_y`|5|320|1 row|
    |`treeview.line_thickness`|1|64|1|
    |`treeview.icon_size`|14|896|1|
    |`treeview.icon_gap`|4|256|1|
    |`treeview.desc_gap`|16|1024|2|
    Config defaults `rowIndent` 10, `paddingX` 5, `paddingY` 5, `lineThickness` 1 (`config.schema.yaml` lines 2834 to 2873). Renderer constants: icon 14 px, icon gap 4 px, description gap 16 px (`treeView/renderer.ts` lines 17 to 19).
- tree-15: A treeview node's guide MUST be a horizontal stub from `indent - row_indent` to `indent` at the row's mid y, `line_thickness` wide. [just lean-parity]
    Its label x is `indent + padding_x` plus `icon_size + icon_gap` when an icon is shown. Upstream: `renderer.ts` lines 146 to 160.
- tree-16: A treeview row MUST have height `text_h + 2 * padding_y`. [just lean-parity]
- tree-17: In cell, each treeview level MUST be 4 cells, and the guide glyphs MUST follow these rules. [just lean-parity]
    A node at depth `d >= 1` writes its guide in columns `4(d-1)` to `4d - 1`: `├── ` when it is not the last child, `└── ` when it is. Each ancestor level writes `│   ` when that ancestor has a later sibling, else four spaces. The label starts at column `4d`.
- tree-18: Descriptions MUST align in one column, which is the largest label right edge plus `desc_gap` (vector) or 2 cells (cell). [just lean-parity]
    Description x is that column.

## Ishikawa

- tree-19: The ishikawa constants MUST have these values. [just gen-check]
    |Key|Vector (px)|Vector (units)|Cell|
    |---|---|---|---|
    |`ishikawa.spine_base_length`|250|16000|40|
    |`ishikawa.rib_min_length`|75|4800|12|
    |`ishikawa.rib_pool`|500|32000|80|
    |`ishikawa.cause_min_spacing`|28|1792|4|
    |`ishikawa.bone_stub`|30|1920|3|
    |`ishikawa.bone_base`|60|3840|6|
    |`ishikawa.bone_per_child`|5|320|1|
- tree-20: The three derived lengths MUST hold these relations to the constants. [just gen-check]
    `rib_min_length` is `0.3 * spine_base_length`. `rib_pool` is `2 * spine_base_length`. `cause_min_spacing` is `2 * font size 14`. Upstream: `ishikawa/ishikawaRenderer.ts`, `BONE_STUB`, `BONE_BASE`, `BONE_PER_CHILD`, lines 19 to 23.
- tree-21: Cause `0`, `2`, `4`, ... MUST go above (upper), causes `1`, `3`, ... MUST go below (lower), and upper causes MUST be first. [just lean-parity]
    Upstream: `ishikawa/ishikawaRenderer.ts` lines 59 to 151.
- tree-22: A rib MUST leave the spine at 82 degrees, with the integer slope `dx : dy = rib_cos_q15 : rib_sin_q15 = 4561 : 32455`, and `rib_angle_turns = 14928`. [just lean-parity]
    `rib_cos_q15` is `cos 82° × 32768` rounded and `rib_sin_q15` is `sin 82° × 32768` rounded. `rib_angle_turns` is `82 × 65536 / 360`, rounded. A rib of rise `len` has run `floor_div(len * 4561, 32455)`. The rib leans toward the spine's tail (left), so its far end is at `x_p - run`. The cell profile uses the same formula on rows. `x_0` is `-20 px` (cell `-2`).
- tree-23: The upper and lower rib lengths MUST be `upper_len = max(rib_min_length, floor_div(rib_pool * upper_total, total))` and `lower_len = max(rib_min_length, floor_div(rib_pool * lower_total, total))`. [just lean-parity]
    `total` counts all descendants on both sides. If `total = 0`, both lengths are `spine_base_length`. Then each length is raised to `max_depth_count * cause_min_spacing`. `spine_y = max(upper_len, spine_base_length)`. Upstream: lines 106 to 118.
- tree-24: Pair `p` MUST hold causes `2p` (upper) and `2p + 1` (lower), and pair `p` MUST attach at spine x `x_p`. [just lean-parity]
    The next attach point is the minimum left edge of pair `p`'s labels (`ishikawaRenderer.ts` lines 139 to 146).
- tree-25: A sub-rib MUST use the depth-dependent `depthBone` construction, with the head at depth 0, primary causes at depth 1, and their children at depth 2. [just lean-parity]
    Write a parent bone as `(par.x0, par.t0, par.x1, par.t1, par.count, par.drawn)`, where `t` is distance from the spine and `par.drawn` counts previously placed odd-depth children. At odd depth, `x0 = par.x0 + floor_div((par.x1 - par.x0) * (par.count - par.drawn), par.count + 1)`; the bone runs from `(x0, par.t0)` to `(x0 - floor_div((t - par.t0) * rib_cos_q15, rib_sin_q15), t)`, then increments `par.drawn`. At even depth, require `par.t1 > par.t0`, set `x0 = par.x0 + floor_div((par.x1 - par.x0) * (t - par.t0), par.t1 - par.t0)`, and run horizontally from `(x0, t)` to `(x0 - length, t)`. Screen y is `spine_y - t` above the spine and `spine_y + t` below it.
- tree-26: An even-depth horizontal sub-rib MUST have length `max(if c > 0 then bone_base + c * bone_per_child else bone_stub, (c + 1) * margin)`, where `c` is its child count and `margin = floor_div(max_descendant_height * rib_cos_q15, rib_sin_q15) + 3`. [just lean-parity]

## Integer rules for the proofs

- tree-27: The proof MUST take root children as alternating sides by declaration order, with child `i` right iff `i mod 2 = 0`, deeper nodes keeping the side of their root ancestor, and each side as a non-layered tidy tree. [just proofs]
    Sibling separation is `mindmap.sibling_gap` (vertical, between a box and the union contour of earlier siblings), the level gap is `mindmap.level_gap` (horizontal), and all values are integers rounded with `floor_div`.
- tree-28: The proof MUST take a subtree contour as the list of its boxes `(left, right, top, bottom)` relative to the subtree root, and the contour of earlier siblings as the list of their boxes. [just proofs]
    Two boxes overlap in x when their widened x-ranges of requirement tree-10 share a positive length.
- tree-29: The proof MUST take treeview rows as the pre-order list, with a child's x equal to its parent's x plus `treeview.row_indent + treeview.padding_x` and row height `text_h + 2 * treeview.padding_y`. [just proofs]
- tree-30: The proof MUST take the ishikawa spine as running left to right, cause `i` above the spine iff `i` is even, and sub-causes as the even-depth horizontal and odd-depth integer diagonal construction of requirements tree-25 and tree-26, not equal direction vectors between parents and children. [just proofs]

## Theorems

- tree-31: The proof `mindmap_contour_walk_fuel` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: the contour merge over the boxes of earlier siblings visits each box once.
    Proof approach: fuel-bounded loop; invariant: remaining fuel >= remaining boxes; the fuel is `mindmap.contour_cap`.
- tree-32: The proof `mindmap_siblings_separated` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: for siblings `i < j` on one side, every box of `j` lies at least `mindmap.sibling_gap` below every box of `i` whose widened x-range overlaps its own (requirement tree-10).
    Proof approach: induction on the child list; `y_j` is a `max` over the overlapping boxes of the earlier siblings; `omega`.
- tree-33: The proof `mindmap_parent_centred` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: `abs (2 * y parent - (y first + y last)) <= 1`.
    Proof approach: `Int.fdiv` identity; `omega`.
- tree-34: The proof `mindmap_child_order` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: siblings `i < j` on one side have `y i < y j`.
    Proof approach: induction on the child list; `mindmap.sibling_gap >= 1`.
- tree-35: The proof `mindmap_side_rule` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: child `i` of the root is on the right iff `i mod 2 = 0`; deeper nodes inherit their root ancestor's side.
    Proof approach: definitional unfolding; `Int.emod` by `decide` on the side table.
- tree-36: The proof `treeview_rows_preorder` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: the row index of each node equals its position in the pre-order list.
    Proof approach: induction on the tree.
- tree-37: The proof `treeview_indent_step` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: for each child `c` of `p`: `c.x = p.x + (treeview.row_indent + treeview.padding_x)`.
    Proof approach: definitional.
- tree-38: The proof `treeview_rows_disjoint` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: for rows `r < r'`: `row r .y + row r .h <= row r' .y`.
    Proof approach: induction on the pre-order list; `omega`.
- tree-39: The proof `ishikawa_causes_alternate` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: cause `i` is above the spine iff `i` is even.
    Proof approach: definitional unfolding.
- tree-40: The proof `ishikawa_ribs_ordered` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: on one side, causes `i < j` have `rib_x i < rib_x j`, and the rib intervals are pairwise disjoint.
    Proof approach: `compact_preserves_order` and `compact_pairwise_disjoint` over the rib slots.
- tree-41: The proof `ishikawa_subcause_parallel` MUST hold in `proofs/Elegant/Tree.lean`. [just proofs]
    Statement: for `depthBone`, even depth gives `(x0,t) -> (x0 - boneLength(p,count,margin),t)`; odd depth gives `(x0,par.t0) -> (x0 - floor_div((t - par.t0) * p.cos,p.sin),t)`; screen y is `spine - t` above and `spine + t` below. This does not assert parent-child equal vectors.
    Proof approach: unfold `depthBone`, `boneLength`, and `ordinate`; split on depth parity.
- tree-42: The proof `Elegant.Tree.tree_valid` MUST hold in `proofs/Elegant/FamilyValidity.lean`. [just proofs]
    Statement: `WellFormed m -> WithinLimits m -> m.kind ∈ ["mindmap", "treeview", "ishikawa"] -> Elegant.kindLayout m = some (.ok result) -> HardConstraints result.scene.layoutDump`.
    Proof approach: dispatch on the family membership and apply the public kind validity proofs, which combine the geometry rows above.
- tree-43: The mindmap contour merge MUST recurse on the fuel `mindmap.contour_cap` (`spec/data/layout-constants.json`, value 2000, equal to the node limit, which bounds the depth). [just proofs]
    The treeview and ishikawa phases have no loop: they recurse structurally on the tree.
- tree-44: The per-kind geometry reference module MUST remain `proofs/Elegant/Tree.lean`, serving the kinds `mindmap`, `treeview` (header `treeView-beta`), and `ishikawa` (`ishikawa`, `ishikawa-beta`). Unified model-stage dispatch MUST use `Elegant.kindLayout` in `proofs/Elegant/KindLayout.lean`; family validity MUST use `Elegant.Tree.tree_valid` in `proofs/Elegant/FamilyValidity.lean` over the explicit family domain in tree-42. [just proofs]
    The `mindmap` packet MUST build this family module, because `mindmap` is the family's first kind. The other tree kinds wait for it. Every packet gates on `just proofs` and `just lean-parity KIND=<kind>`.

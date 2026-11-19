# Railroad layout family

This file defines the railroad family: its model, its box rules, its rule and diagram layout, its four syntaxes, and its proofs.

## Entry and model

- railroad-01: The Go entry point MUST be `func Layout(rules []Rule, p Params) (scene.Scene, error)` in package `internal/layout/railroad`, which builds the scene from its own tree and takes text measurement, constants, and dump options through `Params`. [just build]
    The glue `FromRailroad` and `layoutRailroad` in package `internal/layout` converts the model to the dump encoding of railroad-32 and rebuilds the family tree from the `Input` boxes. Rust: `pub fn layout(rules: &[Rule], params: &Params) -> Result<Scene, LayoutError>` in `layout::railroad::family`, and `layout::railroad::layout(input)` for the glue.
- railroad-02: The model MUST hand the glue `Title`, `AccTitle`, `AccDescr`, and `Rules` in declaration order, each `Rule{Name string, Index int, Definition Node, Span}`; the title is kept and not drawn. [just lean-parity]
- railroad-03: `Node` MUST be one of these seven types. [just lean-parity]
    - `Terminal{Value}`, `NonTerminal{Name}`, `Special{Text}`;
    - `Sequence{Elements}`, with at least 2 elements;
    - `Choice{Alternatives}`, with at least 2 alternatives;
    - `Optional{Element}`;
    - `Repetition{Element, Min, Max}`, with `Max = -1` for unbounded.
- railroad-04: The model MUST hold no coordinates, and the family MUST measure text with `measure` before it computes the boxes. [just lean-parity]
- railroad-05: The box model MUST follow upstream `railroadRenderer.ts`, which returns `DiagramDimensions{width, height, up, down}` (`railroadTypes.ts:113-123`) from each composition method: `renderSequence`, `renderChoice`, `renderOptional`, `renderRepetition`, `renderSpecial`, `renderTerminal`, `renderNonTerminal`, and `renderRule`. [just lean-parity]
    The published tabatkins/railroad-diagrams source is not in this checkout; it was read for this revision from `railroad.js` on the gh-pages branch. Only the `Choice` centring rule below depends on it. The port's own rules are in this file.

## Constants

- railroad-06: Every railroad constant MUST be a key of `spec/data/layout-constants.json`, with the value in units for the vector profile and in cells or dots for the cell profile. [just gen-check]
    An upstream value in px is multiplied by 64. These are the keys and values:
    - `railroad.pad_x`: 640 / 1.
    - `railroad.pad_y`: 640 / 1. These two are upstream `padding` (10 px).
    - `railroad.line_height`: 1280 / 1. This is the body line height of 20 px from `spec/text-measurement.md`.
    - `railroad.hsep`: 640 / 2. This is upstream `horizontalSeparation` (10 px).
    - `railroad.vsep`: 512 / 1. This is upstream `verticalSeparation` (8 px).
    - `railroad.arc_radius`: 640 / 1. This is upstream `arcRadius` (10 px). The value `r` in this file means this key.
    - `railroad.terminal_radius`: 640 / 0. This is the corner radius of a terminal (`rx` 10 px, read `renderTerminal`). In cells, the corners are box-drawing glyphs.
    - `railroad.marker_radius`: 320 / 1. This is upstream `markerRadius` (5 px).
    - `railroad.margin`: 640 / 1.
    - `railroad.rule_name_gap`: 1280 / 2. This is the 20 px gap used twice in `renderRule`.
    - `railroad.rule_end_gap`: 640 / 2. This is the 10 px end gap.
    - `railroad.rule_min_baseline`: 1280 / 2. This is the 20 px lower bound of the baseline.
    - `railroad.rule_min_height`: 2560 / 3. This is the 40 px minimum rule height.
    - `railroad.empty_width`: 12800 / 20, and `railroad.empty_height`: 6400 / 5. These are the 200 by 100 px canvas for zero rules.

## Text width

- railroad-07: The vector profile MUST take a text width from `spec/text-measurement.md`: the sum of advances, rounded up per string. The cell profile MUST take the sum of cell widths. [just lean-parity]
    Upstream measures with the DOM (`getBBox`, `railroadRenderer.ts:74-90`). This family does not, because the core never reads host fonts.

## Boxes

- railroad-08: Every node MUST hold `Width`, `Up`, and `Down` as `int64` units, all at least 0, with `Height = Up + Down`. [just lean-parity]
- railroad-09: A `Terminal(v)`, `NonTerminal(n)`, or `Special(t)` node MUST size by these rules. [just lean-parity]
    For `Special`, the text is `"? " + t + " ?"`. Then `Width = textW(text) + 2 * pad_x`, `Height = line_height + 2 * pad_y`, `Up = floor_div(Height, 2)`, and `Down = Height - Up`. A terminal is a rounded rectangle, a non-terminal is a plain rectangle, and a special node is a dashed rectangle (read `renderSpecial`).
- railroad-10: A `Sequence(e_1..e_n)` node MUST size and place by these rules. [just lean-parity]
    `Width = sum of W_i + (n - 1) * hsep`. `Up = max Up_i` and `Down = max Down_i`. Child `i` sits at `y = Up - Up_i`. A line joins child `i` to child `i + 1` at `y = Up`, across `hsep` (read `renderSequence`).
- railroad-11: A `Choice(a_1..a_n)` node MUST size by these rules, with `maxW = max W_i` and `H_total = sum of H_i + (n - 1) * vsep`. [just lean-parity]
    `Width = maxW + 4r`, `cy = floor_div(H_total, 2)`, `Up = cy`, and `Down = H_total - cy`.
- railroad-12: Alternative `i` of a `Choice` MUST sit at `x = 2r + floor_div(maxW - W_i, 2)` and `y = sum over j < i of (H_j + vsep)`, with its centre row at `y + Up_i`, and arcs of radius `r` MUST join that row to the centre line at `cy`. [just lean-parity]
    The port centres on the total height (read `renderChoice`). Tabatkins centres on the item at index `normal`, which the caller passes; the constructor has no default (`railroad.js`, `class Choice`), and the through-line is the normal item's height (`this.height = normalItem.height`). `Optional` passes `1`, so the child is on the through-line and the bypass sits above it.
- railroad-13: An `Optional(e)` node MUST size by these rules. [just lean-parity]
    `Width = W_e + 4r` and `Height = H_e + 2r`. The child sits at `(2r, 2r)`. The line is at `cy = 2r + Up_e`, with `Up = cy` and `Down = Height - cy`. The bypass sits above the child (read `renderOptional`).
- railroad-14: A `Repetition(e, min, max)` node MUST size by these rules. [just lean-parity]
    The bypass sits above the child only when `min = 0`. `Width = W_e + 4r`. `Height = H_e + 2r + (min = 0 ? 2r : 0)`. The child sits at `(2r, bypass ? 2r : 0)`. The centre row is `cy = child_y + Up_e`, with `Up = cy` and `Down = Height - cy`. The loop returns below the child, from its right end to its left end, at `child_y + H_e + r` (read `renderRepetition`).
- railroad-15: `ZeroOrMore` MUST be a repetition with `min = 0`, and `OneOrMore` MUST be a repetition with `min >= 1`. [just lean-parity]
- railroad-16: `max` MUST NOT be drawn, and a finite `Max` MUST emit `railroad/repeat-max-ignored` (info). [just lean-parity]

## Rule layout

- railroad-17: A rule MUST lay out by these rules, read from `renderRule`. [just lean-parity]
    `nameW = textW(Title) + railroad.rule_name_gap`, where `Title` is `Name + " ="`, and `defX = nameW + railroad.rule_name_gap`. The baseline is `baseline = max(railroad.rule_min_baseline, Up_def)`. The definition group sits at `y = baseline - Up_def`. Rule height is `max(railroad.rule_min_height, (baseline - Up_def) + H_def + 2 * railroad.margin)`. Rule width is `defX + W_def + railroad.rule_end_gap + marker`. The rule content starts at `x = railroad.margin`, and the rule box is the frame of railroad-33.
- railroad-18: The start and end markers MUST be circles of radius `railroad.marker_radius`, written `marker` in this file. [just lean-parity]
    The start marker is a circle at `(nameW, baseline)`, and a line joins `(nameW + marker, baseline)` to `(defX, baseline)`. The end marker is a circle at `(defX + W_def + railroad.rule_end_gap, baseline)`, and a line joins `(defX + W_def, baseline)` to `(defX + W_def + railroad.rule_end_gap - marker, baseline)`.

## Diagram layout

- railroad-19: Rules MUST stack top to bottom in declaration order, with the first rule starting at `y = railroad.margin` and each rule advancing `y` by its height plus `railroad.vsep`. [just lean-parity]
    Read `renderDiagram`.
- railroad-20: The canvas width MUST be the widest rule plus `2 * railroad.margin`, and the canvas height MUST be the final `y` plus `railroad.margin`. [just lean-parity]
- railroad-21: Zero rules MUST give a canvas of `railroad.empty_width` by `railroad.empty_height` and MUST emit `railroad/no-rules` (warning). [just lean-parity]
    Upstream warns the same way (`draw`).

## Dump encoding and scene

- railroad-32: The glue MUST encode the model as follows, so that the model-stage dump alone fixes the layout. [just lean-parity]
    Rule `i` (0-based) is a box `r{i}` with role `group`, shape `rule`, no parent, and a label record `r{i}.label` whose text is `Name =`. The definition tree follows in preorder: node `j` (root 0) is a box `r{i}.{j}`. A leaf has role `node`, `exclusive` true, shape `terminal`, `nonterminal`, or `special`, and a label record `<id>.label` whose text is the displayed text. A composite has role `group`, `exclusive` false, shape `sequence`, `choice`, `optional`, `zeroOrMore`, or `oneOrMore`, and its container as parent (the rule box for the root). The only routes are the sequence joins: for each sequence node in preorder, route `e{k}` runs from child `i` to child `i + 1`, with `k` counting from 0 over the document; every other rail is drawn by the scene only.
    Displayed text replaces each TAB, LF, and CR with a space and each other C0 or C1 control character with U+FFFD. A special node shows `"? " + text + " ?"`. A leaf label is never wrapped and never read as Markdown.
- railroad-33: A rule box MUST be the padded frame `x = 0`, `y = y_i`, `w = ruleW + 2 * railroad.margin`, `h = ruleH`, where the rule content starts at `x = railroad.margin`, so its title label lies strictly inside it as clause `frame-clearance` requires. [just validate]
    The title label of rule `i` is the only label record of the layout-stage dump. Its rect is `(margin, y_i + baseline - floor_div(railroad.line_height, 2), textW(Title), railroad.line_height)` and its `lines` is `[Title]`. Leaf label records are not part of the layout-stage dump, because their boxes are exclusive.
- railroad-34: A sequence join MUST be the route `[(x_i + W_i, y_s + Up), (x_(i+1), y_s + Up)]`, orthogonal, where `y_s` is the top of the sequence box, and its edge group MUST hold one `Polyline` in style `edge` through the same points. [just lean-parity]
- railroad-35: The scene MUST hold these groups in this order: one `group` group per rule box and composite box in dump order, one `edge` group per join, one `node` group per leaf in dump order. [just lean-parity]
    A leaf group holds the outline and then one `Text` (role `label`, size 14, align `middle`, style `text`, rect `(x, y + floor_div(h - line_height, 2), w, line_height)`). The outline is a `RoundRect` of radius `railroad.terminal_radius` for a terminal, a `Rect` for a non-terminal, and a dashed `Rect` for a special node, all in style `node`. A rule group holds, in order: the left rule rail, the right rule rail, the start marker, the end marker, and the title `Text` (align `start`). A marker is an `Ellipse` of radius `railroad.marker_radius` in style `ink`. A composite group holds its rails, in the order of railroad-36, and nothing else, so no frame is drawn for a composite.
- railroad-36: Rails MUST be these polylines in the local coordinates of the composite box (origin at its top left, `r = railroad.arc_radius`, `W` its width, `cy` its `Up`), drawn in style `edge`. [just lean-parity]
    Choice, for each alternative `i` with box `(x_i, y_i, W_i, H_i)` and `ecy = y_i + Up_i`: the left rail `[(0, cy), (x_i, ecy)]` joined through `(r, cy), (r, ecy)` when `ecy != cy`, and the right rail `[(x_i + W_i, ecy), (W, cy)]` joined through `(W - r, ecy), (W - r, cy)` when `ecy != cy`; the left rail of alternative `i` comes before its right rail, alternatives in order. Optional, zero-or-more, and one-or-more with child box `(2r, y_c, W_e, H_e)`: the forward rails `[(0, cy), (2r, cy)]` and `[(2r + W_e, cy), (W, cy)]`; then for one-or-more and zero-or-more the loop `[(2r + W_e, cy), (3r + W_e, cy), (3r + W_e, B), (r, B), (r, cy), (2r, cy)]` with `B = H`; then for optional and zero-or-more the bypass `[(0, cy), (r, cy), (r, 0), (W - r, 0), (W - r, cy), (W, cy)]`. Rule rails: `[(nameW + marker, baseline), (defX, baseline)]` and `[(defX + W_def, baseline), (defX + W_def + rule_end_gap - marker, baseline)]`, translated to the rule content origin.
- railroad-37: The cell profile MUST draw each rail as one `Polyline`, with these two changes: a rail that starts at the right boundary of a leaf starts one cell to the left, on the border cell of the leaf, and the loop uses `B = H - 1`. [just lean-parity]
    The change keeps every rail on a painted cell inside the box it belongs to. A rail that starts at the right boundary of a composite keeps its start.
- railroad-38: The vector profile MUST draw each rail as one `Path` with rounded corners. [just parity]
    For an interior corner `P` with incoming unit direction `u1`, outgoing unit direction `u2`, incoming leg length `a`, and outgoing leg length `b`, the radius is `min(r, a', b')`, with `a' = a` when the incoming leg is the first leg of the rail and `floor_div(a, 2)` otherwise, and `b' = b` when the outgoing leg is the last leg and `floor_div(b, 2)` otherwise. Consecutive equal points are removed first. A radius of 0 gives a sharp corner `L P`. Otherwise the path goes `L S` with `S = P - radius * u1`, then `A` with centre `S + radius * u2`, radius `radius`, start angle the angle of `-u2`, and sweep `+16384` when `u1.x * u2.y - u1.y * u2.x > 0` and `-16384` otherwise. The angles of `+x`, `+y`, `-x`, and `-y` are 0, 16384, 32768, and 49152.
- railroad-39: A top-level box that is not a rule MUST be laid out as a rule without a name: no rule box, no title label, no markers, and no rail, and its tree is the box with its descendants. [just go-check]
    A composite whose child count is outside its arity (sequence and choice 2 or more, optional and repetition exactly 1, leaf 0), a rule box with other than one child, a rule with no definition, and a box reached twice are errors: `ErrArity` in Go and `LayoutError::Domain` in Rust. A size outside int32 is `ErrOverflow`. The nodes, edges, and text bytes limits apply to the boxes, routes, and texts of the input.

## The four syntaxes

- railroad-22: Each of the four syntaxes MUST have a detector that matches its header case-insensitively: `^\s*railroad-beta` (`railroadDetector.ts`), `railroad-ebnf-beta` (`ebnfDetector.ts`), `railroad-abnf-beta` (`abnfDetector.ts`), and `railroad-peg-beta` (`pegDetector.ts`). [just parity]
- railroad-23: Each parser under `parser/` MUST import `db` from `railroadDb.ts` and call `db.addRule`, so one renderer draws all four syntaxes. [just lean-parity]
- railroad-24: Each construct MUST lower to the model node of this table, by its cell. [just lean-parity]
    Each cell names the parser node and the model node.
    |Construct|`railroad-beta` (`parser/railroadParser.ts`)|`railroad-ebnf-beta` (`parser/ebnfParser.ts`)|`railroad-abnf-beta` (`parser/abnfParser.ts`)|`railroad-peg-beta` (`parser/pegParser.ts`)|
    |---|---|---|---|---|
    |Literal|`RailroadTerminalExpr` gives `Terminal`|`EbnfTerminal` gives `Terminal`|`AbnfStringLiteral` and `AbnfNumVal` give `Terminal`|`PegLiteral` gives `Terminal`|
    |Rule reference|`RailroadNonTerminalExpr` gives `NonTerminal`|`EbnfNonTerminal` gives `NonTerminal`|`AbnfRuleName` gives `NonTerminal`|`PegIdentifier` gives `NonTerminal`|
    |Special|`RailroadSpecialExpr` gives `Special`|`EbnfSpecial` gives `Special`|none|`PegAny` (`.`) gives `Special(".")`|
    |Sequence|`RailroadSequenceExpr` gives `Sequence`; one element collapses|juxtaposed terms give `Sequence` (`EbnfSequence`)|`AbnfConcatenation` gives `Sequence`|`PegSequence` gives `Sequence`|
    |Choice|`RailroadChoiceExpr` gives `Choice`|`EbnfChoice` gives `Choice`|`AbnfAlternation` gives `Choice`|`PegOrderedChoice` gives `Choice`|
    |Group|none|`EbnfGroup` is inlined as its choice|`AbnfGroup` is inlined as its alternation|`PegGroup` is inlined as its ordered choice|
    |Optional|`RailroadOptionalExpr` gives `Optional`|`[ ... ]` (`EbnfOptional`) and the `?` postfix give `Optional`|`AbnfOptionalGroup` gives `Optional`; `0*1` gives `Optional`|the `?` suffix gives `Optional`|
    |Zero or more|`RailroadZeroOrMoreExpr` gives `Repetition(0, unbounded)`|`{ ... }` (`EbnfRepetition`) and the `*` postfix give `Repetition(0, unbounded)`|`*` and `0*` give `Repetition(0, unbounded)`|the `*` suffix gives `Repetition(0, unbounded)`|
    |One or more|`RailroadOneOrMoreExpr` gives `Repetition(1, unbounded)`|the `+` postfix gives `Repetition(1, unbounded)`|`1*` gives `Repetition(1, unbounded)`; `n*m` gives `Repetition(n, m)`|the `+` suffix gives `Repetition(1, unbounded)`|
    |Exact count|none|none|`n` gives `Repetition(n, n)`|none|
    |Exception|none|the `-` postfix gives `Sequence(node, Terminal("-"), except)`|none|none|
    |Lookahead|none|none|none|`&e` gives `Special("&" + label(e))`; `!e` gives `Special("!" + label(e))`|
- railroad-25: ABNF `n*m` MUST take `min = n` when `n` is absent, which is 0, and `max = m` when `m` is absent, which is unbounded, and the renderer MUST draw `n >= 1` as `OneOrMore` and `n = 0` as `ZeroOrMore`. [just lean-parity]
    Read `parseRepeat`. An exact count `n` gives `min = max = n`. This is upstream behaviour.
- railroad-26: PEG `label(e)` MUST be `"v"` for a terminal (with quotes), the name for a non-terminal, the text for a special node, and `(...)` for any other node. [just lean-parity]
    Read `nodeToLabel`.
- railroad-27: A group MUST NOT become a node. [just lean-parity]
    It is inlined by the rule of its syntax in the lowering table.

## Proofs

- railroad-28: The Lean entry points MUST be `Kinds.Railroad.lower` (valid frontend-produced normalized models to a rule forest of `Node` values), `Railroad.box : Node -> Box`, and `Railroad.layout`. The model adapter MUST reside in `proofs/Elegant/Kinds/Railroad.lean`; geometry MUST reside in `proofs/Elegant/Railroad.lean`. The native frontends MUST retain checks for all four grammars. [just proofs]
- railroad-29: The railroad box proofs MUST hold over these rules: an upstream port that uses `height / 2` for `up` and `down` becomes the integer port `up = Int.fdiv height 2` and `down = height - up`, so `up + down = height`; each syntax is lowered once to `Node`; and each sequence child's centre line is at `y = maxUp`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`railroad_box_nonneg`|every node has `width >= 0`, `up >= 0`, and `down >= 0`|induction on the node tree; `Int.max` nonnegativity|
    |`railroad_box_height_split`|for every node, `up + down = height`|definitional unfolding per constructor; `omega`|
    |`railroad_sequence_inside`|each child box of a sequence satisfies `0 <= maxUp - up_i`, `maxUp - up_i + height_i <= maxUp + maxDown`, and `x_i + width_i <= width`|`le_max` bounds; `omega`|
    |`railroad_choice_inside`|each alternative lies horizontally inside the choice box: `2r <= x_i` and `x_i + width_i <= width - 2r` where `r` is `railroad.arc_radius` and `x_i = 2r + Int.fdiv (maxW - width_i) 2`|`omega` on the floor bounds|
    |`railroad_rail_join`|for consecutive children `i` and `i+1` of a sequence, the exit point `(x_i + width_i, maxUp)` and the entry point `(x_(i+1), maxUp)` lie on one horizontal line, and their distance is `railroad.hsep`|induction on the child list; `omega`|
    |`railroad_lower_total`|lowering every valid frontend-produced normalized model succeeds with a rule forest of `Node` values|structural induction on the encoder's finite reverse-preorder rank; shape, arity, role, and root constraints define the input predicate independently of lowering success|
    |`railroad_valid`|`WellFormed m -> WithinLimits m -> Railroad.layout m = .ok s -> HardConstraints s`|combines the rows above; the rails are the joins of `railroad_rail_join`|
- railroad-30: The railroad family MUST have no fuel loop: the box computation MUST recurse structurally on the node tree, whose depth the nesting limit bounds. [just proofs]

## Gate

- railroad-31: The `railroad` packet MUST pass `just proofs`, `just oracle KIND=railroad`, `just parity KIND=railroad`, `just validate KIND=railroad`, and `just lean-parity KIND=railroad`. [just lean-parity]

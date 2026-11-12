# Railroad layout family

This file defines the railroad family: its model, its box rules, its rule and diagram layout, its four syntaxes, and its proofs.

## Entry and model

- railroad-01: The Go entry point MUST be `func Layout(ctx context.Context, m *model.Railroad, o layout.Options) (*scene.Scene, error)` in package `internal/layout/railroad`. [just build]
    Rust: `pub fn layout(m: &model::Railroad, o: &layout::Options) -> Result<scene::Scene, LayoutError>` in module `layout::railroad`.
- railroad-02: The model MUST hand the family `Title`, `Rules []Rule` in declaration order, and each `Rule{Name string, Index int, Definition Node}`. [just lean-parity]
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
    `nameW = textW(Name + " =") + railroad.rule_name_gap`, and `defX = nameW + railroad.rule_name_gap`. The baseline is `baseline = max(railroad.rule_min_baseline, Up_def)`. The definition group sits at `y = baseline - Up_def`. Rule height is `max(railroad.rule_min_height, (baseline - Up_def) + H_def + 2 * railroad.margin)`. Rule width is `defX + W_def + railroad.rule_end_gap + marker`.
- railroad-18: The start and end markers MUST be circles of radius `railroad.marker_radius`, written `marker` in this file. [just lean-parity]
    The start marker is a circle at `(nameW, baseline)`, and a line joins `(nameW + marker, baseline)` to `(defX, baseline)`. The end marker is a circle at `(defX + W_def + railroad.rule_end_gap, baseline)`, and a line joins `(defX + W_def, baseline)` to `(defX + W_def + railroad.rule_end_gap - marker, baseline)`.

## Diagram layout

- railroad-19: Rules MUST stack top to bottom in declaration order, with the first rule starting at `y = railroad.margin` and each rule advancing `y` by its height plus `railroad.vsep`. [just lean-parity]
    Read `renderDiagram`.
- railroad-20: The canvas width MUST be the widest rule plus `2 * railroad.margin`, and the canvas height MUST be the final `y` plus `railroad.margin`. [just lean-parity]
- railroad-21: Zero rules MUST give a canvas of `railroad.empty_width` by `railroad.empty_height` and MUST emit `railroad/no-rules` (warning). [just lean-parity]
    Upstream warns the same way (`draw`).

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

- railroad-28: The Lean entry points MUST be `Railroad.lower` (the four syntaxes to one `Node` type), `Railroad.box : Node -> Box`, and `Railroad.layout`, in module `proofs/Elegant/Railroad.lean`. [just proofs]
- railroad-29: The railroad box proofs MUST hold over these rules: an upstream port that uses `height / 2` for `up` and `down` becomes the integer port `up = Int.fdiv height 2` and `down = height - up`, so `up + down = height`; each syntax is lowered once to `Node`; and each sequence child's centre line is at `y = maxUp`. [just proofs]
    |Theorem|Statement|Proof approach|
    |---|---|---|
    |`railroad_box_nonneg`|every node has `width >= 0`, `up >= 0`, and `down >= 0`|induction on the node tree; `Int.max` nonnegativity|
    |`railroad_box_height_split`|for every node, `up + down = height`|definitional unfolding per constructor; `omega`|
    |`railroad_sequence_inside`|each child box of a sequence satisfies `0 <= maxUp - up_i`, `maxUp - up_i + height_i <= maxUp + maxDown`, and `x_i + width_i <= width`|`le_max` bounds; `omega`|
    |`railroad_choice_inside`|each alternative lies horizontally inside the choice box: `2r <= x_i` and `x_i + width_i <= width - 2r` where `r` is `railroad.arc_radius` and `x_i = 2r + Int.fdiv (maxW - width_i) 2`|`omega` on the floor bounds|
    |`railroad_rail_join`|for consecutive children `i` and `i+1` of a sequence, the exit point `(x_i + width_i, maxUp)` and the entry point `(x_(i+1), maxUp)` lie on one horizontal line, and their distance is `railroad.hsep`|induction on the child list; `omega`|
    |`railroad_lower_total`|lowering each of the four syntaxes is a total function to `Node`|structural recursion on each grammar AST; exhaustive matching checked by Lean|
    |`railroad_valid`|`WellFormed m -> WithinLimits m -> Railroad.layout m = .ok s -> HardConstraints s`|combines the rows above; the rails are the joins of `railroad_rail_join`|
- railroad-30: The railroad family MUST have no fuel loop: the box computation MUST recurse structurally on the node tree, whose depth the nesting limit bounds. [just proofs]

## Gate

- railroad-31: The `railroad` packet MUST pass `just proofs`, `just oracle KIND=railroad`, `just parity KIND=railroad`, `just validate KIND=railroad`, and `just lean-parity KIND=railroad`. [just lean-parity]

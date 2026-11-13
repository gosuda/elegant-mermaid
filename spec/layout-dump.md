# Canonical layout dump and validator

This file fixes the bytes, key order, and content of the canonical layout dump, and the validator that checks a dump against the hard constraints.

## Encoding

- layout-dump-01: The dump MUST be UTF-8 JSON with no byte-order mark, with no space or tab outside strings, and with one LF after the final `}`. [just parity]
- layout-dump-02: `version` MUST be 1, `stage` MUST be `layout`, and `kind` MUST be the kind id. [just parity]
- layout-dump-03: `canvas` MUST be in units: 1/64 px for the `vector` profile and cells for the `cell` profile. [just parity]
- layout-dump-04: The layout MUST translate the scene so that every `x` and `y` is at least 0, and no conforming dump MUST hold a negative value. [just validate]
- layout-dump-05: Integers MUST be written as an optional `-`, then digits with no leading zero; zero MUST be `0`, and no `+`, fraction, or exponent MUST appear. [just parity]
- layout-dump-06: A string MUST escape `"` as `\"` and `\` as `\\`. [just parity]
- layout-dump-07: A string MUST write U+0008, U+0009, U+000A, U+000C, and U+000D as `\b`, `\t`, `\n`, `\f`, and `\r`. [just parity]
- layout-dump-08: A string MUST write every other U+0000 to U+001F as `\u` followed by four lowercase hex digits, and it MUST write all other scalars, including `/`, U+007F, and non-ASCII, as UTF-8. [just parity]
- layout-dump-09: `true` and `false` MUST be lowercase, and an empty array MUST be `[]`. [just parity]
- layout-dump-10: An array nested in a member, which is `points` or `lines`, MUST stay on one line, and a point MUST be `[x,y]`. [just parity]
- layout-dump-11: The top-level members `boxes`, `routes`, and `labels` MUST each start a new line, the comma before them MUST end the previous line, each element after the first of those three arrays MUST start a new line, and no other newline MUST occur. [just parity]
- layout-dump-12: Every array MUST keep the order of the model stage, which is source declaration order. [just parity]

## Key order

- layout-dump-13: The top-level keys MUST appear in this order: `version`, `stage`, `kind`, `profile`, `options`, `canvas`, `boxes`, `routes`, `labels`. [just parity]
- layout-dump-14: The `options` keys MUST appear in this order: `profile`, `thoroughness`, `max_width`, `direction`, `limits`, then every honoured config key that affects layout in ascending byte order of the key name. [just parity]
- layout-dump-15: The `limits` keys MUST appear in this order: `max_nodes`, `max_edges`, `max_text_bytes`. [just parity]
- layout-dump-16: The `canvas` keys MUST appear in this order: `w`, `h`. [just parity]
- layout-dump-17: The box keys MUST appear in this order: `id`, `role`, `x`, `y`, `w`, `h`, `parent`, `exclusive`. [just parity]
- layout-dump-18: The route keys MUST appear in this order: `id`, `from`, `to`, `orthogonal`, `points`. [just parity]
- layout-dump-19: The label keys MUST appear in this order: `id`, `owner`, `text`, `x`, `y`, `w`, `h`, `lines`. [just parity]
- layout-dump-20: `parent` MUST be `""` for a box with no parent, and `role` MUST be a value of `spec/scene.md`. [just parity]
- layout-dump-21: The `options` defaults MUST be `thoroughness` 3, `max_width` 0 (natural width), and `limits` 2000, 5000, and 1048576. [just parity]
- layout-dump-22: `direction` MUST be the resolved layout direction, `TB`, `BT`, `LR`, or `RL`; a `TD` header MUST be written as `TB`, and a kind with no direction MUST write `TB`. [just parity]

## Shape

- layout-dump-23: A dump MUST have this shape, with one LF at the end of the last line. [just parity]

    ```
    {"version":1,"stage":"layout","kind":"flowchart","profile":"vector","options":{...},"canvas":{"w":..,"h":..},
    "boxes":[{"id":"A","role":"node","x":..,"y":..,"w":..,"h":..,"parent":"","exclusive":true}],
    "routes":[{"id":"e0","from":"A","to":"B","orthogonal":true,"points":[[x,y],..]}],
    "labels":[{"id":"e0.label","owner":"e0","text":"yes","x":..,"y":..,"w":..,"h":..,"lines":["yes"]}]}
    ```

- layout-dump-24: The model stage MUST fix `id`, `role`, `parent`, `exclusive`, `from`, `to`, `orthogonal`, `owner`, and `text`, and it MUST write `lines` as `[]`; the model stage authors the relation section, which is the exclusive boxes, the containment tree, and the edge endpoints, before layout runs, so the validator checks coordinates against relations that layout did not write. [just parity]
- layout-dump-25: Measurement MUST fill `lines`, and layout MUST fill `canvas`, `x`, `y`, `w`, `h`, and `points`. [just parity]
- layout-dump-26: The layout-stage golden of the two-node input MUST be `spec/golden/two-node.layout.json`, and Go, Rust, and Lean MUST reproduce it byte for byte. [just lean-parity]

## Validator input

- layout-dump-27: `ElegantGeometry/Validator.lean` MUST read the dump through the structures of this block. [just proofs]

    ```
    structure Box   where id : String; role : String; rect : Rect; parent : String; exclusive : Bool
    structure Route where id : String; fromId : String; toId : String; orthogonal : Bool; points : List Point
    structure Label where id : String; owner : String; rect : Rect; lines : List String
    structure LayoutDump where canvas : Size; boxes : List Box; routes : List Route; labels : List Label
    ```

- layout-dump-28: `parent` MUST be `""` for no parent, the JSON keys `from` and `to` MUST be read as `fromId` and `toId`, and the JSON keys `version`, `kind`, `profile`, and the `lines` text MUST NOT be validated. [just proofs]

## Well-formed input

- layout-dump-29: `WellFormed d` MUST be checked by the reader before validation, and a dump that fails it MUST make `geomcheck validate` exit 2 with `malformed dump: REASON`. [just validate]
- layout-dump-30: Box, route, and label ids MUST be unique within their kind, `fromId` and `toId` MUST name boxes, and a label `owner` MUST name a route or a box. [just validate]
- layout-dump-31: Each `parent` MUST be `""` or a box id, and the parent chain MUST have no cycle. [just validate]
- layout-dump-32: Every Rect MUST be valid, every width and height MUST be at least 0, every coordinate and point MUST be within `+/-COORD_LIMIT`, and every rect edge `x + w` and `y + h` MUST be within `+/-COORD_LIMIT`. [just validate]
- layout-dump-33: Under `WellFormed`, `intersects`, `contains`, `Polyline.hitsRect`, and `Polyline.isOrthogonal` MUST never return an error. [just validate]

## Ancestors and scope

- layout-dump-34: `anc(id)` MUST be the list of proper ancestors of a box, found by following `parent`. [just validate]
- layout-dump-35: For a route `r`, `Scope(r)` MUST be `{r.fromId, r.toId}` union `anc(r.fromId)` union `anc(r.toId)`. [just validate]
- layout-dump-36: For a label `l`, `OwnerAnc(l)` MUST be `anc(r.fromId)` union `anc(r.toId)` when `owner` names a route `r`, and `anc(owner)` when `owner` names a box. [just validate]
- layout-dump-37: Every exclusive box MUST be a box with `exclusive` `true`. [just validate]

## Clauses

- layout-dump-38: The eight clauses MUST run in this fixed order, and each MUST have its fixed message. [just validate]
    The order is `canvas`, `exclusive-siblings`, `parent`, `orthogonal`, `ports`, `route-clearance`, `label-clearance`, `frame-clearance`.
- layout-dump-39: Clause `canvas` MUST hold when every box rect is contained in `(0, 0, canvas.w, canvas.h)`, and its message MUST be `box outside canvas`. [just validate]
- layout-dump-40: Clause `exclusive-siblings` MUST hold when distinct boxes `b` and `c` with `exclusive` `true` and equal `parent` satisfy `Disjoint(b.rect, c.rect)`, and its message MUST be `exclusive sibling boxes overlap`. [just validate]
- layout-dump-41: Clause `parent` MUST hold when every box with `parent != ""` has its rect contained in the rect of that parent, and its message MUST be `box outside its parent`. [just validate]
- layout-dump-42: Clause `orthogonal` MUST hold when every route with `orthogonal` `true` satisfies `Polyline.isOrthogonal(points)`, and its message MUST be `orthogonal route has a diagonal segment`. [just validate]
- layout-dump-43: Clause `ports` MUST hold when every route has at least one point, its first point satisfies `on_boundary` of the `from` rect, and its last point satisfies `on_boundary` of the `to` rect, and its message MUST be `route end is off its box boundary`. [just validate]
- layout-dump-44: Clause `route-clearance` MUST hold when, for every route `r` and every exclusive box `b` with `b.id` not in `Scope(r)`, `Polyline.hitsRect(r.points, b.rect)` is false, and its message MUST be `route crosses an exclusive box`. [just validate]
- layout-dump-45: Clause `label-clearance` MUST hold when, for every label `l` and every exclusive box `b` with `b.id` not in `OwnerAnc(l)`, `intersects(l.rect, b.rect)` is false, and its message MUST be `label overlaps an exclusive box`. [just validate]
- layout-dump-54: Clause `frame-clearance` MUST hold when both conditions below hold, and its message MUST be `group frame overlaps a foreign box or label`. [just validate]
    Let `G` be the boxes with `role` `group`.
    1. For every `g` in `G` and every box `b` other than `g` with `g.id` not in `anc(b)` and `b.id` not in `anc(g)`, `Disjoint(g.rect, b.rect)` MUST be true. This covers node boxes that are not members of `g`, at any depth, sibling frames, and cousin frames. A nested frame has one id in the `anc` of the other, so this condition skips it, because clause `parent` already makes it contained.
    2. For every `g` in `G` and every label `l`, `Disjoint(g.rect, l.rect)` or `StrictInside(g.rect, l.rect)` MUST be true.
    `StrictInside(o, i)` is true when `o.x < i.x`, `i.x + i.w < o.x + o.w`, `o.y < i.y`, and `i.y + i.h < o.y + o.h`.
    No label straddles a frame boundary, and no label touches a frame boundary from inside. The strict form is required by the cell profile: the border cells of a frame are the columns `x` and `x + w - 1` and the rows `y` and `y + h - 1`, so a label that is only contained could print on them. Nested frames need containment only. A group title is not a dump object. It lies strictly inside its own frame, so condition 1 protects it from foreign frames and nodes.

## Outcomes

- layout-dump-46: `Validator.validate d` MUST return the first clause in this order that fails, or none. [just proofs]
- layout-dump-47: `Validator.check d` MUST be true exactly when no clause fails. [just proofs]
- layout-dump-48: `geomcheck validate` MUST print `valid` and exit 0 when `check` is true, and otherwise MUST print `invalid <clause-id>: <message>` and exit 1, for example `invalid canvas: box outside canvas`. [just validate]
- layout-dump-49: `HardConstraints d` MUST be the conjunction `C1 d and C2 d and C3 d and C4 d and C5 d and C6 d and C7 d and C8 d`, where `Ci` is the predicate of clause `i`. [just proofs]
- layout-dump-50: `Validator.check` MUST compute each `Ci` as a Boolean test and MUST combine the eight tests with `&&`. [just proofs]
- layout-dump-51: The soundness theorem `Validator.sound` MUST hold, and its statement MUST be the row of the kernel theorem table of `spec/lean-reference.md`. [just proofs]
- layout-dump-52: The cell-profile rules of `spec/quality-metrics.md` MUST be outside `HardConstraints`. [just quality]
- layout-dump-53: `just validate` MUST pipe every corpus dump from both implementations through `geomcheck validate`. [just validate]

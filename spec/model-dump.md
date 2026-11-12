# Model-stage dump

This file fixes the dump that `emd layout --stage model` prints, which the Lean reference reads as its input.

## Shape and bytes

- model-dump-01: The model-stage dump MUST use the JSON shape and byte rules of the canonical layout dump of `spec/layout-dump.md`, with `"stage":"model"`. [just lean-parity]
- model-dump-02: The dump MUST NOT hold `canvas`. [just lean-parity]
- model-dump-03: A box MUST NOT hold `x`, `y`, `w`, or `h`. [just lean-parity]
- model-dump-04: A route MUST NOT hold `points`. [just lean-parity]
- model-dump-05: A label MUST NOT hold `x`, `y`, `w`, or `h`. [just lean-parity]
- model-dump-06: The model stage MUST write each label's unwrapped text in `text` and an empty array in `lines`, which MUST be written as `"lines":[]`. [just lean-parity]
- model-dump-07: Measurement MUST fill `lines` from the profile and `max_width`. [just lean-parity]
- model-dump-08: The `options` object MUST hold the resolved options, `direction` included, and every honoured config key that affects layout, in the key order of `spec/layout-dump.md`. [just lean-parity]
- model-dump-09: `emd layout --stage model [--profile P]` MUST print the dump before measurement and layout: the kind, the boxes (nodes and groups), the routes (edges), and the labels with their unwrapped text, and no coordinates. [just go-check]

## Readers

- model-dump-10: `geomcheck layout` MUST read the model-stage dump from stdin and print the canonical layout dump. [just lean-parity]
- model-dump-11: `geomcheck text --charset unicode|ascii` MUST read the model-stage dump from stdin and print the text rendering, under the cell profile and with colour off. [just lean-parity]
- model-dump-12: `proofs/Elegant/Dump.lean` MUST hold the reader of the model-stage dump and the `toDump` writer of the layout dump. [just proofs]

## Golden example

- model-dump-13: The model-stage dump of the input `flowchart` header followed by the line `A -->|yes| B` MUST be these bytes, with one LF at the end of the last line. [just lean-parity]

    ```
    {"version":1,"stage":"model","kind":"flowchart","profile":"vector","options":{"profile":"vector","thoroughness":3,"max_width":0,"direction":"TB","limits":{"max_nodes":2000,"max_edges":5000,"max_text_bytes":1048576}},
    "boxes":[{"id":"A","role":"node","parent":"","exclusive":true},
    {"id":"B","role":"node","parent":"","exclusive":true}],
    "routes":[{"id":"e0","from":"A","to":"B","orthogonal":true}],
    "labels":[{"id":"e0.label","owner":"e0","text":"yes","lines":[]}]}
    ```

## Parity binding

- model-dump-14: The two comparisons of this dump against `geomcheck layout` and `geomcheck text` MUST be the ones that `spec/lean-reference.md` fixes. [just lean-parity]
- model-dump-15: `emd layout --stage model` MUST run neither measurement nor layout, so it MUST print the dump before both stages. [just go-check]
- model-dump-16: The model-stage dump MUST be one of the inputs that `just parity` compares between the Go and Rust binaries. [just parity]
- model-dump-17: A box label MUST be a label record with the id `<boxId>.label` and the box as `owner`, written exactly when the label text of the box differs from its id, an empty label included; a box with no such record has its id as its label text; the box label records MUST come first, in box order, then the route label records in route order. [just lean-parity]
- model-dump-18: A label record owned by an exclusive box MUST exist only in the model stage, where it carries the box text for measurement; layout MUST draw that text inside the box as scene `Text` primitives and MUST NOT write the record to the `labels` array of the layout-stage dump, so clause `label-clearance` of `spec/layout-dump.md` applies only to labels that layout places as separate objects. [just lean-parity]

# Header matching

This file fixes how the parser finds the diagram header keyword.

## Scope

- detection-01: Detection MUST cover the 33 kinds, their 52 header keywords, and their 37 upstream detector registrations, as the rows of `spec/data/kinds.json` define. [just gen-check]
- detection-02: Each kind row of `spec/data/kinds.json` MUST list, in its `aliases` array, the upstream detector ids that map to its kind id. [just gen-check]
- detection-03: An upstream detector id that has no row alias MUST fail `gen-check`. [just gen-check]
- detection-04: The upstream `error` and `---` pseudo-diagrams MUST NOT be kinds. [just gen-check]

## Header position

- detection-05: The header MUST be the first statement after optional whitespace, frontmatter, directives, and comment lines. [just go-check]
- detection-06: Detection MUST skip leading spaces and tabs before the first statement. [just go-check]
- detection-07: Frontmatter, directives, and comment lines MUST be as `spec/preprocessing.md` defines them. [just go-check]

## Header token

- detection-08: The header token MUST be the maximal run of ASCII letters, digits, `-`, and `_` at that position. [just go-check]
- detection-09: The token MUST equal a header keyword of `spec/data/kinds.json`; equality gives the word boundary. [just go-check]
- detection-10: A keyword MUST match only when the text starts with it and the next byte is the end of input or a byte that is not an ASCII letter, digit, `-`, or `_`. [just go-check]
- detection-11: At most one keyword MUST match a header token. [just go-check]
- detection-12: Detection MUST NOT match a keyword that is only a prefix of the header token. [just go-check]

## Keyword case

- detection-13: A header keyword MUST match case-sensitively by default. [just go-check]
- detection-14: The keywords `ishikawa`, `ishikawa-beta`, `railroad-beta`, `railroad-ebnf-beta`, `railroad-abnf-beta`, `railroad-peg-beta`, and `wardley-beta` MUST match with ASCII case folding. [just go-check]
- detection-15: `spec/data/kinds.json` MUST record the case rule of each keyword. [just gen-check]
- detection-16: Case folding MUST be ASCII only. [just go-check]

## Outcomes

- detection-17: A first statement that matches no keyword MUST raise `common/unknown-diagram-kind` (error) with the span of its first token, the message `unknown diagram kind TOKEN`, and the help `Start the source with a supported diagram header, for example flowchart.` [just go-check]
- detection-18: Source that holds only whitespace, frontmatter, directives, or comments MUST raise one `common/empty-source` (error) with span `0..0`, the message `source is empty`, and the help `add a diagram header, for example flowchart`. [just go-check]
- detection-19: A header token of `error` MUST match no keyword, so the source MUST get `common/unknown-diagram-kind`. [just go-check]
- detection-20: A source that starts with `---` MUST follow the frontmatter rule of `spec/preprocessing.md`. [just go-check]
- detection-21: For every corpus file without a row in `corpus/divergences.json`, the detected kind MUST equal the upstream kind of `corpus/verdicts.json`. [just oracle]
- detection-22: A corpus file with a row in `corpus/divergences.json` MUST match the `upstream_verdict` and `our_verdict` of its row. [just oracle]
- detection-23: Go and Rust MUST detect the same kind for the same source. [just parity]

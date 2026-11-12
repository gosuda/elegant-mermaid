# Config key classification

This file fixes the classification of every upstream config key and the diagnostics that a config key raises.

## Registry

- config-01: Each of the 58 top-level schema keys, 27 general keys and 31 per-diagram blocks, MUST have one row in `spec/data/config-keys/common.json`. [just theme-check]
- config-02: The keys inside a per-diagram block MUST have one row each in `spec/data/config-keys/<kind>.json`, where `<kind>` is the kind id that the block names. [just theme-check]
- config-03: `tools/specgen` MUST merge the per-kind files with `spec/data/config-keys/common.json` into the `configkeys` table. [just gen-check]
- config-04: A row from `common.json` MUST carry the kind value `""`. [just gen-check]
- config-05: The `configkeys` table MUST sort by `kind` bytewise with `""` first, then by `key` bytewise. [just gen-check]
- config-06: `tools/specgen` MUST fail `gen-check` when a schema key has no row. [just gen-check]
- config-07: `tools/upstream-oracle/config-keys.mjs --missing DIR` MUST print each schema key that has no row under `DIR`, one per line, and MUST exit 1 when any key is missing. [just theme-check]

## Class rule

- config-08: Every schema key MUST have one class: `honoured`, `accepted-ignored`, or `rejected`. [just gen-check]
- config-09: A schema key MUST be `honoured` exactly when the specification set names the key as read. [just gen-check]
- config-10: A key MUST count as named as read when a layout rule, a limit, a theme or look rule, or an output rule uses its value. [just go-check]
- config-11: Every schema key that is not `honoured` MUST be `accepted-ignored`. [just gen-check]
- config-12: A key whose only use is the upstream oracle MUST be `accepted-ignored`. [just gen-check]
- config-13: This version MUST classify no key as `rejected`. [just gen-check]

## Unknown keys

- config-14: A key in a config document MUST be looked up in the `configkeys` table. [just go-check]
- config-15: A key that is not in the upstream schema MUST raise `config/unknown-key` (warning). [just go-check]
- config-16: The message MUST be `unknown config key KEY`, and the help `Check the spelling of the key, or remove it.` [just gen-check]

## Rejected class

- config-17: The `rejected` class and its diagnostic `config/unsupported-key` (warning) MUST stay defined for the registry format. [just gen-check]
- config-18: The message of `config/unsupported-key` MUST be `config key KEY is not supported by this project`, and the help `Remove the key; this project cannot produce the output it asks for.` [just gen-check]

## Accepted and ignored keys

- config-19: `layout` MUST be `accepted-ignored`, because there is one layout engine. [just gen-check]
- config-20: A `layout` value MUST raise no diagnostic. [just go-check]
- config-21: `securityLevel` MUST be `accepted-ignored`, and output MUST always be static and escaped. [just go-check]

## Honoured keys

- config-22: `fontFamily` MUST be `honoured`. [just gen-check]
- config-23: `fontFamily` MUST be emitted as the SVG `font-family` attribute. [just go-check]
- config-24: In the vector profile, a non-empty `fontFamily` MUST change each measured width to `floor_div(w * 108, 100)`, where `w` is the width measured with Inter. [just go-check]
- config-25: A non-empty `fontFamily` MUST raise `config/font-metrics-approximate` (info), with the message `text width is measured with Inter; fontFamily is VALUE` and the help `Text widths may differ from the font named in fontFamily.` [just go-check]
- config-26: `maxTextSize` and `maxEdges` MUST be `honoured` as limits. [just gen-check]
- config-27: `look` MUST be `honoured`: `handDrawn` redraws vector strokes, and `neo` is a token variant. [just gen-check]
- config-28: The value grammar and the value checks of a honoured key MUST follow the topic that reads the key. [just go-check]

## Limits

- config-29: The text size MUST be the UTF-8 byte length of the Mermaid source passed to the parser. [just go-check]
- config-30: The text-size limit MUST be `maxTextSize`, default 50000. [just go-check]
- config-31: Source above the limit MUST raise `limit/max-text-size` (error), with a span from the limit value to the end of the source. [just go-check]
- config-32: The message MUST be `source has SIZE bytes; the limit is LIMIT bytes`, and the help `Shorten the source, or raise maxTextSize.` [just gen-check]
- config-33: The edge count MUST be the number of edge records in the resolved model, including self-loops and back edges, in declaration order. [just go-check]
- config-34: The edge limit MUST be `maxEdges`, default 500. [just go-check]
- config-35: More edges than the limit MUST raise `limit/max-edges` (error), with the span of the statement of edge `max + 1`. [just go-check]
- config-36: The message MUST be `diagram has COUNT edges; the limit is LIMIT`, and the help `Reduce the number of edges, or raise maxEdges.` [just gen-check]

## Nesting limit

- config-37: The nesting depth of subgraphs, blocks, fragments, groups, and math groups MUST be limited to 64. [just go-check]
- config-38: Deeper input MUST raise `limit/nesting-depth` (error), with the message `nesting depth exceeds 64` and the help `Reduce the nesting to 64 levels or fewer.` [just gen-check]
- config-39: Parsers MUST NOT recurse deeper than 64 levels. [just go-check]
- config-40: The nesting of config values MUST follow `spec/preprocessing.md`. [just go-check]

## Config documents

- config-41: A config key MUST reach the implementation through a config document: the frontmatter `config` mapping, or the `Config` text of the layout options. [just go-check]
- config-42: A config document MUST be one block mapping in the config-value grammar of `spec/preprocessing.md`. [just go-check]
- config-43: Go and Rust MUST produce the same config diagnostics for the same config document. [just parity]

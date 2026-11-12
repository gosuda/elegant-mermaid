# Source and positions

This file fixes the source text, its UTF-8 repair, byte spans, the line index, position conversion, and aliasing.

## Source text and repair

- source-and-positions-01: A source that is not valid UTF-8 MUST raise the diagnostic `source/invalid-utf8` (error) at the first bad byte, with the message `invalid UTF-8 at byte OFFSET`. [just go-check]
- source-and-positions-02: Each maximal subpart of an ill-formed sequence MUST become one U+FFFD before lexing, following the WHATWG UTF-8 decoder. [just go-check]
- source-and-positions-03: Go `Parse` MUST perform the repair with an explicit byte loop and MUST NOT use a `range` over a string. [just go-check]
- source-and-positions-04: Rust `parse_bytes` MUST perform the repair, and Rust `parse(&str)` MUST accept valid text only. [just rust-check]
- source-and-positions-05: `Document.Source()` and `Document::source()` MUST return the input, or the repaired copy when the input was not valid UTF-8. [just go-check]

## Spans

- source-and-positions-06: A span MUST be a pair of byte offsets with an exclusive `end`. [just go-check]
- source-and-positions-07: Every span MUST lie inside the source, with `0 <= start <= end <= len(source)`. [just go-check]
- source-and-positions-08: Every span boundary MUST lie on a UTF-8 boundary. [just go-check]

## Aliasing

- source-and-positions-09: `Parse` MUST NOT copy valid input, and `Source` MUST return the caller's slice. [just go-check]
- source-and-positions-10: The caller MUST NOT change `src` while the `Document` is in use. [just go-check]
- source-and-positions-11: An input that is not valid UTF-8 MUST be repaired into a copy that the `Document` owns, and `Source`, every `Span`, and every `Position` MUST use that copy. [just go-check]
- source-and-positions-12: `ApplyFixes` MUST return a new slice that never aliases `src`, and MUST return repaired text when `src` was invalid. [just go-check]
- source-and-positions-13: A `Block` MUST alias the host slice only for a top-level fence, where no container prefix was removed, and MUST own a copy otherwise; Rust holds a top-level fence as `Cow::Borrowed` and any other block as `Cow::Owned`. [just go-check]
- source-and-positions-14: Rust `parse(&str)` MUST borrow its input. [just rust-check]
- source-and-positions-15: Rust functions that take `&str` MUST require valid UTF-8, and a caller that holds bytes MUST use `parse_bytes`. [just rust-check]
- source-and-positions-16: `ParseIconPack` MUST NOT repair invalid UTF-8: Go MUST return `ErrBadIconPack`, and Rust MUST return `IconPackError::Malformed`. [just go-check]

## Line index and positions

- source-and-positions-17: A line MUST end at LF, at CRLF, or at a CR that is not followed by LF, as `spec/preprocessing.md` defines. [just go-check]
- source-and-positions-18: The CR of a CRLF MUST NOT be part of its line. [just go-check]
- source-and-positions-19: A line MUST start at offset 0 and at each offset just after a line ending. [just go-check]
- source-and-positions-20: `Position` MUST map a byte offset to a 1-based `line` and `column`. [just go-check]
- source-and-positions-21: `column` MUST be 1 plus the number of Unicode scalar values between the line start and the offset. [just go-check]
- source-and-positions-22: `Position` MUST clamp `offset` to `[0, len(Source)]`. [just go-check]
- source-and-positions-23: An offset inside a UTF-8 sequence MUST map to the start of that sequence. [just go-check]
- source-and-positions-24: A span end MUST map as an offset by the same rules, so `end_column` MUST be the column just after the last scalar. [just go-check]
- source-and-positions-25: A property test MUST compare `Position` with a naive line scan as the oracle, with cases for LF, CRLF, and lone CR that check that columns count scalars, not bytes. [just go-check]
- source-and-positions-26: Go and Rust MUST produce the same `line` and `column` for the same source and offset. [just parity]

## UTF-16 conversion

- source-and-positions-27: The Go and Rust APIs MUST expose no UTF-16 offset. [just go-check]
- source-and-positions-28: UTF-16 code units MUST be used only for the SARIF columns of `spec/lint.md`. [just go-check]
- source-and-positions-29: A UTF-16 column MUST count a scalar above U+FFFF as two code units and every other scalar as one. [just go-check]

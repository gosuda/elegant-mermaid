# Markdown extraction

This file fixes the fence scanner that finds Mermaid blocks in a Markdown host, the block records it returns, and the mapping of a block offset to a host offset.

## Block records

- markdown-extraction-01: `MarkdownBlocks` and `markdown::blocks` MUST scan the host as bytes. [just go-check]
- markdown-extraction-02: A block whose text is not valid UTF-8 MUST get `source/invalid-utf8` when it is parsed. [just go-check]
- markdown-extraction-03: `Source` MUST be the block text with its container prefixes, the block quote prefix and the list item prefix, removed. [just go-check]
- markdown-extraction-04: `Lines` MUST hold one `BlockLine` for each line of `Source`. [just go-check]
- markdown-extraction-05: `BlockOffset` MUST be the offset in `Source` of the line's first content byte, `HostOffset` MUST be the host offset of that byte, and `Len` MUST be the byte count of the line's content without its line ending. [just go-check]
- markdown-extraction-06: `Block.Source` MUST alias the host slice for a top-level fence, where no container prefix was removed, and MUST be a copy that the `Block` owns otherwise. [just go-check]
- markdown-extraction-07: Rust MUST hold a top-level fence as `Cow::Borrowed` and any other block as `Cow::Owned`. [just rust-check]
- markdown-extraction-08: `Span` MUST be the byte span in the host file, and `HostOffset(blockOffset)` MUST clamp `blockOffset` to `[0, len(Source)]`, MUST find the line `i` with the largest `BlockOffset_i <= blockOffset`, and MUST return `HostOffset_i + min(blockOffset - BlockOffset_i, Len_i)`. [just go-check]
- markdown-extraction-09: An offset on a line ending MUST map to the host position just after that line's content. [just go-check]
- markdown-extraction-10: A block with no lines MUST map every offset to `Span.Start`. [just go-check]
- markdown-extraction-11: Rust MUST use the same rule with the fields `lines`, `host_offset`, `block_offset`, and `len`. [just rust-check]

## Fence opener

- markdown-extraction-12: A fence opener MUST be an indentation of 0 to 3 spaces after the container prefix, then three or more backticks or three or more tildes. [just go-check]
- markdown-extraction-13: The first word of the info string MUST be `mermaid`, `mmd`, or `{mermaid}`, compared ASCII case-insensitively, for the fence to be a block. [just go-check]
- markdown-extraction-14: The scanner MUST also read `:::mermaid` containers. [just go-check]

## Closing fence

- markdown-extraction-15: The closing fence MUST use the same character as the opener, MUST be at least the opener's length, MUST have an indentation of 0 to 3 spaces, and MUST hold only spaces or tabs after it. [just go-check]
- markdown-extraction-16: A fence still open at the end of its container MUST close there. [just go-check]
- markdown-extraction-17: A `:::` container MUST open with `:::mermaid` followed only by spaces or tabs, MUST close with a line of `:::` followed only by spaces or tabs, and MUST end at its close marker or at the end of its host container. [just go-check]

## Container prefixes

- markdown-extraction-18: Each `>` marker of a block quote prefix and at most one following space MUST be stripped, and a line without the prefix MUST end the quote. [just go-check]
- markdown-extraction-19: A line inside a list item MUST carry the item's content indentation, which is the column after the marker and the spaces that follow it, where a tab advances to the next multiple of 4, and that indentation MUST be stripped. [just go-check]
- markdown-extraction-20: Nested containers MUST strip their prefixes from the outermost inward. [just go-check]

## Host output rules

- markdown-extraction-21: A path ending `.md`, `.markdown`, or `.mdx` MUST be a host document, and `check` and `lint` MUST map every diagnostic to host positions. [just go-check]
- markdown-extraction-22: `render` of a host MUST require `-o` or `-a`. [just go-check]
- markdown-extraction-23: `-o IMAGE` MUST write `<stem>-N<ext>` per block. [just go-check]
- markdown-extraction-24: `-a DIR` alone MUST write `<input-stem>-N.<ext>` into `DIR`. [just go-check]
- markdown-extraction-25: `-o HOST.md` MUST write a copy of the host in which each block is an image link, with alt text equal to the diagram `accTitle` and `diagram` when that is absent, with images in `-a`, default `<HOST-stem>.assets`, and with image format `svg` or `png`, default `svg`. [just go-check]
- markdown-extraction-26: A host with zero Mermaid blocks MUST exit 1 with `no Mermaid blocks found in INPUT; add a fenced code block labelled mermaid` and MUST write nothing. [just go-check]
- markdown-extraction-27: `--fix` on a Markdown host MUST edit inside the blocks only and MUST map each edit back to host offsets. [just go-check]
- markdown-extraction-28: The Rust `markdown::blocks` MUST return the same blocks, `Source` bytes, and host offsets as the Go `MarkdownBlocks` for the same host. [just rust-check]
- markdown-extraction-29: `check` and `lint` MUST read `.md`, `.markdown`, and `.mdx` hosts in their directory walk, beside the `.mmd` and `.mermaid` files. [just go-check]
- markdown-extraction-30: A lint fix MUST be computed on `Source`, so that only the block-to-host mapping of this file is needed to place it in the host. [just go-check]

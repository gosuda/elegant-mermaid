# Windows Markdown path repair contract

This is a proposed cross-engine contract derived from the frozen native observations. It is not candidate verification.

## Source and evidence

- Maintained renderer source: [9a11e8cc](https://github.com/gosuda/elegant-mermaid/commit/9a11e8cc04299367d07c0137653fa87a4e1b945b).
- Parent-owned build-only source: [9c8339a1](https://github.com/gosuda/elegant-mermaid/commit/9c8339a1c214eb93c92384db55edc0e89851ea8a).
- Authentic native Windows baseline: [45958671740](https://github.com/gosuda/elegant-mermaid/actions/runs/45958671740).
- Exact commands, source identities, artifact identity, 19 normalization observations and all 20 Go CLI records are in baseline2.json in this directory.

The Go path implementation is in internal/cli/output_path.go and internal/cli/render_markdown_output.go. The Rust implementation is in crates/elegant-mermaid-cli/src/render/markdown/links.rs, with output targets constructed in output.rs.

## Required behavior

1. Identify ordinary versus explicit verbatim spelling from the user operand. Preserve filesystem component order: resolve a directory link before processing a following parent component. Keep the existing missing-directory cancellation and non-directory/dangling-link rejection behavior.
2. Apply ordinary Windows normalization only to components still belonging to that operand. Do not normalize a previously canonicalized ancestor or a resolved link target again. The frozen native records distinguish a final operand component from an intermediate component; a blanket trim on every component is invalid.
3. Preserve the canonical spelling and identity of literal directory-link targets, including trailing ASCII space or period. Appending an ordinary child component must not strip or reinterpret those canonical ancestors.
4. URL comparison must accept equivalent ordinary/verbatim local-drive or UNC roots without changing filesystem-operation paths. Either canonicalize both roots to the same representation or normalize only their comparison identities. Different volumes must remain rejected.
5. Emit complete correct Markdown link bytes and write the image into the directory identified by the native operand. Cover existing and prospective trailing-dot directories, both mixed-prefix directions, explicit literal directory operands, local/UNC forms, and links to literal targets. The current failing Go result must not serve as the expected oracle.
6. Keep the final output entry unfollowed: atomic replacement must continue replacing a final symlink rather than its target. Moving to canonical directory paths must not silently change how an ordinary final filename is interpreted; this needs a bounded neighboring control if the repair affects that boundary.
7. Complete all planning and path validation before creating directories or writing output. Keep diagnostics tied to the original requested path.

## Proposed Rust boundary

Retain canonical filesystem paths. For ordinary operands, normalize only the next raw component, with its final/intermediate context, then join it to the canonical ancestor. Existing directories can then be canonicalized without dropping their verbatim prefix. Explicit verbatim operands skip ordinary normalization. The component-order loop and final-entry treatment remain visible.

Rust's std::path::absolute uses GetFullPathNameW for ordinary Windows paths without filesystem access. A synthetic rooted component probe can obtain Windows normalization without reinterpreting a literal canonical ancestor. The actual native observations, including final all-dot/space components and intermediate trailing spaces, constrain that operation. No production implementation has been selected or published yet.

## Ownership and gates

The worker owns the Rust and README changes. The parent owns the Go counterpart and the timeout conversion. Both engines must join the same maintained commit, after focused native Windows proof and parent-run repository gates. The README correction installs playground packages before invoking Playwright. Temporary proof workflows do not become permanent CI jobs.

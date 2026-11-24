# Rust cell recovery status

The four production files in this branch preserve the independent occupied-line/swimlane-stub patch. They do not register or enable the generic cell-route refinement.

## Generic refinement snapshot

cell_routes.rs.txt is the complete main module copied from a recorded full file read. The sibling candidates.rs, contacts.rs, invariants.rs, private tests.rs, and public tests/cell_routes.rs were not present in the surviving full-text record. Retrieve the original workspace or the parent agent's earlier route-snapshot before integrating the main module. Do not treat a reconstruction from a behavioral summary as byte-identical to the tested implementation.

The current refinement algorithm is restricted to the nine layered kinds and cell profile, with a 1,048,576-cell allocation budget. It preserves endpoints, terminal directions, group and endpoint-node constraints, owned text contacts, canonical/display route correspondence, and primitive inventory. Candidate admission uses full canonical checks and the actual projected cell renderer. Both refused glyphs and route conflict cells never increase, with one strictly decreasing. The private sequence is published only when the final refused glyph count is zero; otherwise the complete original scene is returned.

## Tests completed before the outage

- The route-only version passed scoped Clippy with warnings denied and 11 private tests.
- After the refusal-aware extension, public cell_routes, cell_masks, and agentflow_padding integration targets passed all 15 tests.
- The final actual-renderer probe passed all 26 remaining four-family fixtures: canonical hard validity true, refused glyphs zero, and route conflicts zero in every row.
- The new refusal-aware private tests and final Clippy rerun had not executed.
- The independent occupied-line/stub patch was formatted and diff-checked but had not compiled or run under Rust. Its paired Go regressions were observed red.

## Performance and build limitations

The unoptimized Rust probe measured flowchart_weave at 109,408ms, state_nested at 13ms, and all other final fixtures between 3ms and 876ms. The separately compiled optimized Go implementation measured weave at 3.756s and state_nested at 6ms.

An isolated opt-level=2 Rust core build was SIGKILLed under container memory pressure. One subsequent default-debug PNG-enabled CLI build was also SIGKILLed in elegant-mermaid after compiling its dependencies. Neither failure was a source diagnostic; neither produced a new green native runtime result. No performance pruning or arbitrary candidate cap was applied.

Reconstructed additions need rustfmt and full compilation in a restored workspace or CI. Complete Go/Rust/Lean parity and all repository gates remain required before publication.

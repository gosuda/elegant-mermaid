# Paired quality diagnostic r39

This directory is an inactive proof draft. The parent owns activation and all gate execution under the repository AGENTS.md. There is no new file under .github/workflows in the draft commit, and no job has been launched.

## Question and scope

Determine whether the eight-path Windows/Markdown output change affects the Linux layout-quality measurements. Compare maintained commit 98ef933e487f502e2e3555750e6621291ba21601 with candidate eb11dfb51e044cd31712fbda0f1e39cb374639ae, without product edits, a baseline rewrite, threshold changes, or another full verification run.

The two exact source indexes contain 6,711 and 6,714 regular blobs respectively, including three executable files in each. The common index is split into five bounded JSON files. The eight-entry candidate delta records every expected old blob/mode and exact new blob/mode; the driver validates every resulting source file and both Git trees.

## Preserved failures

- Root run 45988680468, producer 761b6a3fa979838fd68d6949c7db2a9734e880c0, failed with raw exit 137. Signal 9 was observed; its cause was not established.
- Root run 45996807575, producer cd6ece93aad807f38ccea0a0e756673180dc2a9f, failed with raw exit 1 after 5741.294 seconds. All four quality gates failed. There was no timeout or monitor error, and the source was restored. The following theme-check recipe was not reached.
- The second failure's same-repository artifact is authenticated by producer, run, job, artifact, size, digest and terminal conclusion. The complete archived just-verify.log and report.json are preserved in the new evidence. No earlier recipe is reclassified or rerun.
- The r36 workflow was retired at 483b404282b0b74b880b1b6f7f095706f296fa8a. The successful native Windows proof remains independent.

The committed quality-corpus.txt contains 2,075 paths, while quality-exceptions.json declares 857 fixtures and 419 exceptions. The exact gate requires both files to match its generated data, whose fixture count is the selected list length. Those committed counts cannot both match. This source-derived inconsistency is distinct from the four measured failures; this proof does not change either file.

## Exact execution

The draft workflow uses only depot-ubuntu-24.04-8. It checks out the two source commits and the proof into three separate directories. Tool pins match the failed root run: Go 1.27.4, Node 26.13.1, pnpm 12.23.0, Rust 1.100.0, just 1.59.0, cargo-nextest 0.9.151, uv 0.13.9 and Python 3.15.

Each lane has a fresh Go module cache, Go build cache, real binary, pnpm store, node_modules directory, baseline cache and evidence records. Each native command inherits one CPU selected from the runner's allowed mask. GOMAXPROCS=8 remains the exact failed-root setting. The parent supervisor's original affinity is restored immediately after spawning each owned process.

The actual recipe is just quality JOBS=1 in each source root. Neither lane uses -write. A failure in one lane does not suppress the other lane or the independent missed theme recipe.

### Observation without replaying every fixture

For the quality invocation only, an explicitly disclosed launcher occupies the untracked bin/emd-go path. It forwards the original arguments to that lane's fresh immutable real executable. It relays native stdout and stderr bytes unchanged, preserves the actual exit or signal, and records:

- exact argv, cwd, binary binding and CPU mask;
- stdout/stderr hashes and byte lengths;
- full metric stdout and stderr bytes;
- vector-output hashes from the actual baseline-generation invocation.

The real binary is hashed before and after the quality recipe, and its device, inode, size, mtime and mode are checked for every invocation. Go build metadata must name the exact source revision. No alternate metric scorer or source instrumentation is used. The observer records the calls that the real recipe already performs; it does not repeat all layout work.

Every selected fixture must have exactly one vector invocation and three metric invocations (ours, Dagre, ELK), all completing normally. The driver checks the actual report rows and four printed verdicts against those native metric records, including hard_ok. It retains all numerical measurements, exact vector/metric stdout hashes and both baseline dump hashes. The two reports are compared without stripping numeric differences.

Vector output files are hashed rather than uploaded in bulk. Complete metric byte records, stderr, both full quality logs, source indexes, per-fixture measurements, baseline hashes and all differences remain in the evidence artifact. Binaries, package caches and temporary build files are outside the artifact.

## Missed theme recipe

The candidate then runs the unchanged just theme-check, including its existing build dependency. This requires native Go/Rust builds, Rust/nextest and the already installed Node oracle packages. It does not invoke full verify, house lint, Lean, a browser, WebAssembly or model checking. No optional theme bypass is introduced.

The theme result is recorded separately. A quality failure cannot turn it into a success or suppress it when its own prerequisites completed. Failure within theme-check retains the ordinary recipe's own stopping behavior.

## Cleanup and result semantics

Each command owns a separate session/process group. The supervisor records actual exit, timeout, duration, affinity and log digest. A timeout or supervisor error kills and reaps owned children. Active descendants left behind by a successful command make that command unsuccessful. Source restoration is forbidden while an owned process remains active.

Every tracked blob and executable mode is checked before execution, after quality, before restoration and after restoration. Any pre-restoration source mutation remains an error even when restoration succeeds. The driver does not use git clean or remove unrelated source content.

A complete causal comparison is not a successful quality gate. Any failed quality or theme recipe leaves the final process exit nonzero. The report always sets publication_eligible=false, even if every diagnostic command succeeds. The original full-root failure remains failure.

## Parent activation

After reviewing the exact draft and refreshing the maintained/main/proof refs, the parent may copy workflow.yml.inactive byte-for-byte to .github/workflows/elegant-quality-r39.yml on this isolated branch. The driver refuses execution if the active workflow hash differs or the proof checkout does not match GITHUB_SHA.

The workflow requests contents:read plus actions:read solely to authenticate the prior same-repository artifact. The reviewed artifact helper changes only its repository route from gosuda/sloplint to gosuda/elegant-mermaid. Authorization is attached only to GitHub API requests; the storage redirect uses a fresh credential-free request. The token is removed from all product and dependency subprocess environments.

This draft has received source inspection only. It makes no Python compilation, native execution, ZIP-download or successful gate claim.

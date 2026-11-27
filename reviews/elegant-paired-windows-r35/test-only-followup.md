# Test-only Windows follow-up

Source: eb11dfb51e044cd31712fbda0f1e39cb374639ae, tree 1629dfcca209b305a96dceebafef8bb4e5bf3267, 6,714 blobs.

The prior run 45976852511 remains FAILURE. Its only unexpected exit was the Go namespace test's cognitive-complexity lint finding. Parent changed only that test's structure relative to the verified formatted tree ca39add4228047157b215c282f0bc4ed850d4032. Production bytes, the twelve cases, all assertions, and the five earlier Go tests remain unchanged.

The follow-up authenticates prior producer/run/job metadata and downloads artifact 15187753936 through the same-repository read-only Actions token. The downloaded ZIP must match SHA-256 4f0a57ba34a3939c0fb66bc096a807d8fc8841a26717e90cb93a083dd229acbc. The helper verifies the archived full job log/report, all 59 command logs, eight formatted source payloads and complete compiled index. Command log hashes follow the original driver's documented universal-newline text hashing; source and ZIP bytes are verified without normalization.

The exact new source must differ from that compiled index in only internal/cli/output_path_windows_test.go, before and after the authorized formatting step. Only the 32 explicitly listed successful unchanged historical/native/Rust receipts are reused. The prior overall failure remains explicit.

New execution reruns the changed Go test's discriminating old-predicate mutation, Go format/vet/lint, all six named Go tests, fresh Go and Rust CLI builds, every pending 20+4 case per engine, byte parity, whitespace, and full source restoration. Binaries/build directories are outside the evidence upload. The Actions token is removed from the child-process environment before compilation.

The parent separately owns the actual root just verify gate on the final source tree. This prepared record does not establish completed verification or publication eligibility.

Driver SHA-256: 825a0bebb56c44b35c09aeb23fea5819cb3bd8cb73db0e044fcbff2a1aadec8d
Receipt helper SHA-256: ce0040bcd25b7d97b312a16d56faf6fc636d2705f17d70ef9f03f299b23a7df0
Manifest SHA-256: d2acb21d0828340392e52b2a01086be24a95405e411f7f620d329c206b3d8847
Workflow SHA-256: 5ecb77932d142d1eec1d6a6f92dd34d1682a24a30c4ca0bb422ecdad6ee4a6f8

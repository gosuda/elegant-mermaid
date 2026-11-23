import { readFileSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';

const overlay = JSON.parse(readFileSync('stability-recovery/family-overlay.json', 'utf8'));
const expected = [
  "crates/elegant-mermaid/src/layout/agentflow.rs",
  "crates/elegant-mermaid/src/layout/agentflow/tests.rs",
  "crates/elegant-mermaid/src/layout/state/paint.rs",
  "crates/elegant-mermaid/tests/cell_masks.rs",
  "internal/layout/agentflow.go",
  "internal/layout/cell_decoration_test.go",
  "internal/layout/state_paint.go"
];
if (overlay.base !== '4f18d67db8d2e7434cfbf6eed0627d6bb182923d' ||
    JSON.stringify(Object.keys(overlay.files).sort()) !== JSON.stringify(expected)) {
  throw new Error('unexpected family overlay base or paths');
}
execFileSync('git', ['diff', '--exit-code', overlay.base, '--', 'internal', 'crates'], { stdio: 'inherit' });
for (const file of expected) {
  if (typeof overlay.files[file] !== 'string') throw new Error('missing source ' + file);
  writeFileSync(file, overlay.files[file]);
}
const go = expected.filter((p) => p.endsWith('.go'));
const rust = expected.filter((p) => p.endsWith('.rs'));
execFileSync('gofmt', ['-w', ...go], { stdio: 'inherit' });
execFileSync('rustfmt', ['--edition', '2024', ...rust], { stdio: 'inherit' });
const formatted = Object.fromEntries(expected.map((file) => [file, readFileSync(file, 'utf8')]));
writeFileSync('recovery-results/family-patched-sources.json', JSON.stringify(formatted) + '\n', { flag: 'wx' });

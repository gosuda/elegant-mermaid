import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { corpusFiles } from './wasm-parity.mjs';

test('corpus selection is sorted, tracked, and excludes out-of-scope fixtures', (t) => {
  const root = mkdtempSync(join(tmpdir(), 'emd-corpus-list-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  execFileSync('git', ['init', '--quiet', root]);
  for (const directory of ['flowchart', 'state', '_out-of-scope', 'termgfx']) {
    mkdirSync(join(root, 'corpus', directory), { recursive: true });
    writeFileSync(join(root, 'corpus', directory, 'b.mmd'), 'flowchart LR\n A --> B\n');
  }
  writeFileSync(join(root, 'corpus', 'flowchart', 'a.mmd'), 'flowchart LR\n C --> D\n');
  writeFileSync(join(root, 'corpus', 'flowchart', 'notes.txt'), 'not a fixture');
  execFileSync('git', ['-C', root, 'add', 'corpus']);
  writeFileSync(join(root, 'corpus', 'flowchart', 'untracked.mmd'), 'flowchart LR\n');
  assert.deepEqual(corpusFiles(root), ['corpus/flowchart/a.mmd', 'corpus/flowchart/b.mmd', 'corpus/state/b.mmd']);
});

test('an exported tree fails instead of silently reporting no fixtures', (t) => {
  const root = mkdtempSync(join(tmpdir(), 'emd-exported-tree-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  mkdirSync(join(root, 'corpus'));
  writeFileSync(join(root, 'corpus', 'untracked.mmd'), 'flowchart LR\n');
  assert.throws(() => corpusFiles(root), /cannot list tracked corpus fixtures/);
});

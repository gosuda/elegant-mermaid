import { spawnSync } from 'node:child_process';
import { writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { DEFAULT_SOURCE } from '../src/lib/defaults.ts';

const root = fileURLToPath(new URL('../../', import.meta.url));
const binary = fileURLToPath(new URL('../../bin/emd-go', import.meta.url));
const result = spawnSync(
  binary,
  ['render', '-e', 'text', '--charset', 'unicode', '--color', 'never', '-t', 'elegant-light'],
  {
    cwd: root,
    input: DEFAULT_SOURCE,
    encoding: 'utf8',
  },
);
if (result.error !== undefined) {
  throw result.error;
}
if (result.status !== 0 || result.stdout.trim() === '') {
  throw new Error(`Cannot render the initial playground sample: ${result.stderr}`);
}
writeFileSync(new URL('../src/lib/initial-text.txt', import.meta.url), result.stdout);

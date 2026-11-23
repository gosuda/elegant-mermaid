import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { execFile, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import path from 'node:path';

const execute = promisify(execFile);
const output = 'recovery-results';
const base = '4f18d67db8d2e7434cfbf6eed0627d6bb182923d';
const kinds = new Set(['flowchart', 'class', 'state', 'er', 'requirement', 'usecase', 'c4', 'agentflow', 'swimlane']);
const cellKinds = new Set(['agentflow', 'flowchart', 'state', 'swimlane']);
const overlayPaths = [
  'internal/layout/layered/compact.go',
  'internal/layout/layered/component.go',
  'internal/layout/layered/pipeline.go',
  'internal/layout/layered/port_alignment.go',
  'internal/layout/layered/port_alignment_test.go',
  'internal/layout/layered/port_compaction.go',
  'internal/layout/layered/portfolio.go',
].sort();

function writeJSON(file, value) {
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, JSON.stringify(value) + '\n', { flag: 'wx' });
}

function prepare() {
  const verdicts = JSON.parse(readFileSync('corpus/verdicts.json', 'utf8'));
  const fixtures = Object.keys(verdicts).filter((p) => verdicts[p].accept && kinds.has(verdicts[p].kind)).sort();
  const cells = fixtures.filter((p) => cellKinds.has(verdicts[p].kind));
  cells.push(
    'stability-recovery/cell/cell-label-minimal.mmd',
    'stability-recovery/cell/agent-tool-mask.mmd',
    'stability-recovery/cell/state-region-title-mask.mmd',
    'stability-recovery/cell/complete-bipartite.mmd',
  );
  mkdirSync(output, { recursive: true });
  writeFileSync(path.join(output, 'fixtures.txt'), fixtures.join('\n') + '\n', { flag: 'wx' });
  writeFileSync(path.join(output, 'cells.txt'), cells.join('\n') + '\n', { flag: 'wx' });
  console.log(JSON.stringify({ fixtures: fixtures.length, cellFixtures: cells.length, base }));
}

function apply() {
  const overlay = JSON.parse(readFileSync('stability-recovery/geometry-overlay.json', 'utf8'));
  if (overlay.base !== base || JSON.stringify(Object.keys(overlay.files).sort()) !== JSON.stringify(overlayPaths)) {
    throw new Error('unexpected geometry overlay base or write set');
  }
  execFileSync('git', ['diff', '--exit-code', base, '--', 'internal', 'crates'], { stdio: 'inherit' });
  for (const file of overlayPaths) {
    if (typeof overlay.files[file] !== 'string') throw new Error('missing overlay source: ' + file);
    writeFileSync(file, overlay.files[file]);
  }
  execFileSync('gofmt', ['-w', ...overlayPaths], { stdio: 'inherit' });
  console.log('Applied the isolated Go prototype; production branch is unchanged.');
}

async function json(binary, args) {
  const { stdout } = await execute(binary, args, { maxBuffer: 64 * 1024 * 1024, timeout: 120000 });
  return JSON.parse(stdout);
}

async function collect(stage, binary) {
  if (!['baseline', 'trial'].includes(stage) || !path.isAbsolute(binary)) throw new Error('expected stage and absolute executable');
  const fixtures = readFileSync(path.join(output, 'fixtures.txt'), 'utf8').trimEnd().split('\n');
  const rows = Array(fixtures.length);
  let next = 0;
  async function worker() {
    while (next < fixtures.length) {
      const i = next++;
      const fixture = fixtures[i];
      const ours = await json(binary, ['layout', '--metrics', fixture]);
      const dump = await json(binary, ['layout', '--profile', 'vector', fixture]);
      writeJSON(path.join(output, stage, fixture + '.ours.json'), dump);
      const dagre = await json(binary, ['layout', '--metrics', '--dump', path.join('corpus/.cache/quality', fixture + '.dagre.json')]);
      const elk = await json(binary, ['layout', '--metrics', '--dump', path.join('corpus/.cache/quality', fixture + '.elk.json')]);
      rows[i] = { path: fixture, ours, dagre, elk };
    }
  }
  await Promise.all(Array.from({ length: Math.min(4, fixtures.length) }, worker));
  writeJSON(path.join(output, stage + '-metrics.json'), rows);
  const total = { crossings: [0, 0, 0], cost: [0, 0, 0], exceptions: 0, hardFailures: 0 };
  const families = {};
  const hard = [];
  for (const row of rows) {
    const family = row.path.split('/')[1];
    const summary = families[family] ??= { fixtures: 0, exceptions: 0, hardFailures: 0, crossings: 0, cost: 0 };
    summary.fixtures++;
    for (const [i, key] of ['ours', 'dagre', 'elk'].entries()) {
      total.crossings[i] += row[key].crossings;
      total.cost[i] += row[key].soft_cost;
    }
    const exception = BigInt(row.ours.soft_cost) * 100n > BigInt(Math.min(row.dagre.soft_cost, row.elk.soft_cost)) * 120n;
    total.exceptions += Number(exception);
    summary.exceptions += Number(exception);
    summary.crossings += row.ours.crossings;
    summary.cost += row.ours.soft_cost;
    if (!row.ours.hard_ok) {
      total.hardFailures++;
      summary.hardFailures++;
      hard.push(row.path);
    }
  }
  const gates = {
    hardConstraints: total.hardFailures === 0,
    totalCrossings: total.crossings[0] <= Math.min(...total.crossings.slice(1)),
    totalSoftCost: total.cost[0] <= Math.min(...total.cost.slice(1)),
    exceptions: total.exceptions * 20 <= rows.length,
  };
  const summary = { stage, fixtures: rows.length, total, families, gates, hardFailures: hard };
  writeJSON(path.join(output, stage + '-summary.json'), summary);
  console.log(JSON.stringify(summary, null, 2));
}

const [mode, stage, binary] = process.argv.slice(2);
if (mode === 'prepare') prepare();
else if (mode === 'apply') apply();
else if (mode === 'collect') await collect(stage, binary);
else throw new Error('expected prepare, apply, or collect STAGE EXECUTABLE');

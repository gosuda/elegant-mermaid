import { createReadStream } from 'node:fs';
import { readFile, writeFile } from 'node:fs/promises';
import { createInterface } from 'node:readline';
import { basename } from 'node:path';

const kinds = new Set([
  'flowchart', 'class', 'state', 'er', 'requirement',
  'usecase', 'c4', 'agentflow', 'swimlane',
]);

function object(value, context) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    throw new Error('expected object: ' + context);
  }
  return value;
}

async function fixtureList(path) {
  const verdicts = object(JSON.parse(await readFile(path, 'utf8')), path);
  const paths = [];
  for (const [name, raw] of Object.entries(verdicts)) {
    const verdict = object(raw, name);
    if (typeof verdict.accept !== 'boolean') {
      throw new Error('missing acceptance verdict: ' + name);
    }
    if (verdict.accept && kinds.has(verdict.kind)) paths.push(name);
  }
  paths.sort();
  process.stdout.write(paths.length === 0 ? '' : paths.join('\n') + '\n');
}

function count(value, name) {
  if (!Number.isSafeInteger(value) || value < 0) {
    throw new Error('invalid nonnegative count: ' + name);
  }
  return value;
}

function family(path) {
  return path.startsWith('corpus/') ? path.split('/')[1] : 'repro';
}

function counters() {
  return {
    inputs: 0, errors: 0, dump_failures: 0, cell_failures: 0,
    refused_scenes: 0, conflict_scenes: 0,
    refused_clusters: 0, route_conflict_cells: 0,
  };
}

function addCounts(target, row) {
  target.inputs++;
  if (row.error) {
    target.errors++;
    return;
  }
  if (!row.valid) target.dump_failures++;
  if (row.refused_clusters > 0 || row.route_conflicts > 0) target.cell_failures++;
  if (row.refused_clusters > 0) target.refused_scenes++;
  if (row.route_conflicts > 0) target.conflict_scenes++;
  target.refused_clusters += row.refused_clusters;
  target.route_conflict_cells += row.route_conflicts;
}

function checkedReport(raw, number) {
  const row = object(raw, 'report line ' + number);
  if (typeof row.path !== 'string' || typeof row.valid !== 'boolean') {
    throw new Error('malformed report line ' + number);
  }
  count(row.refused_clusters, row.path + '.refused_clusters');
  count(row.route_conflicts, row.path + '.route_conflicts');
  if (row.error !== undefined && typeof row.error !== 'string') {
    throw new Error('invalid error field: ' + row.path);
  }
  return row;
}

async function summarize(path, tag) {
  const totals = counters();
  const byFamily = new Map();
  const failures = [];
  const errors = [];
  const seen = new Set();
  let number = 0;
  const reader = createInterface({ input: createReadStream(path), crlfDelay: Infinity });
  for await (const line of reader) {
    number++;
    if (line.trim() === '') continue;
    const row = checkedReport(JSON.parse(line), number);
    if (seen.has(row.path)) throw new Error('duplicate report: ' + row.path);
    seen.add(row.path);
    const kind = family(row.path);
    if (!byFamily.has(kind)) byFamily.set(kind, counters());
    addCounts(totals, row);
    addCounts(byFamily.get(kind), row);
    if (row.error) {
      errors.push({ path: row.path, error: row.error });
    } else if (!row.valid || row.refused_clusters > 0 || row.route_conflicts > 0) {
      failures.push({
        path: row.path,
        valid: row.valid,
        clause: row.clause ?? '',
        refused_clusters: row.refused_clusters,
        route_conflicts: row.route_conflicts,
        refused_labels: row.refused_labels ?? [],
      });
    }
  }
  if (totals.inputs === 0) throw new Error('empty probe report: ' + path);
  const summary = {
    tag, totals,
    families: Object.fromEntries([...byFamily.entries()].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)),
    failures, errors,
  };
  await writeFile(path + '.summary.json', JSON.stringify(summary, null, 2) + '\n');
  await writeFile(path + '.failed-paths.txt', [...failures, ...errors].map(row => row.path).sort().join('\n') + '\n');
  console.log('CELL_PROBE_TOTALS ' + JSON.stringify({ tag, totals, families: summary.families }));
  for (const row of failures) console.log('CELL_PROBE_FAILURE ' + JSON.stringify({ tag, ...row }));
  for (const row of errors) console.log('CELL_PROBE_ERROR ' + JSON.stringify({ tag, ...row }));
}

async function compare(beforePath, afterPath) {
  const before = object(JSON.parse(await readFile(beforePath, 'utf8')), beforePath);
  const after = object(JSON.parse(await readFile(afterPath, 'utf8')), afterPath);
  const bad = summary => new Map([...summary.failures, ...summary.errors].map(row => [row.path, row]));
  const oldBad = bad(before);
  const newBad = bad(after);
  const output = {
    before: before.tag, after: after.tag,
    regressions: [...newBad.keys()].filter(path => !oldBad.has(path)).sort(),
    repaired: [...oldBad.keys()].filter(path => !newBad.has(path)).sort(),
    changed: [...oldBad.keys()].filter(path => newBad.has(path))
      .filter(path => JSON.stringify(oldBad.get(path)) !== JSON.stringify(newBad.get(path)))
      .map(path => ({ path, before: oldBad.get(path), after: newBad.get(path) })),
  };
  console.log('CELL_PROBE_COMPARISON ' + JSON.stringify(output));
}

const [mode, first, second] = process.argv.slice(2);
if (mode && first === undefined) {
  await summarize(mode, basename(mode).replace(/\.jsonl$/, ''));
} else if (mode === 'list' && first && second === undefined) {
  await fixtureList(first);
} else if (mode === 'summarize' && first && second) {
  await summarize(first, second);
} else if (mode === 'compare' && first && second) {
  await compare(first, second);
} else {
  throw new Error('usage: node summarize.mjs list VERDICTS | summarize JSONL TAG | compare BEFORE_SUMMARY AFTER_SUMMARY');
}

import { readFileSync, writeFileSync } from 'node:fs';

const [file] = process.argv.slice(2);
if (!file) throw new Error('expected probe JSONL path');
const rows = readFileSync(file, 'utf8').trimEnd().split('\n').filter(Boolean).map((line) => JSON.parse(line));
const failures = rows.filter((r) => r.error || !r.valid || r.refused_clusters || r.route_conflicts);
const families = {};
for (const row of rows) {
  const kind = row.path.startsWith('corpus/') ? row.path.split('/')[1] : 'repro';
  const family = families[kind] ??= { fixtures: 0, errors: 0, invalid: 0, refused: 0, conflicts: 0 };
  family.fixtures++;
  family.errors += Number(Boolean(row.error));
  family.invalid += Number(!row.error && !row.valid);
  family.refused += Number(row.refused_clusters > 0);
  family.conflicts += Number(row.route_conflicts > 0);
}
const summary = {
  input: file, fixtures: rows.length, failures: failures.length, families,
  rows: failures.map(({ dump, text, ...rest }) => rest),
};
writeFileSync(file + '.summary.json', JSON.stringify(summary) + '\n', { flag: 'wx' });
console.log(JSON.stringify(summary, null, 2));

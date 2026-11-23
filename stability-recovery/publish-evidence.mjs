import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';

const [directory] = process.argv.slice(2);
const repository = process.env.GITHUB_REPOSITORY;
const token = process.env.GH_TOKEN;
const parent = process.env.GITHUB_SHA;
if (repository !== 'gosuda/elegant-mermaid' || !token || !/^[0-9a-f]{40}$/.test(parent ?? '')) {
  throw new Error('expected this repository, a job token, and the exact experiment commit');
}
const candidates = [
  path.join(directory, 'recovery-results'),
  path.join(directory, 'elegant-mermaid/elegant-mermaid/recovery-results'),
];
const root = candidates.find((p) => existsSync(p));
if (!root) throw new Error('artifact has no recovery-results directory');

async function request(endpoint, value) {
  const response = await fetch('https://api.github.com/repos/' + repository + '/git/' + endpoint, {
    method: 'POST',
    headers: { authorization: 'Bearer ' + token, accept: 'application/vnd.github+json', 'content-type': 'application/json', 'x-github-api-version': '2022-11-28' },
    body: JSON.stringify(value),
  });
  if (!response.ok) throw new Error('GitHub ' + endpoint + ' returned ' + response.status + ': ' + await response.text());
  return response.json();
}

const documents = [];
const index = { experiment: parent, run: process.env.GITHUB_RUN_ID, summaries: [], metricChunks: [], sceneChunks: [], cellChunks: [] };
function add(name, value) {
  documents.push({ name, content: JSON.stringify(value) + '\n' });
}
function chunks(type, stage, rows, limit = 40) {
  const entries = [];
  for (let i = 0; i < rows.length; i += limit) {
    const name = type + '/' + stage + '-' + String(i / limit).padStart(3, '0') + '.json';
    const part = rows.slice(i, i + limit);
    add(name, part);
    entries.push({ file: name, paths: part.map((r) => r.path) });
  }
  return entries;
}
for (const stage of ['baseline', 'trial']) {
  for (const name of [stage + '-summary.json', 'cell-' + stage + '.jsonl.summary.json', 'compound-' + stage + '.json']) {
    const file = path.join(root, name);
    if (!existsSync(file)) continue;
    add('summaries/' + name, JSON.parse(readFileSync(file, 'utf8')));
    index.summaries.push('summaries/' + name);
  }
  const metricsFile = path.join(root, stage + '-metrics.json');
  if (existsSync(metricsFile)) {
    const rows = JSON.parse(readFileSync(metricsFile, 'utf8'));
    index.metricChunks.push(...chunks('metrics', stage, rows, 80));
    const scenes = [];
    for (const row of rows) {
      const file = path.join(root, stage, row.path + '.ours.json');
      if (existsSync(file)) scenes.push({ path: row.path, dump: JSON.parse(readFileSync(file, 'utf8')) });
    }
    index.sceneChunks.push(...chunks('scenes', stage, scenes, 25));
  }
  const cells = path.join(root, 'cell-' + stage + '.jsonl');
  if (existsSync(cells)) {
    const failures = readFileSync(cells, 'utf8').trimEnd().split('\n').filter(Boolean).map((s) => JSON.parse(s))
      .filter((r) => r.error || !r.valid || r.refused_clusters || r.route_conflicts || r.path.startsWith('stability-recovery/'));
    index.cellChunks.push(...chunks('cells', stage, failures, 8));
  }
}
for (const name of readdirSync(root).filter((n) => n.startsWith('compound-') && n.endsWith('.json'))) {
  const target = 'summaries/' + name;
  if (index.summaries.includes(target)) continue;
  add(target, JSON.parse(readFileSync(path.join(root, name), 'utf8')));
  index.summaries.push(target);
}
add('index.json', index);
let next = 0;
const tree = Array(documents.length);
async function worker() {
  while (next < documents.length) {
    const i = next++;
    const document = documents[i];
    const blob = await request('blobs', { content: document.content, encoding: 'utf-8' });
    tree[i] = { path: document.name, mode: '100644', type: 'blob', sha: blob.sha };
  }
}
await Promise.all(Array.from({ length: Math.min(4, documents.length) }, worker));
const result = await request('trees', { tree });
const commit = await request('commits', { message: 'Preserve stabilization experiment evidence', tree: result.sha, parents: [parent] });
console.log('EVIDENCE_COMMIT ' + commit.sha);
console.log('EVIDENCE_TREE ' + result.sha);
console.log('EVIDENCE_FILES ' + documents.length);
console.log('No branch or tag references were changed.');

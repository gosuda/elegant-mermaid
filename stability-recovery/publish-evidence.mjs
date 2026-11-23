import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { setTimeout as pause } from 'node:timers/promises';

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
  for (let attempt = 0; attempt < 5; attempt++) {
    const response = await fetch('https://api.github.com/repos/' + repository + '/git/' + endpoint, {
      method: 'POST',
      headers: { authorization: 'Bearer ' + token, accept: 'application/vnd.github+json', 'content-type': 'application/json', 'x-github-api-version': '2022-11-28' },
      body: JSON.stringify(value),
    });
    if (response.ok) {
      const result = await response.json();
      await pause(1250);
      return result;
    }
    const message = await response.text();
    const limited = response.status === 429 || response.status === 403 && message.includes('rate limit');
    if (!limited || attempt === 4) throw new Error('GitHub ' + endpoint + ' returned ' + response.status + ': ' + message);
    const retryAfter = Number(response.headers.get('retry-after') ?? '60');
    const seconds = Number.isFinite(retryAfter) && retryAfter > 0 ? retryAfter : 60;
    console.log('Rate limited; respecting a retry delay of ' + seconds + ' seconds.');
    await pause(seconds * 1000);
  }
  throw new Error('request attempts exhausted');
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
const familyRoot = path.join(directory, 'family');
const patched = path.join(familyRoot, 'family-patched-sources.json');
if (existsSync(patched)) {
  const sources = JSON.parse(readFileSync(patched, 'utf8'));
  for (const [file, content] of Object.entries(sources)) {
    if (!file.startsWith('internal/layout/') && !file.startsWith('crates/elegant-mermaid/')) throw new Error('unexpected patched source path');
    documents.push({ name: 'patched/' + file, content });
  }
}
for (const stage of ['family', 'detour']) {
  const file = path.join(familyRoot, 'cell-' + stage + '.jsonl');
  if (!existsSync(file)) continue;
  const rows = readFileSync(file, 'utf8').trimEnd().split('\n').filter(Boolean).map((s) => JSON.parse(s))
    .filter((r) => r.error || !r.valid || r.refused_clusters || r.route_conflicts || r.path.startsWith('stability-recovery/'));
  index.cellChunks.push(...chunks('cells', stage, rows, 8));
  const summary = file + '.summary.json';
  if (existsSync(summary)) {
    const name = 'summaries/cell-' + stage + '.json';
    add(name, JSON.parse(readFileSync(summary, 'utf8')));
    index.summaries.push(name);
  }
}
add('index.json', index);
const priority = (name) => name === 'index.json' ? 0 : name.startsWith('summaries/') ? 1 : name.startsWith('patched/') ? 2 : name.startsWith('cells/') ? 3 : name.startsWith('metrics/') ? 4 : 5;
documents.sort((a, b) => priority(a.name) - priority(b.name) || a.name.localeCompare(b.name));
let next = 0;
const tree = Array(documents.length);
async function worker() {
  while (next < documents.length) {
    const i = next++;
    const document = documents[i];
    const blob = await request('blobs', { content: document.content, encoding: 'utf-8' });
    tree[i] = { path: document.name, mode: '100644', type: 'blob', sha: blob.sha };
    console.log('EVIDENCE_BLOB ' + JSON.stringify({ file: document.name, sha: blob.sha }));
  }
}
await worker();
const result = await request('trees', { tree });
const commit = await request('commits', { message: 'Preserve stabilization experiment evidence', tree: result.sha, parents: [parent] });
console.log('EVIDENCE_COMMIT ' + commit.sha);
console.log('EVIDENCE_TREE ' + result.sha);
console.log('EVIDENCE_FILES ' + documents.length);
console.log('No branch or tag references were changed.');

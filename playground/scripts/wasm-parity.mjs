#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import vm from 'node:vm';

const root = fileURLToPath(new URL('../../', import.meta.url));
const wasmDir = join(root, 'playground', 'static', 'wasm');
const corpusDir = join(root, 'corpus');
const binaries = { 'emd-go': join(root, 'bin', 'emd-go'), 'emd-rs': join(root, 'bin', 'emd-rs') };

const OPS = [
  { name: 'check', args: ['check', '--output-format', 'json', '-'] },
  {
    name: 'render_text',
    args: ['render', '-e', 'text', '--charset', 'unicode', '--color', 'never', '-t', 'elegant-light'],
  },
  { name: 'layout', args: ['layout', '--profile', 'vector', '--stage', 'layout'] },
];

const PAIRS = [
  ['go-wasm', 'emd-go'],
  ['rust-wasm', 'emd-rs'],
  ['go-wasm', 'rust-wasm'],
  ['emd-go', 'emd-rs'],
];

const MAX_REPORTED = 20;
const CORPUS_PATHSPEC = ['corpus/*.mmd', ':!corpus/_out-of-scope/*', ':!corpus/termgfx/*'];

function fail(message) {
  process.stderr.write(`wasm-parity: ${message}\n`);
  process.exit(2);
}

function parseEvery(argv) {
  const index = argv.indexOf('--every');
  if (index < 0) {
    return 10;
  }
  const value = Number(argv[index + 1]);
  if (!Number.isInteger(value) || value < 1) {
    fail('--every needs a positive integer');
  }
  return value;
}

function corpusFiles() {
  const listed = spawnSync('git', ['ls-files', '-z', '--', ...CORPUS_PATHSPEC], { cwd: root, maxBuffer: 1 << 26 });
  if (listed.error !== undefined || listed.status !== 0) {
    fail(`git ls-files failed: ${listed.error ?? listed.stderr.toString('utf8').trim()}`);
  }
  return listed.stdout
    .toString('utf8')
    .split('\0')
    .filter((path) => path !== '')
    .sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)));
}

function sleep(ms) {
  const { promise, resolve } = Promise.withResolvers();
  setTimeout(resolve, ms);
  return promise;
}

async function loadGo() {
  const loader = readFileSync(join(wasmDir, 'wasm_exec.js'), 'utf8');
  vm.runInThisContext(loader, { filename: 'wasm_exec.js' });
  const go = new globalThis.Go();
  const bytes = readFileSync(join(wasmDir, 'emd-go.wasm'));
  const { instance } = await WebAssembly.instantiate(bytes, go.importObject);
  go.run(instance).then(
    () => fail('the Go runtime exited'),
    (error) => fail(`the Go runtime stopped: ${error}`),
  );
  for (let waited = 0; typeof globalThis.emdCall !== 'function'; waited += 5) {
    if (waited > 10_000) {
      fail('emdCall was not registered by the Go engine within 10 seconds');
    }
    await sleep(5);
  }
  const call = globalThis.emdCall;
  return (op, source, optionsJson) => call(op, source, optionsJson);
}

async function loadRust() {
  const module = await import(pathToFileURL(join(wasmDir, 'emd-rs', 'elegant_mermaid_wasm.js')).href);
  const bytes = readFileSync(join(wasmDir, 'emd-rs', 'elegant_mermaid_wasm_bg.wasm'));
  await module.default({ module_or_path: bytes });
  return (op, source, optionsJson) => module.emdCall(op, source, optionsJson);
}

function runWasm(call, op, source) {
  try {
    const response = JSON.parse(call(op, source, '{}'));
    if (typeof response.ok !== 'boolean' || typeof response.output !== 'string') {
      return { error: 'response lacks ok or output' };
    }
    return { ok: response.ok, output: Buffer.from(response.output, 'utf8') };
  } catch (error) {
    return { error: String(error) };
  }
}

function runNative(binary, args, input, cwd) {
  const result = spawnSync(binary, args, { input, cwd, maxBuffer: 1 << 28 });
  if (result.error) {
    return { error: String(result.error) };
  }
  return { ok: result.status === 0, output: result.stdout };
}

function samePair(a, b) {
  if (a.error !== undefined || b.error !== undefined) {
    return false;
  }
  return a.ok === b.ok && a.output.equals(b.output);
}

function describeResult(result) {
  if (result.error !== undefined) {
    return `error: ${result.error}`;
  }
  const text = result.output.toString('utf8');
  return `ok=${result.ok} ${result.output.length} bytes ${JSON.stringify(text.slice(0, 80))}`;
}

async function main() {
  const every = parseEvery(process.argv.slice(2));
  for (const [name, path] of Object.entries(binaries)) {
    if (!existsSync(path)) {
      fail(`${name} is missing at ${path}; run just build`);
    }
  }
  for (const path of [
    join(wasmDir, 'wasm_exec.js'),
    join(wasmDir, 'emd-go.wasm'),
    join(wasmDir, 'emd-rs', 'elegant_mermaid_wasm.js'),
    join(wasmDir, 'emd-rs', 'elegant_mermaid_wasm_bg.wasm'),
  ]) {
    if (!existsSync(path)) {
      fail(`${path} is missing; run just playground-wasm`);
    }
  }
  if (!existsSync(corpusDir)) {
    fail(`${corpusDir} is missing`);
  }

  const goCall = await loadGo();
  const rustCall = await loadRust();
  const files = corpusFiles().filter((_, index) => index % every === 0);
  const scratch = mkdtempSync(join(tmpdir(), 'emd-wasm-parity-'));
  let differences = 0;
  let reported = 0;
  try {
    for (const file of files) {
      const text = new TextDecoder().decode(readFileSync(join(root, file)));
      const input = Buffer.from(text, 'utf8');
      for (const { name, args } of OPS) {
        const results = {
          'go-wasm': runWasm(goCall, name, text),
          'rust-wasm': runWasm(rustCall, name, text),
          'emd-go': runNative(binaries['emd-go'], args, input, scratch),
          'emd-rs': runNative(binaries['emd-rs'], args, input, scratch),
        };
        const broken = PAIRS.filter(([a, b]) => !samePair(results[a], results[b]));
        if (broken.length === 0) {
          continue;
        }
        differences += 1;
        if (reported < MAX_REPORTED) {
          reported += 1;
          process.stderr.write(`difference: ${file} ${name}\n`);
          for (const [a, b] of broken) {
            process.stderr.write(
              `  ${a} vs ${b}\n    ${a}: ${describeResult(results[a])}\n    ${b}: ${describeResult(results[b])}\n`,
            );
          }
        }
      }
    }
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
  process.stdout.write(`compared ${files.length}, differences ${differences}\n`);
  process.exit(differences > 0 ? 1 : 0);
}

main().catch((error) => fail(String(error?.stack ?? error)));

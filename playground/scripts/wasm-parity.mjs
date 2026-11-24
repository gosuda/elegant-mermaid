#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
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

const CONFIG_OPS = [...OPS, { name: 'render_svg', args: ['render', '-e', 'svg', '-t', 'elegant-light'] }];
const CONFIG_FIXTURES = [
  ['flowchart', 'flowchart LR\nA[Alphabetic label] --> B\n'],
  ['class', 'classDiagram\nclass A {\n+longAlphabeticalMemberNameUsedForMeasurement\n}\n'],
  ['er', 'erDiagram\nA {\nstring longAlphabeticalAttributeNameUsedForMeasurement\n}\n'],
  ['requirement', 'requirementDiagram\nrequirement R {\ntext: long alphabetical field text used for measurement\n}\n'],
].map(([kind, body]) => ({
  file: `configured-font/${kind}`,
  text: `---\nconfig:\n  fontFamily: 'Custom & <Font>'\n---\n${body}`,
  font: 'Custom & <Font>',
  ops: CONFIG_OPS,
  accepted: true,
}));
CONFIG_FIXTURES.push({
  file: 'configured-aliases',
  text: '---\nconfig:\n  quadrantChart: {typo: true}\n  wardley-beta: {typo: true}\n---\nflowchart\nA\n',
  ops: OPS,
  accepted: true,
});

const PAIRS = [
  ['go-wasm', 'emd-go'],
  ['rust-wasm', 'emd-rs'],
  ['go-wasm', 'rust-wasm'],
  ['emd-go', 'emd-rs'],
];

const MAX_REPORTED = 20;

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

export function corpusFiles(repositoryRoot = root) {
  const result = spawnSync(
    'git',
    ['ls-files', '-z', '--', 'corpus/*.mmd', ':!corpus/_out-of-scope/*', ':!corpus/termgfx/*'],
    { cwd: repositoryRoot, encoding: 'utf8', maxBuffer: 1 << 24 },
  );
  if (result.error !== undefined || result.status !== 0) {
    throw new Error(`cannot list tracked corpus fixtures: ${result.error?.message ?? result.stderr.trim()}`);
  }
  return result.stdout
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

function fixtureErrors(fixture, operation, results) {
  const errors = [];
  for (const [engine, result] of Object.entries(results)) {
    if (fixture.accepted && (result.error !== undefined || !result.ok)) {
      errors.push(`${engine}: expected accepted configured diagram`);
      continue;
    }
    if (fixture.font !== undefined && operation === 'layout') {
      try {
        if (JSON.parse(result.output.toString('utf8')).options?.fontFamily !== fixture.font) {
          errors.push(`${engine}: configured font is absent from the layout`);
        }
      } catch (error) {
        errors.push(`${engine}: invalid configured layout: ${String(error)}`);
      }
    }
  }
  return errors;
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
  const fixtures = [
    ...files.map((file) => ({ file, text: new TextDecoder().decode(readFileSync(join(root, file))), ops: OPS })),
    ...CONFIG_FIXTURES,
  ];
  const scratch = mkdtempSync(join(tmpdir(), 'emd-wasm-parity-'));
  let differences = 0;
  let reported = 0;
  try {
    for (const fixture of fixtures) {
      const { file, text } = fixture;
      const input = Buffer.from(text, 'utf8');
      for (const { name, args } of fixture.ops) {
        const results = {
          'go-wasm': runWasm(goCall, name, text),
          'rust-wasm': runWasm(rustCall, name, text),
          'emd-go': runNative(binaries['emd-go'], args, input, scratch),
          'emd-rs': runNative(binaries['emd-rs'], args, input, scratch),
        };
        const broken = PAIRS.filter(([a, b]) => !samePair(results[a], results[b]));
        const errors = fixtureErrors(fixture, name, results);
        if (broken.length === 0 && errors.length === 0) {
          continue;
        }
        differences += 1;
        if (reported < MAX_REPORTED) {
          reported += 1;
          process.stderr.write(`difference: ${file} ${name}\n`);
          for (const error of errors) {
            process.stderr.write(`  ${error}\n`);
          }
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
  process.stdout.write(`compared ${fixtures.length}, differences ${differences}\n`);
  process.exit(differences > 0 ? 1 : 0);
}

if (process.argv[1] !== undefined && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((error) => fail(String(error?.stack ?? error)));
}

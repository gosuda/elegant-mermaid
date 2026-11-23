import type { FromWorker, ToWorker } from './protocol';

type EmdCall = (op: string, source: string, optionsJson: string) => string | Promise<string>;

interface GoRuntime {
  importObject: WebAssembly.Imports;
  run(instance: WebAssembly.Instance): Promise<void>;
}

interface RustModule {
  default(options: { module_or_path: Uint8Array }): Promise<unknown>;
  emdCall: EmdCall;
}

interface WorkerScope {
  postMessage(message: FromWorker): void;
  onmessage: ((event: MessageEvent<ToWorker>) => void) | null;
  importScripts(...urls: string[]): void;
}

const scope = self as unknown as WorkerScope;
const globals = globalThis as unknown as { Go?: new () => GoRuntime; emdCall?: unknown };

const EMD_CALL_WAIT_MS = 10_000;

let call: EmdCall | null = null;

function post(message: FromWorker): void {
  scope.postMessage(message);
}

function messageOf(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}

async function fetchBytes(url: string): Promise<Uint8Array<ArrayBuffer>> {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`${url} answered HTTP ${response.status}`);
  }
  const header = response.headers.get('Content-Length');
  const total = header !== null && /^\d+$/.test(header) ? Number(header) : null;
  post({ type: 'progress', loaded: 0, total });
  if (response.body === null) {
    const bytes = new Uint8Array(await response.arrayBuffer());
    post({ type: 'progress', loaded: bytes.byteLength, total });
    return bytes;
  }
  const reader = response.body.getReader();
  const chunks: Uint8Array[] = [];
  let loaded = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) {
      break;
    }
    chunks.push(value);
    loaded += value.byteLength;
    post({ type: 'progress', loaded, total });
  }
  const bytes = new Uint8Array(loaded);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}

async function waitForEmdCall(): Promise<EmdCall> {
  const deadline = Date.now() + EMD_CALL_WAIT_MS;
  for (;;) {
    const candidate = globals.emdCall;
    if (typeof candidate === 'function') {
      return candidate as EmdCall;
    }
    if (Date.now() > deadline) {
      throw new Error('emdCall was not registered within 10 seconds');
    }
    await new Promise<void>((resolve) => {
      setTimeout(resolve, 5);
    });
  }
}

async function loadGo(loader: string, wasm: string): Promise<void> {
  scope.importScripts(loader);
  const GoRuntimeClass = globals.Go;
  if (typeof GoRuntimeClass !== 'function') {
    throw new Error('wasm_exec.js did not define Go');
  }
  const bytes = await fetchBytes(wasm);
  const go = new GoRuntimeClass();
  const { instance } = await WebAssembly.instantiate(bytes, go.importObject);
  go.run(instance).then(
    () => {
      call = null;
      post({ type: 'failed', message: 'the Go runtime exited' });
    },
    (error: unknown) => {
      call = null;
      post({ type: 'failed', message: messageOf(error) });
    },
  );
  call = await waitForEmdCall();
}

async function loadRust(loader: string, wasm: string): Promise<void> {
  const module = (await import(/* @vite-ignore */ loader)) as RustModule;
  const bytes = await fetchBytes(wasm);
  await module.default({ module_or_path: bytes });
  call = module.emdCall;
}

async function start(engine: 'go' | 'rust', loader: string, wasm: string): Promise<void> {
  try {
    if (engine === 'go') {
      await loadGo(loader, wasm);
    } else {
      await loadRust(loader, wasm);
    }
    post({ type: 'ready' });
  } catch (error) {
    post({ type: 'failed', message: messageOf(error) });
  }
}

async function handleCall(
  id: number,
  revision: number,
  op: string,
  source: string,
  optionsJson: string,
): Promise<void> {
  if (call === null) {
    post({ type: 'call-failed', id, revision, message: 'the engine is not ready' });
    return;
  }
  try {
    const response = await call(op, source, optionsJson);
    post({ type: 'result', id, revision, response });
  } catch (error) {
    post({ type: 'call-failed', id, revision, message: messageOf(error) });
  }
}

scope.onmessage = (event) => {
  const message = event.data;
  if (message.type === 'init') {
    void start(message.engine, message.loader, message.wasm);
  } else {
    void handleCall(message.id, message.revision, message.op, message.source, message.optionsJson);
  }
};

import { type EngineId, type FromWorker, LOAD_TIMEOUT_MS, type Op, type ToWorker } from './protocol';

export type EngineState = 'idle' | 'loading' | 'ready' | 'error';

export interface EngineSnapshot {
  state: EngineState;
  loaded: number;
  total: number | null;
  message: string;
}

export interface WorkerLike {
  postMessage(message: ToWorker): void;
  terminate(): void;
  onmessage: ((event: MessageEvent<FromWorker>) => void) | null;
  onerror: ((event: ErrorEvent) => void) | null;
}

export interface EngineClientOptions {
  id: EngineId;
  createWorker: () => WorkerLike;
  loader: string;
  wasm: string;
  timeoutMs?: number;
}

interface Pending {
  resolve(response: string): void;
  reject(error: Error): void;
}

type Listener = (snapshot: EngineSnapshot) => void;

export const IDLE_SNAPSHOT: EngineSnapshot = { state: 'idle', loaded: 0, total: null, message: '' };

export class EngineClient {
  readonly id: EngineId;
  readonly #createWorker: () => WorkerLike;
  readonly #loader: string;
  readonly #wasm: string;
  readonly #timeoutMs: number;
  readonly #listeners = new Set<Listener>();
  readonly #pending = new Map<number, Pending>();
  #snapshot: EngineSnapshot = IDLE_SNAPSHOT;
  #worker: WorkerLike | null = null;
  #timer: ReturnType<typeof setTimeout> | null = null;
  #nextCall = 1;

  constructor(options: EngineClientOptions) {
    this.id = options.id;
    this.#createWorker = options.createWorker;
    this.#loader = options.loader;
    this.#wasm = options.wasm;
    this.#timeoutMs = options.timeoutMs ?? LOAD_TIMEOUT_MS;
  }

  get snapshot(): EngineSnapshot {
    return this.#snapshot;
  }

  subscribe(listener: Listener): () => void {
    this.#listeners.add(listener);
    return () => {
      this.#listeners.delete(listener);
    };
  }

  start(): void {
    if (this.#snapshot.state === 'idle') {
      this.#begin();
    }
  }

  retry(): void {
    if (this.#snapshot.state === 'error') {
      this.#begin();
    }
  }

  call(op: Op, source: string, optionsJson: string, revision: number): Promise<string> {
    const worker = this.#worker;
    if (this.#snapshot.state !== 'ready' || worker === null) {
      return Promise.reject(new Error('the engine is not ready'));
    }
    const id = this.#nextCall++;
    const { promise, resolve, reject } = Promise.withResolvers<string>();
    this.#pending.set(id, { resolve, reject });
    worker.postMessage({ type: 'call', id, revision, op, source, optionsJson });
    return promise;
  }

  dispose(): void {
    this.#stopWorker();
    this.#rejectPending('the engine was disposed');
    this.#listeners.clear();
  }

  #begin(): void {
    this.#stopWorker();
    const worker = this.#createWorker();
    this.#worker = worker;
    this.#set({ state: 'loading', loaded: 0, total: null, message: '' });
    worker.onmessage = (event) => {
      if (this.#worker === worker) {
        this.#handle(event.data);
      }
    };
    worker.onerror = (event) => {
      if (this.#worker === worker) {
        this.#fail(event.message || 'the worker stopped with an error');
      }
    };
    this.#timer = setTimeout(() => {
      this.#fail(`timed out after ${Math.round(this.#timeoutMs / 1000)} seconds`);
    }, this.#timeoutMs);
    worker.postMessage({ type: 'init', engine: this.id, loader: this.#loader, wasm: this.#wasm });
  }

  #handle(message: FromWorker): void {
    switch (message.type) {
      case 'progress':
        if (this.#snapshot.state === 'loading') {
          this.#set({ ...this.#snapshot, loaded: message.loaded, total: message.total });
        }
        return;
      case 'ready':
        this.#clearTimer();
        this.#set({ ...this.#snapshot, state: 'ready', message: '' });
        return;
      case 'failed':
        this.#fail(message.message);
        return;
      case 'result': {
        const pending = this.#pending.get(message.id);
        this.#pending.delete(message.id);
        pending?.resolve(message.response);
        return;
      }
      case 'call-failed': {
        const pending = this.#pending.get(message.id);
        this.#pending.delete(message.id);
        pending?.reject(new Error(message.message));
        return;
      }
    }
  }

  #fail(message: string): void {
    this.#stopWorker();
    this.#rejectPending(message);
    this.#set({ state: 'error', loaded: 0, total: null, message });
  }

  #stopWorker(): void {
    this.#clearTimer();
    const worker = this.#worker;
    this.#worker = null;
    if (worker !== null) {
      worker.onmessage = null;
      worker.onerror = null;
      worker.terminate();
    }
  }

  #clearTimer(): void {
    if (this.#timer !== null) {
      clearTimeout(this.#timer);
      this.#timer = null;
    }
  }

  #rejectPending(message: string): void {
    const pending = [...this.#pending.values()];
    this.#pending.clear();
    for (const entry of pending) {
      entry.reject(new Error(message));
    }
  }

  #set(snapshot: EngineSnapshot): void {
    this.#snapshot = snapshot;
    for (const listener of this.#listeners) {
      listener(snapshot);
    }
  }
}

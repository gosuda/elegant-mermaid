import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { EngineClient, type EngineSnapshot, type WorkerLike } from './engine-client';
import type { FromWorker, ToWorker } from './protocol';

class FakeWorker implements WorkerLike {
  sent: ToWorker[] = [];
  terminated = false;
  onmessage: ((event: MessageEvent<FromWorker>) => void) | null = null;
  onerror: ((event: ErrorEvent) => void) | null = null;
  postMessage(message: ToWorker): void {
    this.sent.push(message);
  }
  terminate(): void {
    this.terminated = true;
  }
  emit(message: FromWorker): void {
    this.onmessage?.({ data: message } as MessageEvent<FromWorker>);
  }
}

function setup(timeoutMs?: number) {
  const workers: FakeWorker[] = [];
  const client = new EngineClient({
    id: 'go',
    createWorker: () => {
      const worker = new FakeWorker();
      workers.push(worker);
      return worker;
    },
    loader: '/wasm/wasm_exec.js',
    wasm: '/wasm/emd-go.wasm',
    timeoutMs,
  });
  const states: EngineSnapshot[] = [];
  client.subscribe((snapshot) => states.push(snapshot));
  return { client, workers, states };
}

describe('EngineClient', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });
  afterEach(() => {
    vi.useRealTimers();
  });

  it('starts idle and sends its built URLs as the first message', () => {
    const { client, workers } = setup();
    expect(client.snapshot.state).toBe('idle');
    client.start();
    expect(client.snapshot.state).toBe('loading');
    expect(workers[0]?.sent[0]).toEqual({
      type: 'init',
      engine: 'go',
      loader: '/wasm/wasm_exec.js',
      wasm: '/wasm/emd-go.wasm',
    });
  });

  it('records progress with a total or null and becomes ready', () => {
    const { client, workers } = setup();
    client.start();
    workers[0]?.emit({ type: 'progress', loaded: 10, total: 100 });
    expect(client.snapshot).toMatchObject({ state: 'loading', loaded: 10, total: 100 });
    workers[0]?.emit({ type: 'progress', loaded: 50, total: null });
    expect(client.snapshot).toMatchObject({ loaded: 50, total: null });
    workers[0]?.emit({ type: 'ready' });
    expect(client.snapshot.state).toBe('ready');
    vi.advanceTimersByTime(60_000);
    expect(client.snapshot.state).toBe('ready');
  });

  it('answers a call with the reply carrying the same id and revision', async () => {
    const { client, workers } = setup();
    client.start();
    workers[0]?.emit({ type: 'ready' });
    const answer = client.call('check', 'src', '{}', 7);
    const sent = workers[0]?.sent[1];
    expect(sent).toMatchObject({ type: 'call', revision: 7, op: 'check', source: 'src', optionsJson: '{}' });
    if (sent?.type !== 'call') {
      throw new Error('expected a call message');
    }
    workers[0]?.emit({ type: 'result', id: sent.id, revision: 7, response: '{"ok":true}' });
    await expect(answer).resolves.toBe('{"ok":true}');
  });

  it('rejects a call that the worker reports as failed', async () => {
    const { client, workers } = setup();
    client.start();
    workers[0]?.emit({ type: 'ready' });
    const answer = client.call('layout', 's', '{}', 1);
    const sent = workers[0]?.sent[1];
    if (sent?.type !== 'call') {
      throw new Error('expected a call message');
    }
    workers[0]?.emit({ type: 'call-failed', id: sent.id, revision: 1, message: 'boom' });
    await expect(answer).rejects.toThrow('boom');
  });

  it('refuses calls before the engine is ready', async () => {
    const { client } = setup();
    await expect(client.call('check', 's', '{}', 1)).rejects.toThrow('not ready');
  });

  it('fails after 30 seconds and terminates the worker', () => {
    const { client, workers } = setup();
    client.start();
    vi.advanceTimersByTime(29_999);
    expect(client.snapshot.state).toBe('loading');
    vi.advanceTimersByTime(1);
    expect(client.snapshot).toMatchObject({ state: 'error', message: 'timed out after 30 seconds' });
    expect(workers[0]?.terminated).toBe(true);
  });

  it('fails when the worker reports a failure or an error event', () => {
    const first = setup();
    first.client.start();
    first.workers[0]?.emit({ type: 'failed', message: 'HTTP 404' });
    expect(first.client.snapshot).toMatchObject({ state: 'error', message: 'HTTP 404' });
    const second = setup();
    second.client.start();
    second.workers[0]?.onerror?.({ message: 'Script error' } as ErrorEvent);
    expect(second.client.snapshot).toMatchObject({ state: 'error', message: 'Script error' });
  });

  it('rejects pending calls when the engine fails', async () => {
    const { client, workers } = setup();
    client.start();
    workers[0]?.emit({ type: 'ready' });
    const answer = client.call('check', 's', '{}', 1);
    workers[0]?.emit({ type: 'failed', message: 'the Go runtime exited' });
    await expect(answer).rejects.toThrow('the Go runtime exited');
  });

  it('retries with a new worker and ignores the old one', () => {
    const { client, workers } = setup();
    client.start();
    workers[0]?.emit({ type: 'failed', message: 'HTTP 500' });
    client.retry();
    expect(workers).toHaveLength(2);
    expect(client.snapshot.state).toBe('loading');
    workers[0]?.emit({ type: 'ready' });
    expect(client.snapshot.state).toBe('loading');
    workers[1]?.emit({ type: 'ready' });
    expect(client.snapshot.state).toBe('ready');
  });

  it('does not retry unless it failed', () => {
    const { client, workers } = setup();
    client.retry();
    client.start();
    client.retry();
    expect(workers).toHaveLength(1);
  });
});

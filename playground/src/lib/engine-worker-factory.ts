import type { WorkerLike } from './engine-client';

export function createEngineWorker(): WorkerLike {
  return new Worker(new URL('./engine.worker.ts', import.meta.url), { type: 'classic' });
}

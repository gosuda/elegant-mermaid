export type EngineId = 'go' | 'rust';

export const ENGINE_IDS: readonly EngineId[] = ['go', 'rust'];

export const ENGINE_NAME: Record<EngineId, string> = { go: 'Go', rust: 'Rust' };

export type Op = 'check' | 'lint' | 'fix' | 'render_svg' | 'render_text' | 'layout' | 'version';

export type AnswerOp = 'check' | 'render_svg' | 'render_text' | 'layout';

export const ANSWER_OPS: readonly AnswerOp[] = ['check', 'render_svg', 'render_text', 'layout'];

export type ToWorker =
  | { type: 'init'; engine: EngineId; loader: string; wasm: string }
  | { type: 'call'; id: number; revision: number; op: Op; source: string; optionsJson: string };

export type FromWorker =
  | { type: 'progress'; loaded: number; total: number | null }
  | { type: 'ready' }
  | { type: 'failed'; message: string }
  | { type: 'result'; id: number; revision: number; response: string }
  | { type: 'call-failed'; id: number; revision: number; message: string };

export const DEBOUNCE_MS = 150;

export const LOAD_TIMEOUT_MS = 30_000;

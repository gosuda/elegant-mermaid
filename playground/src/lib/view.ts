import type { EngineDiagnostics } from './diagnostics';
import type { AnswerOp } from './protocol';

export type TabId = 'svg' | 'text' | 'layout' | 'diagnostics';

export interface TabSpec {
  id: TabId;
  label: string;
  op: AnswerOp;
}

export const TABS: readonly TabSpec[] = [
  { id: 'svg', label: 'SVG', op: 'render_svg' },
  { id: 'text', label: 'Text', op: 'render_text' },
  { id: 'layout', label: 'Layout', op: 'layout' },
  { id: 'diagnostics', label: 'Diagnostics JSON', op: 'check' },
];

export interface Answer {
  ok: boolean;
  output: string;
}

export interface ValidSlot {
  revision: number;
  output: string;
}

export interface EngineView {
  revision: number;
  answers: Partial<Record<AnswerOp, Answer>>;
  valid: Partial<Record<AnswerOp, ValidSlot>>;
  diagnostics: EngineDiagnostics | null;
}

export interface PaneContent {
  slot: ValidSlot | null;
  stale: boolean;
  invalid: boolean;
}

export function emptyView(): EngineView {
  return { revision: 0, answers: {}, valid: {}, diagnostics: null };
}

export function paneContent(view: EngineView, op: AnswerOp, latest: number): PaneContent {
  const slot = view.valid[op] ?? null;
  const answer = view.revision === latest ? view.answers[op] : undefined;
  const failed = op !== 'check' && answer !== undefined && !answer.ok;
  return { slot, stale: failed && slot !== null, invalid: failed && slot === null };
}

export function nextTab(current: TabId, key: string): TabId | null {
  const index = TABS.findIndex((tab) => tab.id === current);
  const last = TABS.length - 1;
  let target: number;
  switch (key) {
    case 'ArrowRight':
      target = index === last ? 0 : index + 1;
      break;
    case 'ArrowLeft':
      target = index === 0 ? last : index - 1;
      break;
    case 'Home':
      target = 0;
      break;
    case 'End':
      target = last;
      break;
    default:
      return null;
  }
  return TABS[target]?.id ?? null;
}

export function failureText(name: string, message: string): string {
  return `The ${name} engine could not load: ${message.replace(/\.+$/, '')}. Check your connection, then select Retry ${name} engine.`;
}

const MIB = 1024 * 1024;

export function mebibytes(bytes: number): string {
  return (bytes / MIB).toFixed(1);
}

export function progressText(loaded: number, total: number | null): string {
  if (total !== null && total > 0 && loaded <= total) {
    return `${mebibytes(loaded)} of ${mebibytes(total)} MiB`;
  }
  return `${mebibytes(loaded)} MiB`;
}

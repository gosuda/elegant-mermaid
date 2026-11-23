import { ENGINE_NAME, type EngineId } from './protocol';

export interface LineDifference {
  line: number;
  left: string | null;
  right: string | null;
}

export interface EngineAnswers {
  failed: boolean;
  layout: { ok: boolean; output: string } | null;
  text: { ok: boolean; output: string } | null;
}

export interface Difference {
  subject: 'Layout' | 'Text';
  difference: LineDifference;
}

export type Comparison =
  | { kind: 'none'; text: '' }
  | { kind: 'pending' | 'unavailable'; text: string }
  | { kind: 'settled'; text: string; difference: Difference | null };

export function firstDifference(left: string, right: string): LineDifference | null {
  if (left === right) {
    return null;
  }
  const a = left.split('\n');
  const b = right.split('\n');
  const length = Math.max(a.length, b.length);
  for (let index = 0; index < length; index += 1) {
    const x = index < a.length ? (a[index] ?? '') : null;
    const y = index < b.length ? (b[index] ?? '') : null;
    if (x !== y) {
      return { line: index + 1, left: x, right: y };
    }
  }
  return null;
}

export function excerpt(text: string | null, line: number): string {
  return text === null ? `(no line ${line})` : text;
}

function names(ids: EngineId[]): string {
  return ids.map((id) => ENGINE_NAME[id]).join(', ');
}

export function compare(go: EngineAnswers, rust: EngineAnswers, revision: number, sourceEmpty: boolean): Comparison {
  const failed: EngineId[] = [];
  if (go.failed) {
    failed.push('go');
  }
  if (rust.failed) {
    failed.push('rust');
  }
  const firstFailed = failed[0];
  if (firstFailed !== undefined) {
    return { kind: 'unavailable', text: `Comparison unavailable: ${ENGINE_NAME[firstFailed]} engine failed` };
  }
  if (sourceEmpty) {
    return { kind: 'unavailable', text: 'Comparison unavailable: current source has errors' };
  }
  const waiting: EngineId[] = [];
  if (go.layout === null || go.text === null) {
    waiting.push('go');
  }
  if (rust.layout === null || rust.text === null) {
    waiting.push('rust');
  }
  if (waiting.length > 0) {
    return { kind: 'pending', text: `Comparison pending for revision ${revision}: ${names(waiting)}` };
  }
  const answers = [go.layout, go.text, rust.layout, rust.text];
  if (answers.some((answer) => answer === null || !answer.ok)) {
    return { kind: 'unavailable', text: 'Comparison unavailable: current source has errors' };
  }
  const layout = firstDifference(go.layout?.output ?? '', rust.layout?.output ?? '');
  const text = firstDifference(go.text?.output ?? '', rust.text?.output ?? '');
  const summary = `Layout: ${layout === null ? 'identical' : 'differs'} · Text: ${text === null ? 'identical' : 'differs'}`;
  const difference: Difference | null =
    layout !== null
      ? { subject: 'Layout', difference: layout }
      : text !== null
        ? { subject: 'Text', difference: text }
        : null;
  return { kind: 'settled', text: summary, difference };
}

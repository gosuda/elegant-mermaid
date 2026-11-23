import { describe, expect, it } from 'vitest';
import { compare, type EngineAnswers, excerpt, firstDifference } from './compare';

const done = (layout: string, text: string, ok = true): EngineAnswers => ({
  failed: false,
  layout: { ok, output: layout },
  text: { ok, output: text },
});
const waiting: EngineAnswers = { failed: false, layout: null, text: null };
const failed: EngineAnswers = { failed: true, layout: null, text: null };

describe('firstDifference', () => {
  it('is null for equal text', () => {
    expect(firstDifference('a\nb\n', 'a\nb\n')).toBeNull();
  });

  it('numbers lines from 1', () => {
    expect(firstDifference('a\nb\nc', 'a\nx\nc')).toEqual({ line: 2, left: 'b', right: 'x' });
  });

  it('reports a missing line as null', () => {
    expect(firstDifference('a\nb', 'a')).toEqual({ line: 2, left: 'b', right: null });
    expect(firstDifference('a', 'a\nb')).toEqual({ line: 2, left: null, right: 'b' });
    expect(excerpt(null, 2)).toBe('(no line 2)');
    expect(excerpt('b', 2)).toBe('b');
  });

  it('sees a trailing line feed as a difference', () => {
    expect(firstDifference('a\n', 'a')).toEqual({ line: 2, left: '', right: null });
  });
});

describe('compare', () => {
  it('reports identical outputs', () => {
    const result = compare(done('l', 't'), done('l', 't'), 3, false);
    expect(result).toEqual({ kind: 'settled', text: 'Layout: identical · Text: identical', difference: null });
  });

  it('reports the first difference, layout before text', () => {
    const result = compare(done('l1\nl2', 't1'), done('l1\nx2', 't2'), 3, false);
    expect(result).toEqual({
      kind: 'settled',
      text: 'Layout: differs · Text: differs',
      difference: { subject: 'Layout', difference: { line: 2, left: 'l2', right: 'x2' } },
    });
    const textOnly = compare(done('l', 't1'), done('l', 't2'), 3, false);
    expect(textOnly.kind === 'settled' && textOnly.difference?.subject).toBe('Text');
  });

  it('names the engines that have not answered', () => {
    expect(compare(waiting, done('l', 't'), 4, false).text).toBe('Comparison pending for revision 4: Go');
    expect(compare(done('l', 't'), waiting, 4, false).text).toBe('Comparison pending for revision 4: Rust');
    expect(compare(waiting, waiting, 4, false).text).toBe('Comparison pending for revision 4: Go, Rust');
  });

  it('reports a failed engine before anything else', () => {
    expect(compare(failed, waiting, 4, false).text).toBe('Comparison unavailable: Go engine failed');
    expect(compare(done('l', 't'), failed, 4, false).text).toBe('Comparison unavailable: Rust engine failed');
  });

  it('reports a source with errors', () => {
    expect(compare(done('', '', false), done('', '', false), 2, false).text).toBe(
      'Comparison unavailable: current source has errors',
    );
    expect(compare(done('l', 't'), done('', '', false), 2, false).text).toBe(
      'Comparison unavailable: current source has errors',
    );
    expect(compare(waiting, waiting, 2, true).text).toBe('Comparison unavailable: current source has errors');
  });
});

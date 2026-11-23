import { describe, expect, it } from 'vitest';
import { parseResponse } from './response';

describe('parseResponse', () => {
  it('reads the four keys', () => {
    const raw = JSON.stringify({ ok: true, output: 'x', diagnostics: [], applied: 2 });
    expect(parseResponse(raw)).toEqual({ ok: true, output: 'x', diagnostics: [], applied: 2 });
  });

  it('drops malformed diagnostics and keeps valid ones', () => {
    const good = {
      code: 'a/b',
      severity: 'error',
      message: 'm',
      span: { start: 0, end: 1 },
      line: 1,
      column: 1,
      end_line: 1,
      end_column: 2,
      related: [],
      help: '',
      fixes: [],
    };
    const parsed = parseResponse(
      JSON.stringify({ ok: false, output: '', diagnostics: [good, { code: 1 }], applied: 0 }),
    );
    expect(parsed?.diagnostics).toEqual([good]);
  });

  it('rejects text that is not a response', () => {
    expect(parseResponse('nope')).toBeNull();
    expect(parseResponse('null')).toBeNull();
    expect(parseResponse('{"ok":1}')).toBeNull();
    expect(parseResponse('{"ok":true,"output":"","diagnostics":{}}')).toBeNull();
  });
});

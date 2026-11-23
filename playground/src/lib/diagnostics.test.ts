import { describe, expect, it } from 'vitest';
import {
  accessibleName,
  ByteIndex,
  type Diagnostic,
  editorRanges,
  emptySourceDiagnostic,
  mergeDiagnostics,
} from './diagnostics';

function diagnostic(
  code: string,
  start: number,
  end: number,
  message = 'm',
  severity: Diagnostic['severity'] = 'error',
): Diagnostic {
  return {
    code,
    severity,
    message,
    span: { start, end },
    line: 2,
    column: 4,
    end_line: 2,
    end_column: 6,
    related: [],
    help: '',
    fixes: [],
  };
}

describe('mergeDiagnostics', () => {
  it('merges diagnostics with equal code, span and message', () => {
    const merged = mergeDiagnostics(
      { diagnostics: [diagnostic('a/x', 3, 5)], source: 's' },
      { diagnostics: [diagnostic('a/x', 3, 5)], source: 's' },
    );
    expect(merged.map((item) => item.engine)).toEqual(['Go and Rust']);
  });

  it('keeps diagnostics that differ in any of the three fields apart', () => {
    const merged = mergeDiagnostics(
      { diagnostics: [diagnostic('a/x', 3, 5), diagnostic('a/y', 3, 5), diagnostic('a/z', 3, 5, 'one')], source: 's' },
      { diagnostics: [diagnostic('a/x', 3, 6), diagnostic('a/y', 3, 5), diagnostic('a/z', 3, 5, 'two')], source: 's' },
    );
    expect(merged.map((item) => `${item.diagnostic.code}:${item.engine}`)).toEqual([
      'a/x:Go',
      'a/x:Rust',
      'a/y:Go and Rust',
      'a/z:Go',
      'a/z:Rust',
    ]);
  });

  it('labels a single engine', () => {
    expect(mergeDiagnostics({ diagnostics: [diagnostic('a/x', 0, 1)], source: '' }, null).map((i) => i.engine)).toEqual(
      ['Go'],
    );
    expect(mergeDiagnostics(null, { diagnostics: [diagnostic('a/x', 0, 1)], source: '' }).map((i) => i.engine)).toEqual(
      ['Rust'],
    );
    expect(mergeDiagnostics(null, null)).toEqual([]);
  });

  it('sorts by span start then code', () => {
    const merged = mergeDiagnostics(
      { diagnostics: [diagnostic('b/x', 9, 9), diagnostic('z/x', 1, 2), diagnostic('a/x', 1, 2)], source: '' },
      null,
    );
    expect(merged.map((item) => item.diagnostic.code)).toEqual(['a/x', 'z/x', 'b/x']);
  });
});

describe('accessibleName', () => {
  it('follows ENGINE SEVERITY CODE, line L, column C: MESSAGE', () => {
    const [item] = mergeDiagnostics(
      {
        diagnostics: [diagnostic('flowchart/unclosed-node-bracket', 3, 5, 'unclosed node bracket', 'warning')],
        source: '',
      },
      null,
    );
    expect(item && accessibleName(item)).toBe(
      'Go warning flowchart/unclosed-node-bracket, line 2, column 4: unclosed node bracket',
    );
  });
});

describe('emptySourceDiagnostic', () => {
  it('matches the registry row for an empty source', () => {
    const value = emptySourceDiagnostic();
    expect(value.code).toBe('common/empty-source');
    expect(value.message).toBe('source is empty');
    expect(value.span).toEqual({ start: 0, end: 0 });
  });
});

describe('ByteIndex', () => {
  it('maps UTF-8 byte offsets to UTF-16 offsets', () => {
    const text = 'aé世🌍z';
    const index = new ByteIndex(text);
    expect(index.utf16(0)).toBe(0);
    expect(index.utf16(1)).toBe(1);
    expect(index.utf16(3)).toBe(2);
    expect(index.utf16(6)).toBe(3);
    expect(index.utf16(10)).toBe(5);
    expect(index.utf16(11)).toBe(6);
  });

  it('maps an offset inside a sequence to the start of that sequence and clamps', () => {
    const index = new ByteIndex('é世');
    expect(index.utf16(1)).toBe(0);
    expect(index.utf16(4)).toBe(1);
    expect(index.utf16(-3)).toBe(0);
    expect(index.utf16(999)).toBe(2);
  });

  it('counts a lone surrogate as three bytes', () => {
    const text = `a${String.fromCharCode(0xd800)}b`;
    const index = new ByteIndex(text);
    expect(index.utf16(4)).toBe(2);
  });
});

describe('editorRanges', () => {
  it('converts byte spans and clamps to the document', () => {
    const merged = mergeDiagnostics(
      { diagnostics: [diagnostic('a/x', 3, 6), diagnostic('a/y', 100, 200)], source: 'aé世z' },
      null,
    );
    const ranges = editorRanges(merged, 4);
    expect(ranges.map((range) => [range.from, range.to])).toEqual([
      [2, 3],
      [4, 4],
    ]);
    expect(ranges[0]?.message).toBe('a/x: m');
  });
});

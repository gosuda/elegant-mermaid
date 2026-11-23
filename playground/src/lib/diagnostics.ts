import type { EngineId } from './protocol';

export type Severity = 'error' | 'warning' | 'info';

export interface Diagnostic {
  code: string;
  severity: Severity;
  message: string;
  span: { start: number; end: number };
  line: number;
  column: number;
  end_line: number;
  end_column: number;
  related: unknown[];
  help: string;
  fixes: unknown[];
}

export type EngineLabel = 'Go' | 'Rust' | 'Go and Rust';

export interface EngineDiagnostics {
  diagnostics: Diagnostic[];
  source: string;
}

export interface MergedDiagnostic {
  engine: EngineLabel;
  diagnostic: Diagnostic;
  source: string;
}

export interface EditorRange {
  from: number;
  to: number;
  severity: Severity;
  message: string;
  source: string;
}

const SEVERITIES: readonly string[] = ['error', 'warning', 'info'];

export function isDiagnostic(value: unknown): value is Diagnostic {
  if (typeof value !== 'object' || value === null) {
    return false;
  }
  const record = value as Record<string, unknown>;
  const span = record.span as Record<string, unknown> | null | undefined;
  return (
    typeof record.code === 'string' &&
    typeof record.severity === 'string' &&
    SEVERITIES.includes(record.severity) &&
    typeof record.message === 'string' &&
    typeof span === 'object' &&
    span !== null &&
    Number.isInteger(span.start) &&
    Number.isInteger(span.end) &&
    Number.isInteger(record.line) &&
    Number.isInteger(record.column)
  );
}

export function emptySourceDiagnostic(): Diagnostic {
  return {
    code: 'common/empty-source',
    severity: 'error',
    message: 'source is empty',
    span: { start: 0, end: 0 },
    line: 1,
    column: 1,
    end_line: 1,
    end_column: 1,
    related: [],
    help: 'add a diagram header, for example flowchart',
    fixes: [],
  };
}

function sameDiagnostic(a: Diagnostic, b: Diagnostic): boolean {
  return a.code === b.code && a.span.start === b.span.start && a.span.end === b.span.end && a.message === b.message;
}

function compareText(a: string, b: string): number {
  if (a === b) {
    return 0;
  }
  return a < b ? -1 : 1;
}

export function mergeDiagnostics(go: EngineDiagnostics | null, rust: EngineDiagnostics | null): MergedDiagnostic[] {
  const merged: MergedDiagnostic[] = [];
  const matched = new Set<number>();
  for (const diagnostic of go?.diagnostics ?? []) {
    const peerIndex = (rust?.diagnostics ?? []).findIndex(
      (peer, index) => !matched.has(index) && sameDiagnostic(diagnostic, peer),
    );
    if (peerIndex >= 0) {
      matched.add(peerIndex);
      merged.push({ engine: 'Go and Rust', diagnostic, source: go?.source ?? '' });
    } else {
      merged.push({ engine: 'Go', diagnostic, source: go?.source ?? '' });
    }
  }
  (rust?.diagnostics ?? []).forEach((diagnostic, index) => {
    if (!matched.has(index)) {
      merged.push({ engine: 'Rust', diagnostic, source: rust?.source ?? '' });
    }
  });
  const rank: Record<EngineLabel, number> = { 'Go and Rust': 0, Go: 1, Rust: 2 };
  return merged
    .map((item, index) => ({ item, index }))
    .sort(
      (a, b) =>
        a.item.diagnostic.span.start - b.item.diagnostic.span.start ||
        compareText(a.item.diagnostic.code, b.item.diagnostic.code) ||
        rank[a.item.engine] - rank[b.item.engine] ||
        a.index - b.index,
    )
    .map(({ item }) => item);
}

export function accessibleName(item: MergedDiagnostic): string {
  const { diagnostic, engine } = item;
  return `${engine} ${diagnostic.severity} ${diagnostic.code}, line ${diagnostic.line}, column ${diagnostic.column}: ${diagnostic.message}`;
}

export function selectionLabel(engines: readonly EngineId[]): EngineLabel {
  if (engines.length === 2) {
    return 'Go and Rust';
  }
  return engines[0] === 'rust' ? 'Rust' : 'Go';
}

export class ByteIndex {
  readonly #utf16: Uint32Array;
  readonly #length: number;

  constructor(text: string) {
    let bytes = 0;
    for (const character of text) {
      bytes += utf8Length(character.charCodeAt(0), character.length);
    }
    this.#utf16 = new Uint32Array(bytes + 1);
    this.#length = text.length;
    let byte = 0;
    let unit = 0;
    for (const character of text) {
      const width = utf8Length(character.charCodeAt(0), character.length);
      for (let step = 0; step < width; step += 1) {
        this.#utf16[byte + step] = unit;
      }
      byte += width;
      unit += character.length;
    }
    this.#utf16[bytes] = unit;
  }

  utf16(byteOffset: number): number {
    if (byteOffset <= 0) {
      return 0;
    }
    if (byteOffset >= this.#utf16.length) {
      return this.#length;
    }
    return this.#utf16[byteOffset] ?? this.#length;
  }
}

function utf8Length(first: number, utf16Units: number): number {
  if (utf16Units === 2) {
    return 4;
  }
  if (first < 0x80) {
    return 1;
  }
  if (first < 0x800) {
    return 2;
  }
  return 3;
}

export function editorRanges(items: readonly MergedDiagnostic[], docLength: number): EditorRange[] {
  let cached: { text: string; index: ByteIndex } | null = null;
  const indexFor = (text: string): ByteIndex => {
    if (cached === null || cached.text !== text) {
      cached = { text, index: new ByteIndex(text) };
    }
    return cached.index;
  };
  return items.map(({ diagnostic, engine, source }) => {
    const index = indexFor(source);
    const from = Math.min(index.utf16(diagnostic.span.start), docLength);
    const to = Math.min(Math.max(index.utf16(diagnostic.span.end), from), docLength);
    return {
      from,
      to,
      severity: diagnostic.severity,
      message: `${diagnostic.code}: ${diagnostic.message}`,
      source: engine,
    };
  });
}

import { type Diagnostic, isDiagnostic } from './diagnostics';

export interface EmdResponse {
  ok: boolean;
  output: string;
  diagnostics: Diagnostic[];
  applied: number;
}

export function parseResponse(raw: string): EmdResponse | null {
  let value: unknown;
  try {
    value = JSON.parse(raw);
  } catch {
    return null;
  }
  if (typeof value !== 'object' || value === null) {
    return null;
  }
  const record = value as Record<string, unknown>;
  if (typeof record.ok !== 'boolean' || typeof record.output !== 'string' || !Array.isArray(record.diagnostics)) {
    return null;
  }
  const applied = typeof record.applied === 'number' && Number.isInteger(record.applied) ? record.applied : 0;
  return { ok: record.ok, output: record.output, diagnostics: record.diagnostics.filter(isDiagnostic), applied };
}

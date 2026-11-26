import { describe, expect, it } from 'vitest';
import { RevisionGuard } from './revision';

describe('RevisionGuard', () => {
  it('numbers revisions from 1', () => {
    const guard = new RevisionGuard();
    expect(guard.latest).toBe(0);
    expect(guard.issue()).toBe(1);
    expect(guard.issue()).toBe(2);
    expect(guard.latest).toBe(2);
  });

  it('drops a response older than the newest request', () => {
    const guard = new RevisionGuard();
    const first = guard.issue();
    const second = guard.issue();
    expect(guard.accept(first)).toBe(false);
    expect(guard.displayed).toBe(0);
    expect(guard.accept(second)).toBe(true);
    expect(guard.displayed).toBe(second);
  });

  it('never moves the displayed revision backwards when answers arrive out of order', () => {
    const guard = new RevisionGuard();
    const shown: number[] = [];
    const revisions = [guard.issue(), guard.issue(), guard.issue()];
    for (const revision of [revisions[2], revisions[0], revisions[1], revisions[2]]) {
      if (revision !== undefined && guard.accept(revision)) {
        shown.push(revision);
      }
    }
    expect(shown).toEqual([3, 3]);
    expect(guard.displayed).toBe(3);
    const next = guard.issue();
    expect(guard.accept(3)).toBe(false);
    expect(guard.displayed).toBe(3);
    expect(guard.accept(next)).toBe(true);
    expect(guard.displayed).toBe(next);
  });

  it('accepts every answer of the newest revision', () => {
    const guard = new RevisionGuard();
    const revision = guard.issue();
    expect([guard.accept(revision), guard.accept(revision), guard.accept(revision)]).toEqual([true, true, true]);
  });

  it('rejects a revision that was never issued', () => {
    const guard = new RevisionGuard();
    guard.issue();
    expect(guard.accept(7)).toBe(false);
    expect(guard.displayed).toBe(0);
  });
});

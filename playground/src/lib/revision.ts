export class RevisionGuard {
  #latest = 0;
  #displayed = 0;

  get latest(): number {
    return this.#latest;
  }

  get displayed(): number {
    return this.#displayed;
  }

  issue(): number {
    this.#latest += 1;
    return this.#latest;
  }

  accept(revision: number): boolean {
    if (revision !== this.#latest) {
      return false;
    }
    this.#displayed = revision;
    return true;
  }
}

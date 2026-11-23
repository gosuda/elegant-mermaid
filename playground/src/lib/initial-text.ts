const files = import.meta.glob<string>('./initial-text.txt', { query: '?raw', import: 'default', eager: true });

export const INITIAL_TEXT: string = files['./initial-text.txt'] ?? '';

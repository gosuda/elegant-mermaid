import adapter from '@sveltejs/adapter-static';
import { sveltekit } from '@sveltejs/kit/vite';
import { loadEnv } from 'vite';
import { defineConfig } from 'vitest/config';

export default defineConfig(({ mode }) => {
  const base = loadEnv(mode, '.', '').BASE_PATH ?? '';
  return {
    plugins: [
      sveltekit({
        adapter: adapter({ pages: 'build', assets: 'build', precompress: false, strict: true }),
        paths: { base: base as '' | `/${string}`, relative: false },
      }),
    ],
    worker: { format: 'iife' },
    test: {
      include: ['src/**/*.test.ts'],
      environment: 'node',
    },
  };
});

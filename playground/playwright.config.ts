import { defineConfig } from '@playwright/test';

declare const process: { env: Record<string, string | undefined> };

const basePath = process.env.BASE_PATH ?? '';
const external = process.env.PLAYGROUND_URL;
const local = `http://localhost:4173${basePath}/`;
const baseURL = external === undefined || external === '' ? local : external.endsWith('/') ? external : `${external}/`;

export default defineConfig({
  testDir: './tests',
  timeout: 60_000,
  expect: { timeout: 20_000 },
  workers: 2,
  reporter: [['list']],
  use: {
    baseURL,
    channel: process.env.PLAYWRIGHT_CHANNEL,
    trace: 'retain-on-failure',
  },
  ...(external === undefined || external === ''
    ? {
        webServer: {
          command:
            process.env.PLAYGROUND_SERVER_MODE === 'dev'
              ? 'pnpm dev --port 4173 --strictPort'
              : 'pnpm preview --port 4173 --strictPort',
          url: local,
          reuseExistingServer: false,
          timeout: 120_000,
        },
      }
    : {}),
});

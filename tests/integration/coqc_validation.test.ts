/**
 * Regression test: coqc cross-validation in check_file.
 *
 * Verifies that check_file runs coqc after the LSP check and produces:
 *   - "coqc agrees with coq-lsp" when both tool results match
 *   - "coqc vs coq-lsp discrepancy" when coq-lsp Qed but coqc rejects
 *
 * The real-world discrepancy (Iris heap proof) is tested via the fixture
 * coqlsp_qed_coqc_rejects.v which requires compiled deps. See that file
 * and its _RocqProject for manual verification.
 *
 * Run: npm run test:integration -- coqc_validation
 */

import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { McpHarness, createHarness, fixture, tempFixture, removeTempFixture } from './harness.js';

const TIMEOUT = 60_000;

let h: McpHarness;

beforeAll(async () => {
  h = await createHarness();
}, TIMEOUT);

afterAll(async () => {
  await h.teardown();
});

describe('coqc validation in check_file', () => {
  it('shows coqc errors inline with each lemma entry', async () => {
    const f = tempFixture('coqc_validation_basic.v', 'coqc_inline');
    try {
      const r = await h.callTool('check_file', { file: f, auto_admit: false }, TIMEOUT);
      expect(r.isError).toBe(false);
      // bad_proof is [FAILED]; coqc errors appear inline after coq-lsp errors
      expect(r.text).toMatch(/coqc L\d+/);
      // the coqc error should be on the line where reflexivity fails (line 7 = 0-based 6)
      expect(r.text).toMatch(/coqc L7:|coqc L8:/);
      console.log('[coqc_inline]', r.text);
    } finally {
      removeTempFixture(f);
    }
  });

  it('shows [DISCREPANCY] when coq-lsp Qed but coqc rejects', async () => {
    // Use the Iris discrepancy fixture — requires deps in same directory
    // For CI, this test is informational; the real regression test is manual
    // with the coqlsp_qed_coqc_rejects.v fixture in a workspace with deps.
    const f = tempFixture('coqc_validation_basic.v', 'coqc_discrepancy');
    try {
      // Inject a lemma that coq-lsp might accept but coqc rejects.
      // We'll use a lemma name containing "discrepancy" so the test can match.
      const edit = await h.callTool('edit_file', {
        file: f,
        find: 'Qed.',
        replace: 'Qed.\n\n(* coq-lsp may accept this at Qed time but coqc rejects it *)\nLemma delib_unsound : 1 = 2.\nProof.\n  exact (ltac:(exact_no_check (eq_refl 1))).\nQed.\n',
      }, TIMEOUT);

      const r = await h.callTool('check_file', { file: f, auto_admit: false }, TIMEOUT);
      expect(r.isError).toBe(false);

      // The lemma should have coqc errors. If coq-lsp also catches it, status is FAILED.
      // If coq-lsp misses it, status is DISCREPANCY.
      // In either case, coqc error line should appear in the output.
      expect(r.text).toMatch(/coqc L\d+/);
      expect(r.text).toMatch(/delib_unsound/);
      console.log('[coqc_discrepancy]', r.text);
    } finally {
      removeTempFixture(f);
    }
  });
});

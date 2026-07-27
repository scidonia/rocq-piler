# Specsaver Output Grouping for Parallel Proof

## Problem

Generated obligation files (e.g. `GenReleaseObligations.v`) bundle 10-12 lemmas into a single file. The lemmas are interdependent, making them inherently sequential within one file. For parallel AI proof generation, we need the smallest feasible chunks that can be proven independently.

## Dependency Analysis (GenRelease)

```
Layer 0 (standalone, no lemma deps):
  o4_exit_coverage           — trivial arithmetic, 0 deps
  o1_admissibility_sanity    — existential over gen_pre, 0 deps

Layer 1 (depends on gen_table structure only):
  gen_table_total_pure        — vacuous for FunSpec, 0 lemma deps  
  gen_table_total             — requires gen_table structure, 0 lemma deps

Layer 2 (depends on Layer 1):
  o2_spec_consistency         — uses gen_table_total
  o3_0_exception_consistency  — uses gen_table_total

Layer 3 (depends on store invariants only):
  store_inv_lookup            — induction on store, 0 lemma deps
  gen_preserves_inv_0         — uses store_inv definitions, 0 lemma deps

Layer 4 (depends on multiple layers):
  o5_invariant_preservation   — uses store_inv_lookup + gen_preserves_inv_0
  o8_frame_soundness          — uses gen_post, 0 lemma deps
```

## Recommendation: Split by Dependency Layer

Specsaver should emit **one `.v` file per dependency layer**, each containing only the lemmas from that layer. All files share a single language/prelude module.

```
contracts/release/
  release_lang.v          — shared language definitions (unchanged)
  release_wp.v            — shared WP lemmas (unchanged)  
  release_prelude.v       — shared imports/context (unchanged)
  release_L0.v            — 2 lemmas (o4, o1)
  release_L1.v            — 2 lemmas (gen_table_total_pure, gen_table_total)
  release_L2.v            — 2 lemmas (o2, o3)
  release_L3.v            — 2 lemmas (store_inv_lookup, gen_preserves_inv_0)
  release_L4.v            — 2 lemmas (o5, o8)
```

**Benefits:**
- 5 files can be proven in parallel (down from 1)
- Each file is ~30-50 lines (vs ~200 lines combined)
- Model handles 2 lemmas at a time instead of 10
- If one group fails, others still succeed
- Correlates output with contract via directory structure (`contracts/release/`)

**Tradeoffs:**
- More files to manage
- Each file needs the shared imports (release_lang, release_wp, release_prelude)
- Layer 0 must complete before Layer 1-4 can be proven (they share the FunCtx)
- Actually: Layers 0, 1, 3 have **no inter-layer deps** — they can all run in parallel

## Revised Parallel Schedule

```
Phase 1 (run simultaneously):
  release_L0.v     — standalone, 0 deps
  release_L1.v     — depends on gen_table (unchanged definition, not lemma)
  release_L3.v     — depends on store_inv (unchanged definition, not lemma)

Phase 2 (after Phase 1):
  release_L2.v     — depends on gen_table_total (proved in L1)
  release_L4.v     — depends on L3 + L1 lemmas
```

## Implementation in Specsaver

1. Track which generated lemma depends on which other generated lemma during obligation emission
2. Build a dependency graph
3. Topological sort into layers
4. Emit one `.v` file per layer, each importing the shared language module
5. Output a `_CoqProject` that lists all layers in dependency order (for sequential fallback)
6. Generate a `schedule.json` with the DAG for automated parallel execution

## Benchmark Harness Integration

The benchmark harness can read `schedule.json` to run phases:
```json
{
  "contract": "release",
  "phases": [
    {"files": ["release_L0.v", "release_L1.v", "release_L3.v"], "maxParallel": 3},
    {"files": ["release_L2.v", "release_L4.v"], "maxParallel": 2}
  ]
}
```

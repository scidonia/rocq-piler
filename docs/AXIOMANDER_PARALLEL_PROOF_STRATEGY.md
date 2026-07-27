# Parallel Obligation Proof Strategy

## Overview

Axiomander emits proof obligations in **dependency layers** — one `.v` file
per layer, plus a `schedule.json` that describes which layers can be proven
in parallel and which depend on previous layers.

Rocq-piler consumes this output to orchestrate parallel proof generation
across multiple LLM agents.

## Input Format

After `gen_obligations.py --layered`, the output directory contains:

```
coq/gen/release/
├── release_defs.v          — shared definitions, FunCtx, totals
├── release_L0.v            — standalone lemmas (0 deps)
├── release_L1.v            — depends on L0
├── release_L2.v            — depends on L0, L1
├── release_L3.v            — depends on L0, L1, L2
├── _CoqProject             — files in dependency order (sequential fallback)
└── schedule.json           — parallel execution DAG
```

### `schedule.json`

```json
{
  "contract": "release",
  "phases": [
    {
      "files": ["release_L0.v", "release_L2.v"],
      "maxParallel": 2
    },
    {
      "files": ["release_L1.v", "release_L3.v"],
      "maxParallel": 2
    }
  ]
}
```

## Dependency Layers

Each contract produces four layers:

| Layer | Lemmas | Dependencies | Can parallelize with |
|-------|--------|-------------|---------------------|
| L0 | `o4_exit_coverage`, `o1_admissibility_sanity` | none (standalone) | L2 |
| L1 | `o2_spec_consistency`, `o3_*_exception_consistency` | L0 | L3 |
| L2 | `store_inv_lookup`, `gen_preserves_inv_*` | none (standalone) | L0 |
| L3 | `o5_invariant_preservation`, `o8_frame_soundness` | L0, L1, L2 | L1 |

**Phase 1** dispatches L0 and L2 simultaneously (they have no mutual
dependencies).  **Phase 2** dispatches L1 and L3 after Phase 1 completes
(L1 needs L0; L3 needs L0, L1, L2).

## Rocq-piler Integration

### 1. Parsing the Schedule

Rocq-piler reads `schedule.json` to build a DAG of proof tasks:

```typescript
interface SchedulePhase {
  files: string[];
  maxParallel: number;
}

interface Schedule {
  contract: string;
  phases: SchedulePhase[];
}
```

### 2. Per-File Proof Generation

For each layer file in a phase:

1. **Load the file** and extract open goals (using rocq-lsp's document
   state)
2. **Build context** — the shared definition file and prior-layer imports
   are already `Require Import`ed; rocq-lsp resolves them from the
   `_CoqProject` load path
3. **Invoke the LLM** with:
   - The goal statement (type of the lemma)
   - The current proof state (open goals)
   - The environment (definitions in scope, proven lemmas from earlier layers)
   - A prompt instructing the model to produce a Coq proof script
4. **Validate** — the generated tactic is inserted via rocq-lsp's
   `insert_tactics`; only tactics that close the goal are accepted
5. **Record** the result in the scoreboard

### 3. Parallel Execution

```typescript
async function provePhase(phase: SchedulePhase): Promise<Results> {
  const tasks = phase.files.map(async (file) => {
    const goals = await extractOpenGoals(file);
    const results = [];
    for (const goal of goals) {
      const proof = await llm.generateProof(goal, fileContext(file));
      const accepted = await lsp.tryTactic(file, goal.admitHash, proof);
      results.push({ goal: goal.name, status: accepted ? "PROVED" : "UNKNOWN" });
    }
    return { file, results };
  });
  return Promise.all(tasks);
}

async function proveContract(schedule: Schedule): Promise<void> {
  for (const phase of schedule.phases) {
    await provePhase(phase);
  }
}
```

### 4. Failure Handling

If any lemma in a phase fails to prove (remains `UNKNOWN`):

- The failure does **not** block the parallel phase — other files continue
- Dependent layers (e.g., L3 depends on L2) will receive the lemma as
  `Admitted` in their context, not as a proved theorem
- The scoreboard reflects the partial status
- An `UNKNOWN` lemma can be retried later with a different model or prompt

### 5. Incremental Proof

Proved lemmas are cached by content hash.  When a contract is regenerated
(after spec changes), rocq-piler compares hashes and only re-proves layers
whose content changed or whose dependencies changed.

## Benchmark Harness

The benchmark harness in `rocq-piler` exercises this pipeline:

```
rocq-piler/benchmarks/
├── axiomander/
│   ├── release/          — copy of coq/gen/release/ from specsaver
│   ├── reserve/
│   ├── restock/
│   └── transfer/
└── results/
    └── 2026-07-27/
        ├── release.json  — per-lemma scoreboard
        ├── reserve.json
        └── summary.json  — aggregated stats
```

### Running a Benchmark

```bash
npx rocq-piler bench axiomander/release \
  --model deepseek-v4 \
  --parallel 4 \
  --timeout 300
```

This:
1. Reads `release/schedule.json`
2. Dispatches Phase 1 (L0 + L2) in parallel with up to 4 agents
3. Waits for Phase 1 to complete
4. Dispatches Phase 2 (L1 + L3)
5. Records per-lemma proof status, wall-clock time, and token usage
6. Writes `results/<date>/release.json`

### Expected Results (Current State)

All four contracts have 23/23 obligations PROVED by the hand-written
lowering proofs in `ReserveLowering.v` and the generated `gen_preserves_inv`
lemmas.  The benchmark validates that the LLM-based oracle can reproduce
these proofs autonomously.

## Agent Prompt Template

```
You are proving a Coq lemma in the SnakeletExn WP calculus.

Context: {FunCtx instance with gen_table, pre/post definitions}

Goal: {lemma statement}

Available hypotheses: {environment}

Produce a Coq proof script that closes the goal.  Use tactics:
- intros, destruct, split, exists, reflexivity, lia, congruence
- apply lookup_insert_eq, apply lookup_insert_ne
- eapply gen_table_total, eapply gen_preserves_inv_*

Output only the proof script, no explanation.
```

## Open Questions

1. **Model selection** — which LLM performs best on Coq proof scripts?
   DeepSeek-v4? GPT-5? Fine-tuned Code-Llama?
2. **Prompt engineering** — should the prompt include the full file
   content or just the goal + environment summary?
3. **Retry strategy** — if a lemma fails, should the model see the
   error message and retry? How many retries?
4. **Proof replay** — the generated scripts must be replayable against
   clean Rocq builds.  How to handle non-deterministic tactics?
5. **Cross-contract transfer** — can proofs from one contract (e.g.,
   `reserve`) help prove similar lemmas in another (`release`)?

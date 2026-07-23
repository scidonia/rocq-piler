# rocq-piler

MCP server providing interactive Coq/Rocq proof development tools via coq-lsp.

## Rules

1. **Prove, don't research.** Start writing proofs immediately. Don't search the web for existing proofs or spend time reading the file and understanding the architecture. If a lemma fails, check the error and iterate.
2. **Use `edit_file` for all edits.** It reports errors with goal states inline — you don't need bash+coqc.
3. **Start with easy lemmas** (extends, store weakening) — not the hardest (shift, substitution).

## Tools

- **`search_lemmas`** — find relevant lemmas in the Coq environment by name or pattern
- **`edit_file`** — write or modify `.v` files (supports `find`/`replace` or range-based edits)
- **`check_file`** — verify the file and report errors with diagnostic messages and goal states. Supports `mode: "errors"` (compact: only failures/admitted) and `mode: "first"` (one error at a time)
- **`focus_proof`** — inspect proof state: goals, bullet stack, admits
- **`stratify`** — case-split a proof and auto-close easy cases
- **`close_admits`** — batch-close surviving admits with a portfolio of tactics
- **`reset_proof`** — wipe a proof body and start fresh

Most non-trivial proofs need **helper lemmas** (e.g. substitution, weakening, inversion). Add them before the main theorem.

Start with the **easy lemmas first** (extends, store weakening, heap operations) — not the hardest (shift, substitution). Build up gradually. If a lemma takes more than a few tries, reset and try a different approach. If a proof has too many cases to write by hand, use `stratify` to split it and `close_admits` to batch-close survivors.

**Never reference auto-generated names** from `destruct`, `inversion`, or `induction`. Coq-lsp and coqc can produce different names for the same proof. Always use `as` clauses (`destruct H as [x y]`, `inversion H as [pattern]`, `induction H as [IH]`) and `subst` to canonicalize. Avoid `rename`.

## Build & Test

```bash
npm run build        # TypeScript compilation
npm test             # Run test suite
```

## Benchmarks

The `benchmarks/` directory contains a vericoding evaluation corpus used to benchmark AI proof assistants across multiple MCPs and models.

- `benchmarks/incomplete/` — Challenge files with `Admitted` proofs. These are checked in.
- `benchmarks/complete/` — Solutions produced by AI runs. **NEVER check these in.**

**Do not commit anything under `benchmarks/complete/`.** This directory is gitignored.

### Conjecture pairs

Each benchmark theorem is stated alongside its negation:

```coq
Theorem foo : P.
Proof. Admitted.

Theorem foo_neg : ~ P.
Proof. Admitted.
```

The solver must prove **exactly one** of each pair. The evaluation harness checks that at least one of each pair is `Qed` and the file compiles with `coqc`.

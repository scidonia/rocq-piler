# Proving Specsaver Obligations

These are automatically generated proof obligations for contract verification.
Follow these patterns rather than trying to understand the full system.

## Generic strategies

1. **Trivial arithmetic/propositional splits** → `lia` closes them immediately.
2. **Constructor mismatch** (FunSpecS vs FunSpec, Val vs Exn) → `discriminate`.
3. **Lookup/induction on stores** → induction on the store data structure,
   case split on `String.eqb` or similar equality test.
4. **Destructure function tables** → `unfold fun_table`, destruct on function name,
   `injection` to identify the matching spec, `unfold` the pre/post conditions.
5. **Provide existential witnesses** → `eexists` or `exists` concrete values;
   the post condition definition tells you exactly what to construct.
6. **Apply earlier lemmas** → later obligations often depend on earlier ones;
   reuse `gen_table_total`, `store_inv_lookup`, etc. rather than reproving.
7. **Do NOT use stratify** for single-goal proofs — it corrupts the proof body.
8. **Do NOT use edestruct on spec constructors** — use `injection` then `unfold`.

Start with the shortest lemmas first and work toward the longer ones.

# Proof Patterns for Specsaver Obligations

## Generic strategies the AI discovered through trial and error

### 1. Trivial lemmas — use `lia` or `discriminate`

```
o4_exit_coverage: reserved >= quantity \/ reserved < quantity
  → lia.

gen_table_total_pure: gen_table f = Some (FunSpec ...) 
  → discriminate.  (gen_table only returns FunSpecS, not FunSpec)
```

### 2. Induction on data structures

```
store_inv_lookup: store_inv store_d -> dict_lookup_str k store_d = Some row -> row_inv row
  → induction on store_d, case split on String.eqb

gen_preserves_inv_0: store_inv store_d -> row_inv row -> ... -> store_inv (dict_insert ...)
  → induction on store_d, show updated row still satisfies row_inv
```

### 3. Destruct gen_table, inject constructor, unfold pre/post

```
gen_table_total: gen_table f = Some (FunSpecS pre post) -> pre sigma vs -> ...
  → unfold gen_table, destruct (String.eqb f "release")
  → injection to get pre/post identity, unfold gen_pre/gen_post
  → extract existential witnesses, supply them to gen_post
```

### 4. Construct concrete witnesses for existentials

```
o1_admissibility_sanity: exists sigma vs, gen_pre sigma vs /\ store_inv [...]
  → construct sigma with store_loc pointing to a LitDict
  → construct vs with expected parameter shape
  → prove pre conditions hold for the constructed values
```

### 5. Apply previous lemmas for composition

```
o5_invariant_preservation: ...
  → use store_inv_lookup to get row_inv from pre condition
  → use gen_preserves_inv_0 to show updated store still satisfies store_inv

o2_spec_consistency: gen_pre sigma vs -> ...
  → apply gen_table_total with "release" to get gen_post witnesses
  → extract witnesses from gen_pre using destruct/inversion
```

### 6. Avoid tool misapplication

```
- Do NOT use stratify on gen_table_total_pure — it's a single-case proof
- Do NOT use edestruct on FunSpecS — use injection to equate constructors
- Use lia for arithmetic, discriminate for constructor mismatches
```

### 7. Use `eexists` for existential goals

```
When the goal is exists v, post vs v:
  → eexists or exists with a specific witness
  → the witness is often a LitInt, LitBool, or LitTuple
  → the gen_post definition tells you exactly what to provide
```

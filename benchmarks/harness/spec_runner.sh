#!/usr/bin/env bash
# spec_runner.sh — Read bench_spec.json and run layered benchmarks
# Usage: spec_runner.sh <spec_dir> [--model deepseek/deepseek-v4-pro] [--timeout 600]
set -euo pipefail

SPEC_DIR="$1"; shift
MODEL="${DEEPSEEK_MODEL:-deepseek/deepseek-v4-pro}"
TIMEOUT=600
while [[ $# -gt 0 ]]; do
  case $1 in --model) MODEL="$2"; shift 2 ;; --timeout) TIMEOUT="$2"; shift 2 ;; *) shift ;; esac
done

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
ROCQ_PILER_DIST="$REPO_DIR/dist/index.js"
COQ_LSP_PATH=$(jq -r '(.mcpServers // .mcp // {})["rocq-piler"].command[-1] // empty' "$HOME/.config/opencode/opencode.json" 2>/dev/null || echo "coq-lsp")

SPEC="$SPEC_DIR/bench_spec.json"
[[ ! -f "$SPEC" ]] && { echo "No bench_spec.json in $SPEC_DIR"; exit 1; }

CONTRACT=$(jq -r '.contract' "$SPEC")
RESULT_DIR="/tmp/spec_results/${CONTRACT}_$(date +%s)"
mkdir -p "$RESULT_DIR"

echo "=== $CONTRACT: compiling deps ==="
W=$(mktemp -d "/tmp/spec_${CONTRACT}_XXXXXX")

# Create opencode config with rocq-piler MCP
jq -n --arg cmd "node" --arg dist "$ROCQ_PILER_DIST" --arg coq "$COQ_LSP_PATH" --arg ws "$W" '{
  mcp: { "rocq-piler": { type: "local", command: [$cmd, $dist, "--coq-lsp-path", $coq, "--workspace-root", $ws], enabled: true } },
  tools: {
    "rocq-piler_add_lemma": false, "rocq-piler_add_block": false,
    "rocq-piler_delete_lemma": false, "rocq-piler_move_lemma": false,
    "rocq-piler_inspect_term": true, "rocq-piler_inspect_about": true,
    "rocq-piler_require_lib": false, "rocq-piler_locate_term": false,
    "rocq-mcp_*": false, "morph-mcp_*": false, "github_*": false,
    "google-workspace_*": false, "brevo_*": false, "fal-ai-image_*": false,
    "axiomander_*": false,
    "bash": false, "read": false, "write": false, "edit": false, "grep": false, "glob": false
  }
}' > "$W/opencode.json"

# Copy shared deps (from ../../ = coq/ directory)
for f in $(jq -r '.compile.shared[]' "$SPEC"); do
  cp "$SPEC_DIR/../../${f}" "$W/" 2>/dev/null || cp "$SPEC_DIR/${f}" "$W/" 2>/dev/null || { echo "MISSING: $f"; exit 1; }
done
# Copy per-contract deps
for f in $(jq -r '.compile.per_contract[]' "$SPEC"); do
  cp "$SPEC_DIR/${f}" "$W/"
done

# Compile all deps from scratch in correct dependency order
cd "$W"
for f in SnakeletExnLang SnakeletExnWp SpecPrelude; do
  [ ! -f "${f}.v" ] && { echo "MISSING: ${f}.v"; exit 1; }
  coqc "${f}.v" 2>&1 || { echo "FAIL: ${f}.v"; exit 1; }
done
# Per-contract defs
for f in *.v; do
  [[ ! -f "$f" ]] && continue
  [[ "$f" == *L[0-9].v ]] && continue
  [[ "$f" == Snakelet* ]] && continue
  [[ "$f" == SpecPrelude* ]] && continue
  coqc "$f" 2>&1 || { echo "FAIL: $f"; exit 1; }
done
echo "  deps compiled"
# Delete .vos — coq-lsp and coqc 9.x both fail on them; .vo fallback works
rm -f "$W"/*.vos
# Don't copy _CoqProject — coq-lsp/coqc may corrupt it with -R . Top which breaks compilation
rm -f "$W"/_CoqProject "$W"/_RocqProject 2>/dev/null || true
# Copy project skill for MCP injection
[ -f "$SPEC_DIR/_skill.md" ] && cp "$SPEC_DIR/_skill.md" "$W/"
# coq-lsp 0.2.5 fails on .vos files (empty AND non-empty). Force .vo fallback.
rm -f "$W"/*.vos

# Phase execution
START=$(date +%s)
PHASE_COUNT=$(jq '.prove.phases | length' "$SPEC")
for pi in $(seq 0 $((PHASE_COUNT - 1))); do
  FILES=$(jq -r ".prove.phases[$pi].files[]" "$SPEC")
  MAXP=$(jq -r ".prove.phases[$pi].maxParallel" "$SPEC")
  echo "=== Phase $((pi+1))/$PHASE_COUNT: ${MAXP} parallel ==="
  
  pids=()
  for f in $FILES; do
    cp "$SPEC_DIR/${f}" "$W/"
    # Wipe proofs
    python3 -c "
import re
with open('$W/$f', 'r') as fh: content = fh.read()
lines = content.split('\n'); result = []; i = 0
while i < len(lines):
    line = lines[i]; stripped = line.strip()
    m = re.match(r'^(\s*Proof[\s\.].*?)\s+(Qed\.|Defined\.)\s*$', line)
    if m: result.append(m.group(1) + ' Admitted.'); i += 1; continue
    if stripped.startswith('Proof.') or stripped.startswith('Proof ') or stripped.startswith('Proof\t'):
        depth = 0; j = i + 1; found = False
        while j < len(lines):
            l = lines[j].strip()
            if l.startswith('Proof.') or l.startswith('Proof ') or l.startswith('Proof\t'): depth += 1
            elif l == 'Qed.' or l == 'Defined.' or l == 'Admitted.':
                if depth == 0: found = True; break
                depth -= 1
            j += 1
        if found:
            result.append(lines[i])
            indent = ' ' * (len(line) - len(line.lstrip()))
            result.append(indent + 'Admitted.' if indent else 'Admitted.')
            i = j + 1; continue
    result.append(line); i += 1
with open('$W/$f', 'w') as fh: fh.write('\n'.join(result))
" 2>/dev/null
    # Launch model — prompt references MCP skill resource
    (
      t0=$(date +%s)
      timeout "$TIMEOUT" opencode run --model "$MODEL" --format json \
        --dangerously-skip-permissions --dir "$W" \
        "Prove ALL Admitted theorems in $f — do not stop after the first lemma. Use focus_proof to inspect each goal. Use insert_tactics to step through. Verify with check_file. Prove lemmas in order from top to bottom of the file. A skill guide with Iris/gmap/heap patterns is loaded as project-skill." \
        > "$RESULT_DIR/${f%.v}.jsonl" 2>/dev/null || true  # tolerate timeout (exit 124)
      t1=$(date +%s)
      qed=$(grep -c 'Qed\.' "$W/$f" 2>/dev/null; true)
      admits=$(grep -c 'Admitted\.' "$W/$f" 2>/dev/null; true)
      if coqc -q "$W/$f" 2>/dev/null; then
        echo "  $f: SOLVED ($((t1-t0))s, ${qed}qed)"
      else
        echo "  $f: FAILED ($((t1-t0))s, ${qed}qed/${admits}admits)"
      fi
      # Always compile the layer so next layer can Require Import it.
      # If the model's proof failed, use specsaver's proof to generate a valid .vo.
      if [ ! -f "$W/${f%.v}.vo" ]; then
        mv "$W/$f" "$W/_tmp_$f" 2>/dev/null || true
        cp "${SPEC_DIR}/$f" "$W/$f" 2>/dev/null || true
        coqc -q "$W/$f" 2>/dev/null || true
        mv "$W/_tmp_$f" "$W/$f" 2>/dev/null || true
      fi
    ) &
    pids+=($!)
  done
  for pid in "${pids[@]}"; do wait "$pid"; done
  # Clean up artifacts that block the next layer's compilation
  rm -f "$W"/*.vos "$W"/_CoqProject "$W"/_RocqProject
  echo "  phase $((pi+1)) done"
done

END=$(date +%s)
echo "=== $CONTRACT: wall $((END-START))s, results in $RESULT_DIR ==="
rm -rf "$W"

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

SPEC="$SPEC_DIR/bench_spec.json"
[[ ! -f "$SPEC" ]] && { echo "No bench_spec.json in $SPEC_DIR"; exit 1; }

CONTRACT=$(jq -r '.contract' "$SPEC")
RESULT_DIR="/tmp/spec_results/${CONTRACT}_$(date +%s)"
mkdir -p "$RESULT_DIR"

echo "=== $CONTRACT: compiling deps ==="
W=$(mktemp -d "/tmp/spec_${CONTRACT}_XXXXXX")

# Copy shared deps (from ../../ = coq/ directory)
for f in $(jq -r '.compile.shared[]' "$SPEC"); do
  cp "$SPEC_DIR/../../${f}" "$W/" 2>/dev/null || cp "$SPEC_DIR/${f}" "$W/" 2>/dev/null || { echo "MISSING: $f"; exit 1; }
done
# Copy per-contract deps
for f in $(jq -r '.compile.per_contract[]' "$SPEC"); do
  cp "$SPEC_DIR/${f}" "$W/"
done

# Compile shared deps first
for f in SnakeletExnLang SnakeletExnWp SpecPrelude; do
  [ -f "${f}.v" ] && coqc -q "${f}.v" 2>/dev/null || true
done
# Then per-contract deps
for f in *.v; do
  [[ ! -f "$f" ]] && continue
  [[ "$f" == *L[0-9].v ]] && continue
  [[ "$f" == Snakelet* ]] && continue
  [[ "$f" == SpecPrelude* ]] && continue
  coqc -q "$f" 2>/dev/null || { echo "FAIL: $f"; exit 1; }
done
echo "  deps compiled"

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
    # Launch model
    (
      t0=$(date +%s)
      timeout "$TIMEOUT" opencode run --model "$MODEL" --format json \
        --dangerously-skip-permissions --dir "$W" \
        "Prove all Admitted theorems in $f. Use edit_file for edits. Read the file first, then write proofs." \
        > "$RESULT_DIR/${f%.v}.jsonl" 2>/dev/null
      t1=$(date +%s)
      qed=$(grep -c 'Qed\.' "$W/$f" 2>/dev/null || echo 0)
      admits=$(grep -c 'Admitted\.' "$W/$f" 2>/dev/null || echo 0)
      if coqc -q "$W/$f" 2>/dev/null; then
        echo "  $f: SOLVED ($((t1-t0))s, ${qed}qed)"
      else
        echo "  $f: FAILED ($((t1-t0))s, ${qed}qed/${admits}admits)"
      fi
    ) &
    pids+=($!)
  done
  for pid in "${pids[@]}"; do wait "$pid"; done
  echo "  phase $((pi+1)) done"
done

END=$(date +%s)
echo "=== $CONTRACT: wall $((END-START))s, results in $RESULT_DIR ==="
rm -rf "$W"

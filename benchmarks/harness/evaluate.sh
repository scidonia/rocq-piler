#!/usr/bin/env bash
set -euo pipefail

# evaluate.sh — Check a completed .v file against its incomplete reference
# Usage: evaluate.sh <complete_file> --reference <incomplete_file> [-- coq_flags...]
# Output: JSON object with results to stdout
# Checks: compilation, conjecture pairs, AND axiom soundness (Print Assumptions)

COMPLETE=""
INCOMPLETE=""
COQ_FLAGS=()

while [[ $# -gt 0 ]]; do
  case $1 in
    --reference) INCOMPLETE="$2"; shift 2 ;;
    --) shift; COQ_FLAGS=("$@"); break ;;
    *) [[ -z "$COMPLETE" ]] && COMPLETE="$1" || COQ_FLAGS+=("$1"); shift ;;
  esac
done

[[ -z "$COMPLETE" ]] && { echo '{"error":"Usage: evaluate.sh <complete> --reference <incomplete>"}'; exit 1; }

if [[ ! -f "$COMPLETE" ]]; then
  echo '{"error":"complete file not found","file":"'"$COMPLETE"'"}'
  exit 1
fi

# 1. Try to compile
coqc "${COQ_FLAGS[@]}" "$COMPLETE" >/dev/null 2>&1 && COMPILES=true || COMPILES=false

# Helper: extract theorem/lemma name → qed/admitted from a .v file
extract_statuses() {
  awk '
    /^[[:space:]]*(Theorem|Lemma)[[:space:]]/ {
      name = $2
      gsub(/:$/, "", name)
      waiting = 1
    }
    waiting && /Qed\./ {
      print name, "qed"
      waiting = 0
    }
    waiting && /Admitted\./ {
      print name, "admitted"
      waiting = 0
    }
  ' "$1"
}

# 2. Discover pairs from the INCOMPLETE (reference) file
declare -A REF_PAIRS=()  # base_name -> 1
if [[ -n "$INCOMPLETE" && -f "$INCOMPLETE" ]]; then
  while IFS=' ' read -r name status; do
    [[ -z "$name" ]] && continue
    if [[ "$name" == *_neg ]]; then
      base="${name%_neg}"
      REF_PAIRS["$base"]=1
    fi
  done <<< "$(extract_statuses "$INCOMPLETE")"
fi

# 3. Extract statuses from the COMPLETE file
declare -A COMPLETE_STATUS
while IFS=' ' read -r name status; do
  [[ -z "$name" ]] && continue
  COMPLETE_STATUS["$name"]="$status"
done <<< "$(extract_statuses "$COMPLETE")"

# 4. Check axiom soundness for Qed theorems using Print Assumptions
declare -A AXIOM_STATUS  # name -> "sound" or "unsound:axiom1,axiom2,..."
if [[ "$COMPILES" == "true" ]]; then
  QED_NAMES=()
  for name in "${!COMPLETE_STATUS[@]}"; do
    [[ "${COMPLETE_STATUS[$name]}" == "qed" ]] && QED_NAMES+=("$name")
  done

  if [[ ${#QED_NAMES[@]} -gt 0 ]]; then
    CHECK_FILE=$(mktemp /tmp/eval_check_XXXXXX.v)
    trap "rm -f $CHECK_FILE" EXIT

    # Copy the complete file and append Print Assumptions for each Qed theorem
    cp "$COMPLETE" "$CHECK_FILE"
    for name in "${QED_NAMES[@]}"; do
      echo "Print Assumptions ${name}." >> "$CHECK_FILE"
    done

    # Run coqc and capture assumptions output
    ASSUMPTIONS_OUTPUT=$(coqc "${COQ_FLAGS[@]}" "$CHECK_FILE" 2>&1 || true)

    # Parse: for each theorem, check if "Closed under the global context" or has axioms
    current_theorem=""
    idx=0
    while IFS= read -r line; do
      if echo "$line" | grep -q "Closed under the global context"; then
        if [[ $idx -lt ${#QED_NAMES[@]} ]]; then
          AXIOM_STATUS["${QED_NAMES[$idx]}"]="sound"
          idx=$((idx + 1))
        fi
      elif echo "$line" | grep -q "^Axioms:"; then
        # Collect axiom names until next blank line or Print Assumptions
        axioms=""
        while IFS= read -r aline; do
          [[ -z "$aline" ]] && break
          echo "$aline" | grep -q "^Axioms:" && break
          echo "$aline" | grep -q "Closed under" && break
          # Extract axiom name (first word before :)
          aname=$(echo "$aline" | sed 's/^\s*//' | cut -d' ' -f1 | tr -d ':')
          [[ -n "$aname" ]] && axioms="${axioms:+$axioms,}$aname"
        done
        if [[ $idx -lt ${#QED_NAMES[@]} ]]; then
          # Check if axioms are all from standard library
          has_internal=false
          for ax in $(echo "$axioms" | tr ',' ' '); do
            # Standard axioms contain dots (Stdlib.Logic.Classical_Prop.classic etc)
            if ! echo "$ax" | grep -q '\.'; then
              # No dot = likely an internal admitted lemma
              has_internal=true
            fi
          done
          if [[ "$has_internal" == "true" ]]; then
            AXIOM_STATUS["${QED_NAMES[$idx]}"]="unsound:$axioms"
          else
            AXIOM_STATUS["${QED_NAMES[$idx]}"]="sound"
          fi
          idx=$((idx + 1))
        fi
      fi
    done <<< "$ASSUMPTIONS_OUTPUT"
  fi
fi

# 5. Evaluate pairs (now considering axiom soundness)
PAIRS_JSON="{"
PAIRS_TOTAL=0
PAIRS_RESOLVED=0
SEPARATOR=""

if [[ ${#REF_PAIRS[@]} -gt 0 ]]; then
  for base in "${!REF_PAIRS[@]}"; do
    PAIRS_TOTAL=$((PAIRS_TOTAL + 1))
    pos="${COMPLETE_STATUS[$base]:-missing}"
    neg="${COMPLETE_STATUS[${base}_neg]:-missing}"
    pos_sound="${AXIOM_STATUS[$base]:-unknown}"
    neg_sound="${AXIOM_STATUS[${base}_neg]:-unknown}"

    # A theorem only counts as proved if Qed AND axiom-sound
    pos_valid=$([[ "$pos" == "qed" && "$pos_sound" == "sound" ]] && echo true || echo false)
    neg_valid=$([[ "$neg" == "qed" && "$neg_sound" == "sound" ]] && echo true || echo false)

    if [[ "$pos_valid" == "true" ]]; then
      pair_result="proved"
      PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
    elif [[ "$neg_valid" == "true" ]]; then
      pair_result="refuted"
      PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
    elif [[ "$pos" == "qed" && "$pos_sound" != "sound" ]]; then
      pair_result="unsound"
    elif [[ "$neg" == "qed" && "$neg_sound" != "sound" ]]; then
      pair_result="unsound"
    else
      pair_result="neither"
    fi

    PAIRS_JSON="${PAIRS_JSON}${SEPARATOR}\"${base}\":\"${pair_result}\""
    SEPARATOR=","
  done
else
  for name in "${!COMPLETE_STATUS[@]}"; do
    PAIRS_TOTAL=$((PAIRS_TOTAL + 1))
    if [[ "${COMPLETE_STATUS[$name]}" == "qed" ]]; then
      sound="${AXIOM_STATUS[$name]:-unknown}"
      [[ "$sound" == "sound" ]] && PAIRS_RESOLVED=$((PAIRS_RESOLVED + 1))
    fi
  done
fi
PAIRS_JSON="${PAIRS_JSON}}"

cat <<EOF
{
  "file": "$COMPLETE",
  "compiles": $COMPILES,
  "pairs_total": $PAIRS_TOTAL,
  "pairs_resolved": $PAIRS_RESOLVED,
  "pairs": $PAIRS_JSON
}
EOF

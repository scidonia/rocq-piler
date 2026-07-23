#!/usr/bin/env bash
set -euo pipefail

# run.sh — Run one benchmark problem with one model and MCP profile
# Usage: run.sh --model <provider/model> --problem <name> [--profile full|positional|none|rocq-mcp|<path>] [--timeout <seconds>]

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BENCH_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_DIR="$(cd "$BENCH_DIR/.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"

MODEL=""
PROBLEM=""
PROFILE="standard"
TIMEOUT=1800

while [[ $# -gt 0 ]]; do
  case $1 in
    --model) MODEL="$2"; shift 2 ;;
    --problem) PROBLEM="$2"; shift 2 ;;
    --profile) PROFILE="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    *) echo "Unknown flag: $1" >&2; exit 1 ;;
  esac
done

[[ -z "$MODEL" ]] && { echo "Missing --model" >&2; exit 1; }
[[ -z "$PROBLEM" ]] && { echo "Missing --problem" >&2; exit 1; }

INCOMPLETE="$BENCH_DIR/incomplete/${PROBLEM}.v"
INSTRUCTIONS="$BENCH_DIR/incomplete/${PROBLEM}.md"

if [[ ! -f "$INCOMPLETE" ]]; then
  echo "Challenge file not found: $INCOMPLETE" >&2
  exit 1
fi

if [[ ! -f "$INSTRUCTIONS" ]]; then
  PROMPT="Copy benchmarks/incomplete/${PROBLEM}.v to benchmarks/complete/${PROBLEM}.v and prove all Admitted theorems. For conjecture pairs (foo and foo_neg), prove exactly one of each pair. Do not modify the incomplete file. Write helper lemmas as needed — only add them when the main proof requires one. Start with the simplest lemmas and build up."
else
  PROMPT="Read benchmarks/incomplete/${PROBLEM}.md and follow the instructions."
fi

TIMESTAMP=$(date -u +%Y-%m-%dT%H:%M:%SZ)
SAFE_TIMESTAMP=$(echo "$TIMESTAMP" | tr ':' '-')
SAFE_MODEL=$(echo "$MODEL" | tr '/' '_')
RUN_ID="$(echo "${PROBLEM}_${SAFE_MODEL}_${PROFILE}_$(date +%s)_$$" | tr '/' '_')"
JSON_LOG="/tmp/opencode_bench_${RUN_ID}.jsonl"

# Git hash of rocq-piler for reproducibility
GIT_HASH=$(git -C "$REPO_DIR" rev-parse --short HEAD 2>/dev/null || echo "unknown")

# Per-run results directory
RUN_DIR="$RESULTS_DIR/${SAFE_TIMESTAMP}_${PROBLEM}_${SAFE_MODEL}_${PROFILE}"
mkdir -p "$RUN_DIR"

# Resolve MCP profile
GLOBAL_CONFIG="$HOME/.config/opencode/opencode.json"
ROCQ_PILER_DIST="$REPO_DIR/dist/index.js"
COQ_LSP_PATH=$(jq -r '(.mcpServers // .mcp // {})["rocq-piler"].command[-1] // empty' "$GLOBAL_CONFIG" 2>/dev/null || true)
[[ -z "$COQ_LSP_PATH" ]] && COQ_LSP_PATH="coq-lsp"
ROCQ_MCP_BIN=$(command -v rocq-mcp 2>/dev/null || echo "$HOME/dev/Scidonia/rocq-mcp/.venv/bin/rocq-mcp")

resolve_profile() {
  local profile="$1"
  local profile_file

  case "$profile" in
    full|positional|none|rocq-mcp|standard|lean|robust|working-admits)
      profile_file="$SCRIPT_DIR/profiles/${profile}.json"
      ;;
    *)
      profile_file="$profile"
      ;;
  esac

  if [[ ! -f "$profile_file" ]]; then
    echo "Profile not found: $profile_file" >&2
    exit 1
  fi

  sed -e "s|ROCQ_PILER_DIST|$ROCQ_PILER_DIST|g" \
      -e "s|COQ_LSP_PATH|$COQ_LSP_PATH|g" \
      -e "s|ROCQ_MCP_BIN|$ROCQ_MCP_BIN|g" \
      "$profile_file"
}

RESOLVED_CONFIG=$(resolve_profile "$PROFILE")

# Create isolated working copy
WORKDIR=$(mktemp -d "/tmp/bench_${RUN_ID}_XXXXXX")
trap "rm -rf $WORKDIR" EXIT

echo "[$RUN_ID] Setting up workspace in $WORKDIR ..." >&2

# Minimal scaffold — only the files the LLM needs, nothing to cheat from
mkdir -p "$WORKDIR/benchmarks/incomplete"

# Handle multi-file benchmarks: if PROBLEM contains '/', copy the whole directory
if [[ "$PROBLEM" == */* ]]; then
  local dir="${PROBLEM%%/*}"
  cp -r "$BENCH_DIR/incomplete/${dir}" "$WORKDIR/benchmarks/incomplete/"
else
  cp -f "$BENCH_DIR/incomplete/${PROBLEM}.v" "$WORKDIR/benchmarks/incomplete/"
fi
[[ -f "$INSTRUCTIONS" ]] && cp -f "$INSTRUCTIONS" "$WORKDIR/benchmarks/incomplete/"
# Copy profile-specific AGENTS.md if available, otherwise default
if [[ -f "$SCRIPT_DIR/profiles/${PROFILE}.agents.md" ]]; then
  cp -f "$SCRIPT_DIR/profiles/${PROFILE}.agents.md" "$WORKDIR/AGENTS.md"
else
  cp -f "$REPO_DIR/AGENTS.md" "$WORKDIR/AGENTS.md" 2>/dev/null || true
fi

# Minimal _CoqProject for coq-lsp workspace detection
echo "-R . McpCoqLspBenchmark" > "$WORKDIR/benchmarks/_CoqProject"

# Init a bare git repo (opencode expects one)
git -C "$WORKDIR" init --quiet 2>/dev/null
git -C "$WORKDIR" add -A && git -C "$WORKDIR" commit --quiet -m "init" 2>/dev/null || true

# Write MCP profile as project-local opencode config
# Write profile as project-local opencode.json
# The "tools" section with glob patterns hides unwanted MCP tools from the LLM
# (see https://opencode.ai/docs/mcp-servers/#manage)
echo "$RESOLVED_CONFIG" > "$WORKDIR/opencode.json"

# Extract MCP list from the resolved profile
MCP_LIST=$(echo "$RESOLVED_CONFIG" | jq -c '[(.mcpServers // .mcp // {}) | to_entries[] | select(.value.enabled != false) | {name: .key, command: (.value.command // [] | join(" ")), enabled: (.value.enabled // true)}]' 2>/dev/null || echo "[]")

# Run opencode
echo "[$RUN_ID] Running model=$MODEL problem=$PROBLEM profile=$PROFILE timeout=${TIMEOUT}s ..." >&2
START_TIME=$(date +%s)

timeout "$TIMEOUT" opencode run \
  --model "$MODEL" \
  --format json \
  --dangerously-skip-permissions \
  --dir "$WORKDIR" \
  --title "bench:${PROBLEM}:${MODEL}:${PROFILE}" \
  "$PROMPT" \
  > "$JSON_LOG" 2>/dev/null || true

END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

# Save transcript
cp "$JSON_LOG" "$RUN_DIR/transcript.jsonl"

# Save solution if created
COMPLETE_FILE="$WORKDIR/benchmarks/complete/${PROBLEM}.v"
if [[ -f "$COMPLETE_FILE" ]]; then
  cp "$COMPLETE_FILE" "$RUN_DIR/solution.v"
fi

# Extract token data from step_finish events
TOKENS_IN=$(jq -s '[.[] | select(.type=="step_finish") | .part.tokens.input // 0] | add // 0' "$JSON_LOG")
TOKENS_OUT=$(jq -s '[.[] | select(.type=="step_finish") | .part.tokens.output // 0] | add // 0' "$JSON_LOG")
TOKENS_REASONING=$(jq -s '[.[] | select(.type=="step_finish") | .part.tokens.reasoning // 0] | add // 0' "$JSON_LOG")
TOKENS_CACHE_READ=$(jq -s '[.[] | select(.type=="step_finish") | .part.tokens.cache.read // 0] | add // 0' "$JSON_LOG")
TOKENS_CACHE_WRITE=$(jq -s '[.[] | select(.type=="step_finish") | .part.tokens.cache.write // 0] | add // 0' "$JSON_LOG")
TOTAL_COST=$(jq -s '[.[] | select(.type=="step_finish") | .part.cost // 0] | add // 0' "$JSON_LOG")
SESSION_ID=$(jq -rs '[.[] | .sessionID // empty][0] // "unknown"' "$JSON_LOG")
STEP_COUNT=$(jq -s '[.[] | select(.type=="step_finish")] | length' "$JSON_LOG")

# Extract ACTUAL tool usage from transcript (not just configured MCPs)
TOOLS_USED=$(jq -r 'select(.type=="tool_use") | .part.tool // "?"' "$JSON_LOG" | sort | uniq -c | sort -rn | awk '{printf "{\"tool\":\"%s\",\"count\":%s},",$2,$1}' | sed 's/,$//' | awk '{print "["$0"]"}')
[[ -z "$TOOLS_USED" || "$TOOLS_USED" == "[]" ]] && TOOLS_USED="[]"

# Evaluate the result
INCOMPLETE_REF="$WORKDIR/benchmarks/incomplete/${PROBLEM}.v"
if [[ -f "$COMPLETE_FILE" ]]; then
  EVAL_RESULT=$(bash "$SCRIPT_DIR/evaluate.sh" "$COMPLETE_FILE" --reference "$INCOMPLETE_REF" -- -R "$WORKDIR/benchmarks" McpCoqLspBenchmark 2>/dev/null || echo '{"compiles":false,"pairs_total":0,"pairs_resolved":0,"pairs":{}}')
else
  EVAL_RESULT='{"compiles":false,"pairs_total":0,"pairs_resolved":0,"pairs":{},"error":"file not created"}'
fi

# Build result record
RECORD=$(jq -n \
  --arg timestamp "$TIMESTAMP" \
  --arg model "$MODEL" \
  --arg problem "$PROBLEM" \
  --arg profile "$PROFILE" \
  --arg session_id "$SESSION_ID" \
  --arg git_hash "$GIT_HASH" \
  --arg run_dir "$RUN_DIR" \
  --argjson duration "$DURATION" \
  --argjson tokens_in "$TOKENS_IN" \
  --argjson tokens_out "$TOKENS_OUT" \
  --argjson tokens_reasoning "$TOKENS_REASONING" \
  --argjson tokens_cache_read "$TOKENS_CACHE_READ" \
  --argjson tokens_cache_write "$TOKENS_CACHE_WRITE" \
  --argjson cost "$TOTAL_COST" \
  --argjson steps "$STEP_COUNT" \
  --argjson eval "$EVAL_RESULT" \
  --argjson mcps "$MCP_LIST" \
  --argjson tools_used "$TOOLS_USED" \
  '{
    timestamp: $timestamp,
    model: $model,
    problem: $problem,
    profile: $profile,
    git_hash: $git_hash,
    session_id: $session_id,
    duration_s: $duration,
    tokens: {
      input: $tokens_in,
      output: $tokens_out,
      reasoning: $tokens_reasoning,
      cache_read: $tokens_cache_read,
      cache_write: $tokens_cache_write
    },
    cost: $cost,
    steps: $steps,
    mcps: $mcps,
    tools_used: $tools_used,
    eval: $eval
  }')

# Write to per-run directory and append to summary (compact JSONL)
echo "$RECORD" | jq . > "$RUN_DIR/result.json"
echo "$RECORD" | jq -c . >> "$RESULTS_DIR/summary.jsonl"
echo "$RECORD" | jq .

echo "[$RUN_ID] Done. duration=${DURATION}s cost=\$${TOTAL_COST}" >&2
echo "[$RUN_ID] Results in: $RUN_DIR" >&2

rm -f "$JSON_LOG"

#!/usr/bin/env bash
set -euo pipefail

echo "=== Step 1: Generate & Lean-4.36-Verify Stage 1 Pure Lean Corpus ==="
python3 -m src.gen_stage1_pure_lean

echo "=== Step 2: Generate & Lean-4.36-Verify Stage 2 Sketchpad SFT Dataset ==="
python3 -m src.gen_stage2_sketchpad_sft

echo "=== Step 3: Generate & Lean-4.36-Verify Stage 3 Hard GRPO + Holdout Benchmarks ==="
python3 -m src.gen_stage3_hard_questions

echo "=== Step 4: Train & Merge Stage 1 Pure Lean 3B Model ==="
python3 -m src.train_stage1_pure_lean

echo "=== Step 5: Train & Merge Stage 2 Sketchpad SFT 3B Model ==="
python3 -m src.train_stage2_sft

echo "=== Step 6: Run Per-Question Multi-Round GRPO Until >=75% Mastery ==="
python3 -m src.train_stage3_grpo

echo "=== Step 7: Evaluate All 4 Checkpoints Against Lean 4.36 Kernel ==="
python3 -m src.eval_pipeline

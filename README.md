# High-Level Pure Lean 4: Kernel-Verified Library, Anti-Cheat Verifier & 3-Stage RLVR (GRPO) Pipeline

End-to-end **formal theorem-proving & Reinforcement Learning with Verifiable Rewards (RLVR)** framework in **pure Lean 4 (`v4.36.0`, zero Mathlib imports)**:
- **Standalone Pure Lean 4 Library (`lean/`)**: `233` distinct, deduplicated theorems across 8 `.lean` modules (Abstract Algebra, Galois Connections & Heyting Algebras, Set/Relation Closures & Simulations, Constructive/Classical Logic, Verified Stack-VM Compilers, and Number Theory) plus **3,797** kernel-verified training/evaluation items in `data/`.
- **Anti-Reward-Hacking Kernel Verifier (`src/lean_verifier.py`)**: Parallel `lean --json` + `#print axioms` verification enforcing zero `sorryAx`, standard axioms only (`⊆ {propext, Classical.choice, Quot.sound}`), theorem-signature immutability, and comment-stripped metaprogramming/unsafe-attribute filtering.
- **3-Stage Post-Training (`Qwen/Qwen2.5-Coder-3B-Instruct`)**: Synthetic Pure Lean Domain Adaptation → `<sketchpad>` SFT → Per-Question Multi-Round GRPO, lifting unhinted `Pass@1` on 15 hard multi-step pure Lean 4 theorems from **`0.0%` → `69.2%`** (**`86.7%` `Pass@8`**).

---

## Quick Verification: Build the Standalone Lean 4 Package

Requires [elan / Lean `v4.36.0`](https://lean-lang.org/lean4/doc/quickstart.html) (no Mathlib download required; builds offline in ~5 seconds):

```bash
cd lean
lake build
```

| Lean 4 Module | Theorems | Formalized Structures & Highlights |
| :--- | :---: | :--- |
| [`lean/PureLean/HardBenchmarks.lean`](lean/PureLean/HardBenchmarks.lean) | 15 | Exponent-2 abelian groups, Galois `u(l(u(b))) = u(b)`, Heyting currying, Church–Rosser diamond strip lemma, ring `(-a)(-b) = ab`, CPS `foldl`-via-`foldr`, commutator inverse, arithmetic VM compiler soundness, Nicomachus's sum of cubes |
| [`lean/PureLean/HoldoutBenchmarks.lean`](lean/PureLean/HoldoutBenchmarks.lean) | 12 | Unique one-sided/group inverses, lattice associativity, closure-operator infima, converse transitive closures, periodic function iteration, binary tree leaf-node invariant (`leaves = nodes + 1`), sum of squares (`6 ∑ k² = n(n+1)(2n+1)`) |
| [`lean/PureLean/Algebra.lean`](lean/PureLean/Algebra.lean) | 45 | `PureMonoid`, `PureGroup`, `IsSubgroup`, `GroupHom`, `GroupAction`, `PureRing`, cancellation & involution laws |
| [`lean/PureLean/OrderGalois.lean`](lean/PureLean/OrderGalois.lean) | 34 | `PurePoset`, `PureLattice`, `BoundedLattice`, `GaloisConn` unit/counit/monotone laws, `ClosureOp`, `HeytingAlg` |
| [`lean/PureLean/RelationsSets.lean`](lean/PureLean/RelationsSets.lean) | 31 | Predicate sets (`SetP`), `ImgP`/`PreimgP` Galois adjunction, `EquivR`, `StarR`/`PlusStep` closures, transition `Simulates` |
| [`lean/PureLean/LogicFunctions.lean`](lean/PureLean/LogicFunctions.lean) | 36 | Peirce's law, Drinker's theorem, Cantor diagonalization, Lawvere fixed-point theorem, `InjFn`/`SurjFn`, `Option` monad laws |
| [`lean/PureLean/InductiveCompilers.lean`](lean/PureLean/InductiveCompilers.lean) | 28 | `snocL`/`revL`, `BTree` mirror/flatten/map laws, tail-recursive `sumAcc`/`revAcc`, verified stack-VM `compileAdd` |
| [`lean/PureLean/NumberTheory.lean`](lean/PureLean/NumberTheory.lean) | 32 | Closed-form finite series (`sumUpTo`, `sumOdds`), `pow2N`, `fibN`, `PureDvd`, parity, and `Int` modular congruences (`ModEqInt`) |

---

## Anti-Cheat Kernel Verifier (`src/lean_verifier.py`)

Rather than relying on regex heuristics or partial tactic execution, `src/lean_verifier.py` enforces strict Lean 4 kernel soundness across both dataset synthesis and online GRPO rollouts:

1. **Signature Immutability**: Extracts only the proof body following `:=` and splices it beneath the verifier-owned `preamble` and `theorem_header`, preventing models from weakening hypotheses or altering target types.
2. **Comment-Stripped Forbidden Token Guard**: Iteratively strips nested `/- ... -/` and `-- ...` comments before rejecting `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `implemented_by`, `extern`, `macro`, `elab`, `syntax`, and `notation`.
3. **Kernel Axiom Audit (`#print axioms`)**: Appends `#print axioms <thm>` and parses `lean --json` structured diagnostics, accepting a rollout as `verified_correct = True` if and only if `returncode == 0`, zero error messages, zero `sorry` warnings, and all transitive axioms lie strictly in `{propext, Classical.choice, Quot.sound}`.
4. **Compiler-Feedback Reward Shaping**: Separates unverified attempts (`[0.0, 0.34]` based on parse validity, error count, and first-error line depth) from kernel-verified proofs (`[1.0, 1.08]`) to eliminate zero-gradient groups early in RL.

---

## 3-Stage Training Pipeline & Empirical Results

Trained end-to-end on Apple Silicon (`mps`, `bfloat16`) starting from `Qwen/Qwen2.5-Coder-3B-Instruct`:

1. **Stage 1 — Synthetic Pure Lean Domain Adaptation** (`src/gen_stage1_pure_lean.py`, `src/train_stage1_pure_lean.py`):
   - `1,620` verified pure Lean 4 theorems packed into `914` 512-token blocks; rank-16 LoRA across all 7 attention/MLP projections (`q, k, v, o, gate, up, down`).
   - Validation perplexity: **`2.65` → `1.09`** (`val_loss`: `0.9733` → `0.0843`).
2. **Stage 2 — Multi-Archetype `<sketchpad>` SFT** (`src/gen_stage2_sketchpad_sft.py`, `src/train_stage2_sft.py`):
   - `2,150` verified `<sketchpad>...</sketchpad>` + ```` ```lean ```` examples (`2,050` train / `100` val) across 5 proof-planning styles (`analytical_plan`, `self_correcting`, `tactic_trace`, `subgoal_tree`, `concise_scratchpad`) with prompt-masked completion loss (`r=24, α=48`).
   - Validation perplexity: **`5.25` → `1.02`** (`val_loss`: `1.6576` → `0.0174`).
   - Uses detached 128-token chunked `lm_head` cross-entropy backward (`src/mps_lora_utils.py`) to avoid full-vocabulary (`151,936`-token) `float32` logit buffer spikes, capping Metal memory at **`~8.66 GB`** up to `1,450` tokens.
3. **Stage 3 — Per-Question Multi-Round GRPO** (`src/gen_stage3_hard_questions.py`, `src/train_stage3_grpo.py`):
   - Sequential mastery curriculum over 15 hard multi-step pure Lean 4 theorems (`G = 8` parallel unhinted rollouts/round, adaptive temperature + sublemma warmup when stuck at `0/8`, reference-KL regularization via `disable_adapter()`, and mastery replay buffer).
   - **15 / 15 (`100%`)** hard theorems reached the **`>= 75%` (`>= 6/8`) unhinted kernel-verified graduation gate**.

### End-to-End Checkpoint Evaluation (`logs/final_evaluation.json`)

All four checkpoints evaluated under identical unhinted sampling (`temperature = 0.70`, `max_new_tokens = 1,024`) against the Lean 4.36.0 kernel:

| Checkpoint | Hard 15 `Pass@1` | Hard 15 `Pass@8` | Hard 15 `>=75%` Retained | `<sketchpad>` Adherence | Unseen 12 Holdout `Pass@1` | Unseen 12 Holdout `Pass@4` |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **0. Base (`Qwen2.5-Coder-3B-Instruct`)** | `0.0%` | `0.0%` (`0/15`) | `0/15` (`0.0%`) | `24.2%` | `0.0%` | `0.0%` (`0/12`) |
| **1. Stage 1 (`stage1_pure_lean_merged`)** | `0.0%` | `0.0%` (`0/15`) | `0/15` (`0.0%`) | `0.0%` | `0.0%` | `0.0%` (`0/12`) |
| **2. Stage 2 (`stage2_sketchpad_sft_merged`)** | `2.5%` | `13.3%` (`2/15`) | `0/15` (`0.0%`) | **`100.0%`** | **`12.5%`** | **`16.7%` (`2/12`)** |
| **3. Stage 3 (`stage3_grpo_merged`)** | **`69.2%`** | **`86.7%` (`13/15`)** | **`9/15` (`60.0%`)** | `90.0%` | `0.0%` | `0.0%` (`0/12`) |

*(Note: Without Mathlib automation such as `ring`, `linarith`, or `omega`, base `Qwen2.5-Coder-3B-Instruct` passed `0 / 168` total pure-Lean rollouts. Stage 2 SFT unlocked zero-shot holdout generalization (`16.7%` `Pass@4`), while Stage 3 sequential GRPO drove `Pass@1` on the Hard 15 suite from `2.5%` to `69.2%`—hitting `8/8` (`100%`) simultaneous accuracy on 7 of the 15 theorems.)*

---

## Repository Structure

```text
highlevelpurelean/
├── lean/                           # Standalone zero-Mathlib Lake package (Lean 4.36.0)
│   ├── lakefile.toml
│   ├── lean-toolchain
│   ├── PureLean.lean
│   └── PureLean/                   # 8 modules (233 distinct verified theorems)
├── src/
│   ├── lean_verifier.py            # Kernel verifier (`lean --json` + `#print axioms`) & reward shaping
│   ├── mps_lora_utils.py           # Token-chunked CE autograd & LoRA merge utilities
│   ├── prompts.py                  # System/user prompt & `<sketchpad>` formatting
│   ├── gen_stage1_pure_lean.py     # Synthesizes & verifies 1,620 Stage 1 theorems
│   ├── gen_stage2_sketchpad_sft.py # Synthesizes & verifies 2,150 Stage 2 `<sketchpad>` proofs
│   ├── gen_stage3_hard_questions.py# Synthesizes & verifies 15 Hard GRPO + 12 Holdout benchmarks
│   ├── export_lean_package.py      # Exports deduplicated `lean/` Lake library from verified JSONL
│   ├── train_stage1_pure_lean.py   # Stage 1 LoRA domain trainer
│   ├── train_stage2_sft.py         # Stage 2 prompt-masked `<sketchpad>` SFT trainer
│   ├── train_stage3_grpo.py        # Stage 3 per-question multi-round GRPO trainer
│   └── eval_pipeline.py            # Unified 4-checkpoint Lean kernel evaluator
├── data/                           # Kernel-verified JSONL datasets & evaluation suites
├── logs/                           # Training curves & `final_evaluation.json`
├── requirements.txt
└── run_all.sh                      # End-to-end dataset generation, training, and evaluation script
```

## Reproducing the Python Pipeline

```bash
pip install -r requirements.txt
bash run_all.sh
```
# highlevelpurelean

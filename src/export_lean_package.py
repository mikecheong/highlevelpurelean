"""
Export a clean, deduplicated, zero-Mathlib Lake package (`lean/`) showcasing all
distinct mathematical & CS formalizations in High-Level Pure Lean:
- `PureLean/HardBenchmarks.lean`    (15 multi-step Stage 3 GRPO mastery theorems)
- `PureLean/HoldoutBenchmarks.lean` (12 unseen holdout evaluation theorems)
- `PureLean/Algebra.lean`           (Monoids, Groups, Subgroups, Homomorphisms, Rings)
- `PureLean/OrderGalois.lean`       (Posets, Lattices, Galois Connections, Closure Ops, Heyting Algebras)
- `PureLean/RelationsSets.lean`     (Predicate Sets, Image/Preimage Adjunctions, Star/Plus Closures, Simulations)
- `PureLean/LogicFunctions.lean`    (Constructive/Classical First-Order Logic, Cantor/Lawvere Fixed Points, Monads)
- `PureLean/InductiveCompilers.lean`(Lists, Binary Trees, Tail-Recursive Accumulators, Verified Stack-VM Compilers)
- `PureLean/NumberTheory.lean`      (Finite Series, Fibonacci/Powers, Divisibility, Integer Modular Arithmetic)
"""

from __future__ import annotations

import json
import os
import re
from collections import defaultdict
from typing import Dict, List, Set, Tuple

from src.lean_verifier import extract_theorem_name

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR = os.path.join(ROOT_DIR, "data")
LEAN_DIR = os.path.join(ROOT_DIR, "lean")
PKG_DIR = os.path.join(LEAN_DIR, "PureLean")

DOMAIN_SPECS: Dict[str, Tuple[str, str]] = {
    "algebra": (
        "Algebra",
        "Abstract Algebra: Pure Monoids, Groups, Subgroups, Group Actions, Homomorphisms, and Rings.",
    ),
    "order_lattice": (
        "OrderGalois",
        "Order Theory: Posets, Lattices, Galois Connections, Closure Operators, and Heyting Algebras.",
    ),
    "relations_sets": (
        "RelationsSets",
        "Set-Predicates, Image/Preimage Adjunctions, Equivalence Relations, Reflexive-Transitive Closures, and Simulations.",
    ),
    "logic_functions": (
        "LogicFunctions",
        "Constructive & Classical Logic, Cantor Diagonalization, Lawvere Fixed Points, Function Bijections, and Option Monads.",
    ),
    "inductive_ds": (
        "InductiveCompilers",
        "Inductive Data Structures, Binary Tree Mirrors/Traversals, Tail-Recursive Accumulators, and Stack-VM Compilers.",
    ),
    "nat_number_theory": (
        "NumberTheory",
        "Natural Number Recurrences, Closed-Form Series, Divisibility, Parity, and Integer Modular Congruences.",
    ),
}


def sanitize_ident(raw: str) -> str:
    cleaned = re.sub(r"[^A-Za-z0-9_]", "_", raw)
    if not cleaned or cleaned[0].isdigit():
        cleaned = "S_" + cleaned
    return cleaned


def clean_base_header(header: str, proof_body: str) -> Tuple[str, str]:
    thm_name = extract_theorem_name(header)
    base_name = re.sub(r"_\d+$", "", thm_name)
    if base_name != thm_name and not re.search(rf"\b{re.escape(thm_name)}\b", proof_body):
        header = re.sub(
            rf"\b(theorem|lemma)\s+{re.escape(thm_name)}\b",
            rf"\1 {base_name}",
            header,
            count=1,
        )
        return base_name, header
    return thm_name, header


def render_benchmark_module(title_comment: str, rows: List[Dict]) -> str:
    lines: List[str] = [
        f"/-!\n# {title_comment}\n\nZero-Mathlib pure Lean 4.36 formalizations verified by the Lean kernel.\n-/\n"
    ]
    for idx, r in enumerate(rows, start=1):
        ns = sanitize_ident(r["id"])
        thm_name = extract_theorem_name(r["theorem_header"])
        title = r.get("title", r["id"])
        domain = r.get("domain", "")
        preamble = r.get("preamble", "").strip()
        header = r["theorem_header"].strip()
        if not header.endswith(":="):
            header += " :="
        proof = r["reference_proof"].strip()

        lines.append(f"/-! ## {idx}. {title} (`{domain}`) -/")
        lines.append(f"namespace {ns}\n")
        if preamble:
            lines.append(preamble + "\n")
        lines.append(f"{header}\n{proof}\n")
        lines.append(f"#print axioms {thm_name}\n")
        lines.append(f"end {ns}\n")
    return "\n".join(lines)


def collect_distinct_domain_theorems() -> Dict[str, List[Dict]]:
    by_domain: Dict[str, List[Dict]] = defaultdict(list)
    seen_bases: Set[Tuple[str, str]] = set()

    # Prefer Stage 2 first (richer structures: Rings, Heyting algebras, Stack VM, Simulations, Cantor/Lawvere),
    # then fill remaining distinct Stage 1 theorem templates.
    sources = [
        os.path.join(DATA_DIR, "stage2_sketchpad_sft.jsonl"),
        os.path.join(DATA_DIR, "stage1_pure_lean.jsonl"),
    ]
    for src_path in sources:
        with open(src_path, "r", encoding="utf-8") as f:
            for line in f:
                row = json.loads(line)
                domain = row["domain"]
                thm_name = extract_theorem_name(row["theorem_header"])
                base = re.sub(r"_\d+$", "", thm_name)
                key = (domain, base)
                if key in seen_bases:
                    continue
                seen_bases.add(key)
                by_domain[domain].append(row)

    return by_domain


def render_domain_module(mod_name: str, doc_desc: str, rows: List[Dict]) -> str:
    lines: List[str] = [
        f"/-!\n# PureLean.{mod_name}\n\n{doc_desc}\nAll declarations and proofs use pure Lean 4 (zero Mathlib imports).\n-/\n",
        f"namespace PureLean.{mod_name}\n",
    ]

    # Group items sharing the exact same preamble so shared algebraic/inductive definitions
    # appear cleanly once per section rather than repeating per theorem.
    grouped: Dict[str, List[Dict]] = defaultdict(list)
    preamble_order: List[str] = []
    for r in rows:
        pre = r.get("preamble", "").strip()
        if pre not in grouped:
            preamble_order.append(pre)
        grouped[pre].append(r)

    for sec_idx, pre in enumerate(preamble_order, start=1):
        sec_ns = f"Section{sec_idx:02d}"
        lines.append(f"namespace {sec_ns}\n")
        if pre:
            lines.append(pre + "\n")
        used_names: Set[str] = set()
        for r in grouped[pre]:
            proof = r["proof_body"].strip()
            clean_name, clean_hdr = clean_base_header(r["theorem_header"].strip(), proof)
            if clean_name in used_names:
                clean_hdr = r["theorem_header"].strip()
                clean_name = extract_theorem_name(clean_hdr)
            used_names.add(clean_name)
            if not clean_hdr.endswith(":="):
                clean_hdr += " :="
            lines.append(f"{clean_hdr}\n{proof}\n")
        lines.append(f"end {sec_ns}\n")

    lines.append(f"end PureLean.{mod_name}\n")
    return "\n".join(lines)


def main() -> None:
    os.makedirs(PKG_DIR, exist_ok=True)

    with open(os.path.join(LEAN_DIR, "lean-toolchain"), "w", encoding="utf-8") as f:
        f.write("leanprover/lean4:v4.36.0\n")

    with open(os.path.join(LEAN_DIR, "lakefile.toml"), "w", encoding="utf-8") as f:
        f.write(
            'name = "purelean"\n'
            'version = "0.1.0"\n'
            'defaultTargets = ["PureLean"]\n\n'
            "[[lean_lib]]\n"
            'name = "PureLean"\n'
        )

    with open(os.path.join(DATA_DIR, "stage3_hard_grpo.jsonl"), "r", encoding="utf-8") as f:
        hard_rows = [json.loads(line) for line in f]
    with open(os.path.join(DATA_DIR, "eval_holdout.jsonl"), "r", encoding="utf-8") as f:
        holdout_rows = [json.loads(line) for line in f]

    with open(os.path.join(PKG_DIR, "HardBenchmarks.lean"), "w", encoding="utf-8") as f:
        f.write(render_benchmark_module("Stage 3 Hard Multi-Step Pure Lean 4 Theorems (15 Problems)", hard_rows))

    with open(os.path.join(PKG_DIR, "HoldoutBenchmarks.lean"), "w", encoding="utf-8") as f:
        f.write(render_benchmark_module("Unseen Holdout Pure Lean 4 Evaluation Suite (12 Problems)", holdout_rows))

    domain_rows = collect_distinct_domain_theorems()
    exported_counts = {"HardBenchmarks": len(hard_rows), "HoldoutBenchmarks": len(holdout_rows)}
    imports = ["import PureLean.HardBenchmarks", "import PureLean.HoldoutBenchmarks"]

    for domain_key, (mod_name, doc_desc) in DOMAIN_SPECS.items():
        rows = domain_rows.get(domain_key, [])
        out_path = os.path.join(PKG_DIR, f"{mod_name}.lean")
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(render_domain_module(mod_name, doc_desc, rows))
        exported_counts[mod_name] = len(rows)
        imports.append(f"import PureLean.{mod_name}")

    with open(os.path.join(LEAN_DIR, "PureLean.lean"), "w", encoding="utf-8") as f:
        f.write("\n".join(imports) + "\n")

    total = sum(exported_counts.values())
    print(f"Exported {total} distinct pure Lean 4 theorems across {len(exported_counts)} modules:")
    for k, v in exported_counts.items():
        print(f"  - PureLean.{k}: {v} theorems")


if __name__ == "__main__":
    main()

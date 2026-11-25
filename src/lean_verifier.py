"""
Lean 4 formal verification engine with strict kernel axiom checking,
parallel rollout verification, fast chunked corpus verification, and
compiler-feedback shaped rewards for GRPO.
"""

from __future__ import annotations

import concurrent.futures
import json
import os
import re
import subprocess
import tempfile
from dataclasses import asdict, dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

FORBIDDEN_PROOF_PATTERNS = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\baxiom\b",
    r"\bconstant\b",
    r"\bopaque\b",
    r"\bunsafe\b",
    r"\bimplemented_by\b",
    r"\bextern\b",
    r"\bmacro\b",
    r"\belab\b",
    r"\bsyntax\b",
    r"\bnotation\b",
    r"\binfix[lr]?\b",
    r"\bprefix\b",
    r"\bpostfix\b",
]
FORBIDDEN_REGEX = re.compile("|".join(FORBIDDEN_PROOF_PATTERNS))

SKETCHPAD_REGEX = re.compile(r"<sketchpad>(.*?)</sketchpad>", re.DOTALL | re.IGNORECASE)
LEAN_FENCE_REGEX = re.compile(r"```(?:lean4?|)\s*\n(.*?)```", re.DOTALL | re.IGNORECASE)
THEOREM_NAME_REGEX = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b")


@dataclass
class VerificationResult:
    verified_correct: bool
    shaped_reward: float
    has_sketchpad: bool
    sketchpad_text: str
    extracted_proof: str
    error_count: int
    first_error_line: Optional[int]
    error_summary: str
    axioms_used: List[str]
    cheated: bool

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)


def strip_lean_comments(code: str) -> str:
    """Remove Lean line comments (-- ...) and non-nested/nested block comments (/- ... -/)."""
    # Remove nested block comments iteratively
    prev = None
    cur = code
    while prev != cur:
        prev = cur
        cur = re.sub(r"/\-(?:(?!/\-|\-/).)*?\-/", " ", cur, flags=re.DOTALL)
    cur = re.sub(r"--[^\n]*", "", cur)
    return cur


def extract_theorem_name(theorem_header: str) -> str:
    m = THEOREM_NAME_REGEX.search(theorem_header)
    if not m:
        raise ValueError(f"Could not extract theorem name from header: {theorem_header!r}")
    return m.group(1)


def extract_sketchpad_and_proof(
    response_text: str,
    theorem_header: str,
) -> Tuple[bool, str, str]:
    """
    Extract `<sketchpad>...</sketchpad>` reasoning and the Lean 4 proof body
    that follows `:=` for `theorem_header`.
    """
    sketch_match = SKETCHPAD_REGEX.search(response_text)
    has_sketchpad = sketch_match is not None
    sketchpad_text = sketch_match.group(1).strip() if sketch_match else ""

    # Search for code fences after </sketchpad> if present, else anywhere
    tail = response_text[sketch_match.end() :] if sketch_match else response_text
    fences = LEAN_FENCE_REGEX.findall(tail)
    if not fences:
        fences = LEAN_FENCE_REGEX.findall(response_text)

    if fences:
        raw_code = fences[-1].strip()
    else:
        # Fallback: take text after </sketchpad> or raw response
        raw_code = tail.strip()

    proof_body = normalize_proof_body(raw_code, theorem_header)
    return has_sketchpad, sketchpad_text, proof_body


def normalize_proof_body(raw_code: str, theorem_header: str) -> str:
    """
    Normalize model-generated Lean code into just the RHS proof term/tactic block
    after `<theorem_header> :=`, preventing signature tampering while supporting
    models that repeat the theorem declaration or write `by ...` directly.
    """
    code = raw_code.strip()
    if not code:
        return ""

    thm_name = extract_theorem_name(theorem_header)

    # If the model echoed `theorem <thm_name> ... := <proof>`, extract after `:=`
    decl_pattern = re.compile(
        rf"\b(?:theorem|lemma)\s+{re.escape(thm_name)}\b.*?:=\s*(.*)",
        re.DOTALL,
    )
    m = decl_pattern.search(code)
    if m:
        code = m.group(1).strip()
    else:
        # Also handle if the model wrote an unnamed/renamed theorem declaration
        generic_decl = re.compile(r"^\s*(?:theorem|lemma)\s+[A-Za-z_][A-Za-z0-9_']*\b.*?:=\s*(.*)", re.DOTALL)
        gm = generic_decl.match(code)
        if gm:
            code = gm.group(1).strip()

    if code.startswith(":="):
        code = code[2:].strip()

    return code


def check_forbidden_constructs(proof_body: str) -> Tuple[bool, str]:
    cleaned = strip_lean_comments(proof_body)
    if not cleaned.strip():
        return True, "empty_proof"
    m = FORBIDDEN_REGEX.search(cleaned)
    if m:
        return True, f"forbidden_token:{m.group(0)}"
    # Prevent closing a proof and injecting top-level commands
    if re.search(r"^\s*(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|namespace|section|end)\b", cleaned, re.MULTILINE):
        return True, "top_level_declaration_in_proof"
    return False, ""


def parse_axioms_output(messages: List[Dict[str, Any]], thm_name: str) -> Tuple[bool, List[str]]:
    """
    Inspect `#print axioms <thm_name>` info message from `lean --json`.
    Returns `(saw_print_axioms, axioms_list)`.
    """
    for msg in messages:
        if msg.get("severity") == "information":
            data = msg.get("data", "")
            if f"'{thm_name}' does not depend on any axioms" in data:
                return True, []
            m = re.search(rf"'{re.escape(thm_name)}' depends on axioms:\s*\[(.*?)\]", data, re.DOTALL)
            if m:
                axs = [a.strip() for a in m.group(1).split(",") if a.strip()]
                return True, axs
    return False, []


def verify_single_proof(
    preamble: str,
    theorem_header: str,
    response_text: str,
    require_sketchpad_for_bonus: bool = True,
    timeout_sec: float = 12.0,
) -> VerificationResult:
    """
    Verify a single model response against the Lean 4 kernel and compute both
    `verified_correct` (strict kernel soundness) and `shaped_reward` (for GRPO).
    """
    has_sketchpad, sketchpad_text, proof_body = extract_sketchpad_and_proof(response_text, theorem_header)
    thm_name = extract_theorem_name(theorem_header)
    header_clean = theorem_header.strip()
    if not header_clean.endswith(":="):
        header_clean = header_clean + " :="

    # Format bonus components for unverified shaping
    sketch_ok = has_sketchpad and (30 <= len(sketchpad_text) <= 2400)
    cheated, cheat_reason = check_forbidden_constructs(proof_body)

    if cheated:
        # Still award tiny format credit if sketchpad was structured, unless explicit `sorry`/`admit` cheat
        is_explicit_cheat = cheat_reason.startswith("forbidden_token:")
        shaped = 0.0 if is_explicit_cheat else (0.04 if sketch_ok else 0.0)
        return VerificationResult(
            verified_correct=False,
            shaped_reward=round(shaped, 4),
            has_sketchpad=has_sketchpad,
            sketchpad_text=sketchpad_text,
            extracted_proof=proof_body,
            error_count=1,
            first_error_line=None,
            error_summary=cheat_reason,
            axioms_used=[],
            cheated=is_explicit_cheat,
        )

    preamble_part = preamble.strip()
    assembled_prefix = (preamble_part + "\n\n" if preamble_part else "") + header_clean + "\n"
    prefix_line_count = assembled_prefix.count("\n")
    proof_line_count = max(1, proof_body.count("\n") + 1)

    full_lean_source = (
        f"{assembled_prefix}"
        f"{proof_body}\n\n"
        f"#print axioms {thm_name}\n"
    )

    fd, tmp_path = tempfile.mkstemp(suffix=".lean", prefix="verify_")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(full_lean_source)

        proc = subprocess.run(
            ["lean", "--json", tmp_path],
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    except subprocess.TimeoutExpired:
        return VerificationResult(
            verified_correct=False,
            shaped_reward=0.05 if sketch_ok else 0.01,
            has_sketchpad=has_sketchpad,
            sketchpad_text=sketchpad_text,
            extracted_proof=proof_body,
            error_count=1,
            first_error_line=None,
            error_summary="lean_timeout",
            axioms_used=[],
            cheated=False,
        )
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)

    messages: List[Dict[str, Any]] = []
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            messages.append(json.loads(line))
        except json.JSONDecodeError:
            pass

    errors = [m for m in messages if m.get("severity") == "error"]
    warnings = [m for m in messages if m.get("severity") == "warning"]
    uses_sorry_warning = any("sorry" in m.get("data", "").lower() for m in warnings)

    saw_axioms, axioms_used = parse_axioms_output(messages, thm_name)
    disallowed_axioms = [a for a in axioms_used if a not in ALLOWED_AXIOMS]

    verified_correct = (
        proc.returncode == 0
        and len(errors) == 0
        and not uses_sorry_warning
        and saw_axioms
        and len(disallowed_axioms) == 0
    )

    if verified_correct:
        bonus = 0.0
        if require_sketchpad_for_bonus:
            if sketch_ok:
                bonus += 0.06
            if "```lean" in response_text.lower():
                bonus += 0.02
        return VerificationResult(
            verified_correct=True,
            shaped_reward=round(1.0 + bonus, 4),
            has_sketchpad=has_sketchpad,
            sketchpad_text=sketchpad_text,
            extracted_proof=proof_body,
            error_count=0,
            first_error_line=None,
            error_summary="",
            axioms_used=axioms_used,
            cheated=False,
        )

    # Compute dense compiler-feedback shaped reward strictly in [0.0, 0.34]
    shaped = 0.0
    if sketch_ok:
        shaped += 0.06
    elif has_sketchpad:
        shaped += 0.02

    shaped += 0.05  # Non-empty forbidden-clean proof body

    first_err_line: Optional[int] = None
    err_summaries: List[str] = []
    syntax_error = False

    for err in errors[:3]:
        pos = err.get("pos") or {}
        line_no = pos.get("line")
        if isinstance(line_no, int):
            rel_line = max(1, line_no - prefix_line_count)
            if first_error_or_min(first_err_line, rel_line):
                first_err_line = rel_line
        data = err.get("data", "").strip()
        if any(k in data.lower() for k in ("unexpected token", "expected", "unknown parser", "unterminated")):
            syntax_error = True
        first_line_msg = data.splitlines()[0] if data else "error"
        err_summaries.append(first_line_msg[:140])

    if not syntax_error:
        shaped += 0.08  # Valid Lean 4 parse; errors are type/tactic state errors

    n_err = max(1, len(errors))
    err_count_score = 0.08 / (1.0 + 0.6 * (n_err - 1))
    if first_err_line is not None and proof_line_count > 1:
        depth_ratio = min(1.0, max(0.0, (first_err_line - 1) / proof_line_count))
    else:
        depth_ratio = 0.0
    depth_score = 0.07 * depth_ratio

    shaped = min(0.34, shaped + err_count_score + depth_score)

    if len(errors) == 0 and (disallowed_axioms or uses_sorry_warning):
        shaped = 0.0
        is_kernel_cheat = True
    else:
        is_kernel_cheat = False

    return VerificationResult(
        verified_correct=False,
        shaped_reward=round(shaped, 4),
        has_sketchpad=has_sketchpad,
        sketchpad_text=sketchpad_text,
        extracted_proof=proof_body,
        error_count=len(errors),
        first_error_line=first_err_line,
        error_summary="; ".join(err_summaries) if err_summaries else "verification_failed",
        axioms_used=axioms_used,
        cheated=is_kernel_cheat,
    )


def first_error_or_min(cur: Optional[int], cand: int) -> bool:
    return cur is None or cand < cur


def _verify_worker(args: Tuple[str, str, str, bool, float]) -> VerificationResult:
    return verify_single_proof(*args)


def verify_rollouts_parallel(
    preamble: str,
    theorem_header: str,
    responses: Sequence[str],
    require_sketchpad_for_bonus: bool = True,
    timeout_sec: float = 12.0,
    max_workers: int = 8,
) -> List[VerificationResult]:
    tasks = [
        (preamble, theorem_header, resp, require_sketchpad_for_bonus, timeout_sec)
        for resp in responses
    ]
    workers = min(max_workers, max(1, len(tasks)))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        return list(ex.map(_verify_worker, tasks))


def _verify_lean_chunk(
    chunk_items: List[Tuple[int, str]], timeout_sec: float = 30.0
) -> Tuple[bool, List[int], List[Tuple[int, str]]]:
    """
    Verify a batch of standalone Lean snippets wrapped in isolated namespaces.
    Uses line-range tracking from `lean --json` to pinpoint exact failing items in O(1) passes.
    """
    blocks: List[str] = []
    line_ranges: List[Tuple[int, int, int]] = []  # (start_line, end_line, item_idx)
    cur_line = 1
    for idx, snippet in chunk_items:
        block = f"namespace SyntheticVerify_{idx}\n{snippet.strip()}\nend SyntheticVerify_{idx}\n"
        n_lines = block.count("\n")
        line_ranges.append((cur_line, cur_line + n_lines - 1, idx))
        blocks.append(block)
        cur_line += n_lines + 1  # +1 for "\n".join separator
    source = "\n".join(blocks)

    fd, tmp_path = tempfile.mkstemp(suffix=".lean", prefix="chunk_")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(source)
        proc = subprocess.run(
            ["lean", "--json", tmp_path],
            capture_output=True,
            text=True,
            timeout=timeout_sec,
        )
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)

    bad_map: Dict[int, str] = {}
    for raw in proc.stdout.splitlines():
        if not raw.strip():
            continue
        try:
            msg = json.loads(raw)
        except json.JSONDecodeError:
            continue
        sev = msg.get("severity")
        data = msg.get("data", "")
        if sev == "error" or ("sorry" in data.lower()):
            pos = msg.get("pos") or {}
            ln = pos.get("line")
            if isinstance(ln, int):
                for s_ln, e_ln, idx in line_ranges:
                    if s_ln <= ln <= e_ln:
                        if idx not in bad_map:
                            bad_map[idx] = data[:240]
                        break

    if proc.returncode == 0 and not bad_map:
        return True, [idx for idx, _ in chunk_items], []

    if not bad_map:
        # Fallback bisect if an error lacked line metadata
        if len(chunk_items) == 1:
            return False, [], [(chunk_items[0][0], proc.stdout[:240] or proc.stderr[:240])]
        mid = len(chunk_items) // 2
        _, p1, f1 = _verify_lean_chunk(chunk_items[:mid], timeout_sec)
        _, p2, f2 = _verify_lean_chunk(chunk_items[mid:], timeout_sec)
        return False, p1 + p2, f1 + f2

    # Re-verify survivors cleanly in one pass to ensure no cascading parse effect
    survivors = [(idx, snip) for idx, snip in chunk_items if idx not in bad_map]
    failed_list = [(idx, err) for idx, err in bad_map.items()]
    if not survivors:
        return False, [], failed_list
    _, surv_passed, surv_failed = _verify_lean_chunk(survivors, timeout_sec)
    return False, surv_passed, failed_list + surv_failed


def verify_snippets_batch(
    snippets: Sequence[str],
    chunk_size: int = 80,
    max_workers: int = 8,
) -> Tuple[List[int], List[Tuple[int, str]]]:
    """
    Fast batch verification for thousands of synthetic pure Lean items.
    Returns `(valid_indices, failed_items_with_error)`.
    """
    indexed = list(enumerate(snippets))
    chunks = [indexed[i : i + chunk_size] for i in range(0, len(indexed), chunk_size)]

    valid_indices: List[int] = []
    failed_items: List[Tuple[int, str]] = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as ex:
        futures = {ex.submit(_verify_lean_chunk, ch): ch for ch in chunks}
        for fut in concurrent.futures.as_completed(futures):
            _, passed, failed = fut.result()
            valid_indices.extend(passed)
            failed_items.extend(failed)

    valid_indices.sort()
    failed_items.sort(key=lambda x: x[0])
    return valid_indices, failed_items

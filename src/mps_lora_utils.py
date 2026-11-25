"""
MPS-optimized 3B model loading, LoRA setup, adapter merging, memory-efficient
token-chunked cross-entropy loss, and zero-copy PEFT reference log-probabilities
for Qwen2.5-Coder-3B-Instruct on Apple Silicon (24 GB unified memory).
"""

from __future__ import annotations

import gc
import os
from typing import List, Optional, Tuple

import torch
import torch.nn as nn
import torch.nn.functional as F
from peft import LoraConfig, PeftModel, get_peft_model
from transformers import AutoModelForCausalLM, AutoTokenizer

DEFAULT_BASE_MODEL = "Qwen/Qwen2.5-Coder-3B-Instruct"
LORA_TARGET_MODULES = [
    "q_proj",
    "k_proj",
    "v_proj",
    "o_proj",
    "gate_proj",
    "up_proj",
    "down_proj",
]


def get_device() -> str:
    if torch.backends.mps.is_available():
        return "mps"
    if torch.cuda.is_available():
        return "cuda"
    return "cpu"


def load_tokenizer(model_path_or_id: str = DEFAULT_BASE_MODEL):
    local_only = not os.path.isdir(model_path_or_id)
    tok = AutoTokenizer.from_pretrained(
        model_path_or_id,
        local_files_only=local_only,
        trust_remote_code=False,
    )
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    return tok


def render_chat_ids(tokenizer, messages: list, add_generation_prompt: bool) -> List[int]:
    """Compatible across Transformers 4.x and 5.x (`List[int]` vs `BatchEncoding`)."""
    rendered = tokenizer.apply_chat_template(
        messages,
        tokenize=False,
        add_generation_prompt=add_generation_prompt,
    )
    return list(tokenizer.encode(rendered, add_special_tokens=False))


def load_causal_lm(
    model_path_or_id: str = DEFAULT_BASE_MODEL,
    device: Optional[str] = None,
    dtype: torch.dtype = torch.bfloat16,
    gradient_checkpointing: bool = False,
):
    dev = device or get_device()
    local_only = not os.path.isdir(model_path_or_id)
    model = AutoModelForCausalLM.from_pretrained(
        model_path_or_id,
        dtype=dtype,
        local_files_only=local_only,
        trust_remote_code=False,
    )
    if gradient_checkpointing:
        model.gradient_checkpointing_enable()
        model.enable_input_require_grads()
    model.config.use_cache = not gradient_checkpointing
    return model.to(dev)


def attach_lora(
    model: nn.Module,
    r: int = 16,
    lora_alpha: int = 32,
    lora_dropout: float = 0.05,
    device: Optional[str] = None,
    enable_grad_ckpt: bool = True,
) -> PeftModel:
    dev = device or get_device()
    cfg = LoraConfig(
        r=r,
        lora_alpha=lora_alpha,
        lora_dropout=lora_dropout,
        target_modules=LORA_TARGET_MODULES,
        bias="none",
        task_type="CAUSAL_LM",
    )
    peft_model = get_peft_model(model, cfg).to(dev)
    if enable_grad_ckpt:
        peft_model.gradient_checkpointing_enable(
            gradient_checkpointing_kwargs={"use_reentrant": False}
        )
    return peft_model


def merge_and_save_checkpoint(
    peft_model: PeftModel,
    tokenizer,
    save_dir: str,
    adapter_dir: Optional[str] = None,
) -> None:
    """Save optional adapter weights, then merge LoRA into base weights in bf16 and save."""
    os.makedirs(save_dir, exist_ok=True)
    if adapter_dir:
        os.makedirs(adapter_dir, exist_ok=True)
        peft_model.save_pretrained(adapter_dir)
        tokenizer.save_pretrained(adapter_dir)

    peft_model.eval()
    if torch.backends.mps.is_available():
        torch.mps.synchronize()
    merged = peft_model.merge_and_unload()
    merged.config.use_cache = True
    merged.save_pretrained(save_dir, safe_serialization=True)
    tokenizer.save_pretrained(save_dir)
    if torch.backends.mps.is_available():
        torch.mps.synchronize()


def unwrap_backbone_and_head(model: nn.Module) -> Tuple[nn.Module, nn.Module]:
    """
    Retrieve `(transformer_backbone, lm_head)` whether `model` is a raw
    `Qwen2ForCausalLM` or a `PeftModel` wrapping `Qwen2ForCausalLM`.
    """
    cur = model
    if hasattr(cur, "base_model") and hasattr(cur.base_model, "model"):
        cur = cur.base_model.model
    if hasattr(cur, "model") and hasattr(cur, "lm_head"):
        return cur.model, cur.lm_head
    raise ValueError(f"Unsupported CausalLM wrapper structure: {type(model)}")


def compute_chunked_lm_loss(
    model: nn.Module,
    input_ids: torch.Tensor,
    attention_mask: torch.Tensor,
    labels: torch.Tensor,
    token_chunk_size: int = 128,
) -> Tuple[torch.Tensor, int]:
    """
    Compute exact causal LM cross-entropy loss without materializing full
    `(B, L, 151936)` float32 logits at once on MPS.
    Only supervised positions (`labels != -100`) pass through `lm_head`.
    Returns `(mean_loss, valid_token_count)`.
    """
    backbone, lm_head = unwrap_backbone_and_head(model)
    eff_attn = None if input_ids.size(0) == 1 else attention_mask
    out = backbone(
        input_ids=input_ids,
        attention_mask=eff_attn,
        use_cache=False,
    )
    hidden = out.last_hidden_state  # (B, L, D)

    shift_hidden = hidden[:, :-1, :].reshape(-1, hidden.size(-1))
    shift_labels = labels[:, 1:].reshape(-1)

    valid_mask = shift_labels != -100
    n_valid = int(valid_mask.sum().item())
    if n_valid == 0:
        zero = shift_hidden.sum() * 0.0
        return zero, 0

    valid_hidden = shift_hidden[valid_mask]
    valid_targets = shift_labels[valid_mask]

    if not torch.is_grad_enabled() or not valid_hidden.requires_grad:
        total_nll_val = 0.0
        for s in range(0, n_valid, token_chunk_size):
            e = min(n_valid, s + token_chunk_size)
            logits_chunk = lm_head(valid_hidden[s:e]).float()
            ce = F.cross_entropy(logits_chunk, valid_targets[s:e], reduction="sum")
            total_nll_val += float(ce.item())
        return torch.tensor(total_nll_val / float(n_valid), device=input_ids.device), n_valid

    # True O(chunk_size) memory backward through frozen lm_head: frees 151k-vocab float32
    # softmax buffers after every 128-token slice so MPS never swaps on 24GB unified RAM!
    grad_hidden = torch.empty((n_valid, valid_hidden.size(-1)), device=input_ids.device, dtype=torch.float32)
    total_loss_scalar = 0.0
    inv_n = 1.0 / float(n_valid)
    for s in range(0, n_valid, token_chunk_size):
        e = min(n_valid, s + token_chunk_size)
        h_slice = valid_hidden[s:e].detach().float().requires_grad_(True)
        logits_chunk = F.linear(h_slice.to(lm_head.weight.dtype), lm_head.weight, lm_head.bias).float()
        ce = F.cross_entropy(logits_chunk, valid_targets[s:e], reduction="sum") * inv_n
        total_loss_scalar += float(ce.item())
        ce.backward()
        grad_hidden[s:e] = h_slice.grad
        del logits_chunk, ce, h_slice

    loss_const = torch.tensor(total_loss_scalar, device=input_ids.device, dtype=torch.float32)
    vh_f32 = valid_hidden.float()
    surrogate = loss_const + (vh_f32 * grad_hidden).sum() - (vh_f32.detach() * grad_hidden).sum()
    return surrogate, n_valid


def compute_completion_token_logprobs(
    model: nn.Module,
    input_ids: torch.Tensor,
    attention_mask: torch.Tensor,
    prompt_len: int,
    token_chunk_size: int = 128,
) -> torch.Tensor:
    """
    Compute exact per-token log-probabilities `log p(y_t | x, y_<t)` of shape `(B, C)`
    where `C = input_ids.size(1) - prompt_len`, chunked along tokens to keep MPS
    memory low.
    """
    backbone, lm_head = unwrap_backbone_and_head(model)
    eff_attn = None if input_ids.size(0) == 1 else attention_mask
    out = backbone(
        input_ids=input_ids,
        attention_mask=eff_attn,
        use_cache=False,
    )
    hidden = out.last_hidden_state  # (B, L, D)
    comp_hidden = hidden[:, prompt_len - 1 : -1, :]  # (B, C, D)
    comp_targets = input_ids[:, prompt_len:]  # (B, C)

    bsz, clen, dim = comp_hidden.shape
    flat_h = comp_hidden.reshape(-1, dim)
    flat_t = comp_targets.reshape(-1)
    total = flat_h.size(0)

    chunks: List[torch.Tensor] = []
    for s in range(0, total, token_chunk_size):
        e = min(total, s + token_chunk_size)
        logits = lm_head(flat_h[s:e]).float()
        chosen = logits.gather(-1, flat_t[s:e].unsqueeze(-1)).squeeze(-1)
        lse = torch.logsumexp(logits, dim=-1)
        chunks.append(chosen - lse)

    return torch.cat(chunks, dim=0).view(bsz, clen)


def compute_grpo_single_seq_loss(
    model: nn.Module,
    input_ids: torch.Tensor,
    attention_mask: torch.Tensor,
    prompt_len: int,
    advantage: float,
    old_lp: torch.Tensor,
    ref_lp: torch.Tensor,
    norm_tokens: float,
    clip_eps: float = 0.2,
    kl_beta: float = 0.02,
    token_chunk_size: int = 128,
) -> Tuple[torch.Tensor, float, float]:
    """
    True O(chunk_size) memory GRPO per-sequence loss (`input_ids` shape `(1, P + C)`):
    runs 128-token slices through frozen `lm_head`, computes clipped PPO surrogate +
    unbiased Schulman KL penalty, immediately frees 151k-vocab float32 buffers, and
    returns `(surrogate_loss, pg_scalar, kl_scalar)`.
    """
    backbone, lm_head = unwrap_backbone_and_head(model)
    eff_attn = None if input_ids.size(0) == 1 else attention_mask
    out = backbone(input_ids=input_ids, attention_mask=eff_attn, use_cache=False)
    comp_hidden = out.last_hidden_state[0, prompt_len - 1 : -1, :]  # (C, D)
    comp_targets = input_ids[0, prompt_len:]  # (C,)
    old_1d = old_lp.reshape(-1)
    ref_1d = ref_lp.reshape(-1)

    clen, dim = comp_hidden.shape
    grad_hidden = torch.empty((clen, dim), device=input_ids.device, dtype=torch.float32)
    pg_sum = 0.0
    kl_sum = 0.0
    inv_norm = 1.0 / max(1.0, norm_tokens)

    for s in range(0, clen, token_chunk_size):
        e = min(clen, s + token_chunk_size)
        h_slice = comp_hidden[s:e].detach().float().requires_grad_(True)
        logits = F.linear(h_slice.to(lm_head.weight.dtype), lm_head.weight, lm_head.bias).float()
        chosen = logits.gather(-1, comp_targets[s:e].unsqueeze(-1)).squeeze(-1)
        cur_lp = chosen - torch.logsumexp(logits, dim=-1)

        log_ratio = torch.clamp(cur_lp - old_1d[s:e], -10.0, 10.0)
        ratio = torch.exp(log_ratio)
        surr1 = ratio * advantage
        surr2 = torch.clamp(ratio, 1.0 - clip_eps, 1.0 + clip_eps) * advantage
        pg_tok = -torch.minimum(surr1, surr2)

        ref_diff = torch.clamp(ref_1d[s:e] - cur_lp, -10.0, 10.0)
        kl_tok = torch.exp(ref_diff) - ref_diff - 1.0

        chunk_loss = (pg_tok + kl_beta * kl_tok).sum() * inv_norm
        pg_sum += float(pg_tok.sum().item()) * inv_norm
        kl_sum += float(kl_tok.sum().item()) * inv_norm
        chunk_loss.backward()
        grad_hidden[s:e] = h_slice.grad
        del logits, chosen, cur_lp, chunk_loss, h_slice

    loss_const = torch.tensor(pg_sum + kl_beta * kl_sum, device=input_ids.device, dtype=torch.float32)
    ch_f32 = comp_hidden.float()
    surrogate = loss_const + (ch_f32 * grad_hidden).sum() - (ch_f32.detach() * grad_hidden).sum()
    return surrogate, pg_sum, kl_sum


def clear_mps_cache() -> None:
    gc.collect()
    if torch.backends.mps.is_available():
        torch.mps.synchronize()
        torch.mps.empty_cache()

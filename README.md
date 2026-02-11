# Atomic Lean 4 Reasoning Dataset

## Overview
This repository contains high-resolution formal proofs in **Lean 4**, specifically designed for training AI models in mathematical reasoning. Unlike standard libraries (Mathlib), these proofs are **decomposed into atomic steps** using `calc` blocks, avoiding "black-box" tactics.

## Why this exists
Current LLMs struggle with logical leaps. By providing proofs where every single rewrite is explicit (e.g., using `mul_comm` instead of `simp`), we provide a clearer signal for **Process Supervision** and **Reinforcement Learning**.

## Dataset Structure
- `src/`: Formal Lean 4 source code.
- `data/`: Exported proofs in JSONL format for machine learning pipelines.
- `scripts/`: Validation and conversion tools.

## Sample Proof: Complex Conjugate Identity
**Informal:** $z \cdot \bar{z} = \text{Re}(z)^2 + \text{Im}(z)^2$
**Atomic Formalization:**
```lean
-- See src/AtomicFormalReasoning/ComplexIdentities.lean
calc
  (z * conj z).re = z.re * z.re - z.im * (-z.im) := rfl
  _ = z.re * z.re + z.im * z.im := sub_neg_eq_add ...
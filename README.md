# DkMath: FLT5 for Lean4

Date: Create: 2026/07/29  1:45 JST / Update: 2026/08/01 19:35 JST
Author: Deskuma (D. and Wise Wolf)

## Fermat's Last Theorem (n=5 only) for Lean4

$$
\LARGE
x,y,z\in\mathbb{N}_{>0}
\quad\Longrightarrow\quad
x^5+y^5\ne z^5
$$

**To Lean Code** : [Basic.lean](./Flt5DkMath/Basic.lean)
Pinned stable version: Lean4 + Mathlib4 = v4.32.2
Also build-checked with: Lean4 + Mathlib4 = v4.33.0-rc1

```lean
theorem PNat.pow_add_pow_ne_pow_five
    (x y z : ℕ+) :
    x^5 + y^5 ≠ z^5 :=
  by
    intro h
    have h_eq : (x : ℕ)^5 + (y : ℕ)^5 = (z : ℕ)^5 := by
      exact Subtype.ext_iff.mp h
    exact DkMath.FLT.Five.fermatFive_no_positive_solution
      x.1 y.1 z.1 x.property y.property z.property h_eq
```

## 📖Explanatory document

### Fermat's Last Theorem for Exponent Five

📜PDF

- [FLT5: A Proof Method Using 5-Adic Valuations, the Golden Integer Ring, and Infinite Descent](./docs/pdf/FLT5-main-en-v0-r1.pdf)
  - [日本語版](./docs/pdf/FLT5-main-ja-v0-r1.pdf)

### DocGen

- [General documentation](https://deskuma.github.io/flt5_dk_math_lean4/docs/)

## ⚗️This Project

This is a [standalone](./Flt5DkMath/FLT5StandAlone.lean) version of the following deliverables.

### Hackathon Project

OpenAI Build Week 2026

> ## OpenAI Build Week: Cosmic Formula Inversion and FLT5

DkMath was submitted to OpenAI Build Week as a verifiable AI-assisted mathematical research project built with Codex and GPT-5.6.

The original demonstration video presents the first phase: the Cosmic Formula inversion prototype and a local fifth-degree GN obstruction. After the video and hackathon submission were completed, development continued into a second phase, extending the GN5 route into a Lean formalization of the positive-natural exponent-five case of Fermat's Last Theorem.

Public Lean endpoints:

- `DkMath.FLT.Five.flt5Target`
- `DkMath.FLT.Five.fermatFive_no_positive_solution`

The current theorem states:

$$
x,y,z\in\mathbb{N}_{>0}
\quad\Longrightarrow\quad
x^5+y^5\ne z^5
$$

This result is kernel-checked by Lean. Independent external mathematical review is still to come.

- Hackathon entry point: [DkMath Hackathon](https://github.com/Deskuma/dkmath/blob/64305c707fa3a394a83301c45d2c878be5d905bb/lean/dk_math/DkMath/Hackathon/README.md)
- Full project record: [Cosmic Formula Inversion — OpenAI Build Week](https://github.com/Deskuma/dkmath/blob/64305c707fa3a394a83301c45d2c878be5d905bb/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/README.md)
- FLT5 public Lean API: [DkMath.FLT.Five](https://github.com/Deskuma/dkmath/blob/64305c707fa3a394a83301c45d2c878be5d905bb/lean/dk_math/DkMath/FLT/Five.lean)
- Axiom audit entry point: [CheckAxioms.lean](https://github.com/Deskuma/dkmath/blob/64305c707fa3a394a83301c45d2c878be5d905bb/lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean)
- Devpost submission: [DkMath — Verifiable AI Mathematical Research](https://devpost.com/software/dkmath-verifiable-ai-mathematical-research)

---

Provided by Dk.Math Black Hole Research Institute.

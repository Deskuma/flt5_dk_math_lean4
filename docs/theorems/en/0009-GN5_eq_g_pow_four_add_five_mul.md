# 0009 — `GN5_eq_g_pow_four_add_five_mul`

> This document is the English translation of the Japanese canonical edition.

## Lean type

```lean
theorem GN5_eq_g_pow_four_add_five_mul (g y : ℕ) :
    GN5 g y =
      g ^ 4 + 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 +
        2 * g * y ^ 3 + y ^ 4) := by
  unfold GN5
  ring
```

Its fully qualified name is `DkMath.FLT.Five.GN5_eq_g_pow_four_add_five_mul`.

## Mathematical statement

The theorem separates `GN5` into a multiple of $5$ and the leading term $g^4$.

$$
GN5(g,y)=g^4+5\bigl(g^3y+2g^2y^2+2gy^3+y^4\bigr)
$$

Therefore,

$$
GN5(g,y)\equiv g^4\pmod 5.
$$

## Role in the complete proof

The preceding `GN5_eq_gap_mul_add_five_mul_y_pow_four` is a decomposition modulo the gap $g$. This theorem is the corresponding decomposition modulo the prime $5$, and it is an entry point for reading the five-adic behavior of `GN5 g y`.

In particular, $5\mid GN5(g,y)$ implies $5\mid g^4$, and a separate power-divisibility lemma can then be used to reach $5\mid g$. That latter step is not a conclusion of this theorem alone.

## Direct dependencies

Its only project-specific direct dependency is `DkMath.FLT.Five.GN5`. The proof uses Mathlib's `ring` tactic. It is logically independent of the preceding gap decomposition and is placed beside it as a different presentation of the same polynomial.

## Proof flow

1. `unfold GN5` expands the definition.
2. `ring` converts both sides to canonical polynomial form in a commutative semiring.

The coefficients $10$ in the expanded definition appear on the right as $5\cdot2$.

## Lean-specific processing

`ring` does not evaluate concrete values of $g$ and $y$; it normalizes a polynomial identity. No natural-number subtraction is used, so no truncated-subtraction side condition is needed. The theorem does not itself prove divisibility. It exposes an equality from which later congruence and divisibility statements can be derived.

## Redundancy and duplication

The proof script is again `unfold GN5; ring`, but the exported interfaces have different purposes.

- `GN5_eq_homogeneous_cyclotomic` identifies the standard cyclotomic factor.
- The gap decomposition supports congruence analysis modulo $g$.
- This theorem supports five-adic analysis modulo $5$.

They are therefore parallel API views rather than mere duplication.

## Optimization candidates

The proof body is already close to minimal. If later code repeats the same conversions, thin lemmas such as `GN5 g y % 5 = g ^ 4 % 5`, or a verified theorem relating `5 ∣ GN5 g y` and `5 ∣ g`, could improve the public API. These are unverified proposals.

## Required Mathlib imports and import optimization

The standalone uses `import Mathlib`. The principal requirements here are natural-number semiring operations, powers, and the `ring` tactic. The exact minimal import is not determined by the available evidence. A reduction toward `Mathlib.Tactic.Ring` plus basic natural-number algebra may be possible, but it requires a clean build. No Lean build was run in this task.

## Comparator challenge suitability

This theorem is suitable for a Comparator challenge. One can compare the shortest `unfold GN5; ring` proof, a `ring_nf` proof, and manual coefficient normalization. A more useful two-stage challenge asks the solver to derive the congruence or a divisibility consequence from the equality.

## Next declaration

The next declaration is `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5`.

$$
(g+y)^5=y^5+g\,GN5(g,y)
$$

It connects `GN5` to the actual factorization of the fifth-power difference.

## Evidence and inference

The theorem, proof, declaration order, and the reading $GN5(g,y)\equiv g^4\pmod5$ come from the Lean source. The proposed helper API, minimal-import discussion, and Comparator design are analysis and have not received additional Lean verification.

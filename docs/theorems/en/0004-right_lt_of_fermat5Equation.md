# 0004 — `right_lt_of_fermat5Equation`

> This document is an English translation of the Japanese canonical edition.

## Lean type

```lean
theorem right_lt_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    y < z := by
  unfold Fermat5Equation at hEq
  have hx5 : 0 < x ^ 5 := pow_pos hx 5
  have hy5z5 : y ^ 5 < z ^ 5 := by
    omega
  exact (Nat.pow_lt_pow_iff_left (by decide : 5 ≠ 0)).mp hy5z5
```

Its fully qualified name is `DkMath.FLT.Five.right_lt_of_fermat5Equation`.

## Mathematical statement

If natural numbers $x,y,z$ satisfy the exponent-five Fermat equation

$$
x^5+y^5=z^5
$$

and $0<x$, then $y<z$.

Since the positive quantity $x^5$ is added to $y^5$ to obtain $z^5$, one first gets $y^5<z^5$. For a positive exponent over natural numbers, comparison of powers reflects comparison of the bases, yielding $y<z$.

## Role in the complete proof

This theorem is the first bridge from the Fermat equation to **order information**.

The preceding theorem `fifth_sub_eq_of_add_eq` provides

$$
z^5-y^5=x^5.
$$

However, subtraction on natural numbers is truncated. Before later code can treat `z-y` as a genuinely positive gap, it must establish $y<z$.

The immediate consumer is `gap_pos_of_fermat5Equation`, which applies `Nat.sub_pos_of_lt` to derive

$$
0<z-y.
$$

That positive gap becomes the coordinate used in the later factorization through `GN5 (z-y) y`.

## Direct dependencies

### Project dependency

- `DkMath.FLT.Five.Fermat5Equation`

### Main Lean and Mathlib dependencies

- `pow_pos`
- `Nat.pow_lt_pow_iff_left`
- `omega`
- `by decide : 5 ≠ 0`

Although `fifth_sub_eq_of_add_eq` is mathematically adjacent, it is not called directly in this proof. The theorem unfolds the original additive equation and derives the order relation from it.

## Proof flow

1. `unfold Fermat5Equation at hEq` exposes the raw equality $x^5+y^5=z^5$.
2. `pow_pos hx 5` proves $0<x^5$, stored as `hx5`.
3. `omega` combines `hEq` and `hx5` to prove $y^5<z^5$.
4. The forward direction `.mp` of `Nat.pow_lt_pow_iff_left` converts the power comparison back to $y<z$.
5. The nonzero exponent condition is discharged by `(by decide : 5 ≠ 0)`.

The proof therefore has two mathematical stages: obtain a strict inequality between fifth powers, then reflect that inequality back to the bases.

## Lean-specific processing

### What `omega` handles

`omega` does not expand fifth powers. It treats `x ^ 5`, `y ^ 5`, and `z ^ 5` as natural-number terms and uses the facts

- `0 < x ^ 5`,
- `x ^ 5 + y ^ 5 = z ^ 5`

to derive `y ^ 5 < z ^ 5` by linear arithmetic.

### `Nat.pow_lt_pow_iff_left`

This theorem is used to reflect the strict inequality of powers back to the bases. The exponent must be proved nonzero, and the finite decidable proposition `5 ≠ 0` is closed by `by decide`.

### Implicit parameters

The variables are implicit, written `{x y z : ℕ}`. Lean normally infers them from `hx` and `hEq`.

## Redundancy and duplication

`hx5` is used only once, but it gives a useful name to the central intermediate fact. Inlining it is possible, though likely less readable.

A different proof may be built through `fifth_sub_eq_of_add_eq`, but recovering strict order from truncated natural-number subtraction requires additional care. The current direct route from the additive equation avoids that complication and is robust.

## Optimization candidates

The following are possible but unverified:

1. Inline `hx5` into the `omega` step.
2. Use another strict-monotonicity theorem for powers to make the direction of reasoning more explicit.
3. Extract a reusable helper deriving the strict inequality of fifth powers from `Fermat5Equation`, potentially supporting a symmetric version.

The current proof is already short and clear, so the practical gain from refactoring is limited.

## Mathlib imports and import minimization

The standalone file uses `import Mathlib`, and the repository records success in that environment.

The theorem requires functionality for:

- natural-number powers and order,
- `pow_pos`,
- `Nat.pow_lt_pow_iff_left`,
- the `omega` tactic,
- `decide`.

The exact minimal import set has not been established. A `#min_imports` audit followed by a clean build would be required, including both theorem and tactic imports. This article deliberately does not assert specific minimal module names without verification.

## Comparator challenge suitability

This theorem is suitable for a small Comparator challenge. It supports several strategies:

- the current `pow_pos` + `omega` + `Nat.pow_lt_pow_iff_left` route;
- a structural proof emphasizing strict monotonicity of powers;
- a difference-based proof through `fifth_sub_eq_of_add_eq`.

Comparing the last route is especially instructive because natural-number subtraction may force additional order reasoning.

## Next theorem

The next theorem is `DkMath.FLT.Five.gap_pos_of_fermat5Equation`.

It feeds the conclusion $y<z$ into `Nat.sub_pos_of_lt`, establishing positivity of the gap `z-y`, the local coordinate used by the subsequent factorization.

## Evidence and inference

The theorem type, proof term, direct dependencies, and placement immediately before `gap_pos_of_fermat5Equation` are verified from the Lean source.

Import minimization, alternative proofs, extraction of a symmetric helper, and Comparator suitability are analysis and proposals in this article. No Lean build was run in this publication step.

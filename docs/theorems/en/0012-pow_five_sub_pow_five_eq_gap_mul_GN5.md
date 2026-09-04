# 0012 — `pow_five_sub_pow_five_eq_gap_mul_GN5`

> This document is the English translation of the Japanese canonical edition.

## Lean type

```lean
theorem pow_five_sub_pow_five_eq_gap_mul_GN5
    {y z : ℕ}
    (hyz : y ≤ z) :
    z ^ 5 - y ^ 5 = (z - y) * GN5 (z - y) y := by
  simpa [Nat.sub_add_cancel hyz] using
    (add_pow_five_sub_eq_mul_GN5 (z - y) y)
```

The fully qualified name is `DkMath.FLT.Five.pow_five_sub_pow_five_eq_gap_mul_GN5`.

## Mathematical statement

When $y\le z$, the difference of fifth powers is the product of the actual gap $z-y$ and `GN5`.

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

This is obtained from the abstract identity $(g+y)^5-y^5=g\,GN5(g,y)$ by substituting $g=z-y$.

## Role in the complete proof

The preceding theorem uses an abstract gap. This theorem connects it to the natural-number difference $z-y$ arising from the FLT5 equation. Combined with `fifth_sub_eq_of_add_eq`, it supplies the factorization interface needed later:

$$
x^5=(z-y)\,GN5(z-y,y)
$$

## Direct dependencies

- `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5`
- `Nat.sub_add_cancel`
- `simpa`

It depends indirectly on `GN5`.

## Proof flow

1. Specialize the upstream theorem with $g=z-y$.
2. Its left side becomes `((z - y) + y) ^ 5 - y ^ 5`.
3. Rewrite `(z-y)+y=z` using `Nat.sub_add_cancel hyz`.
4. Let `simpa` normalize the specialized theorem to the target.

No polynomial expansion, `ring`, or `omega` is rerun here.

## Lean-specific processing

Subtraction on `ℕ` is truncated, so `(z-y)+y=z` requires `hyz : y ≤ z`. `Nat.sub_add_cancel hyz` guarantees that no truncation occurs.

## Redundancy and overlap

Mathematically this is a specialization of the preceding theorem. As an API, however, it directly exposes the concrete gap $z-y$ and prevents repeated subtraction bookkeeping in downstream proofs.

## Optimization candidates

The current proof is already very small. One alternative separates `rw [← Nat.sub_add_cancel hyz]` from `exact`, but the present `simpa using` form is more compact. Re-expanding `GN5` would move backward in the dependency structure.

## Required Mathlib imports and import optimization

The standalone file uses `import Mathlib`. This theorem itself needs natural-number subtraction, powers, multiplication, and `simpa`; it does not directly need `ring` or `omega`. The exact minimal import set is unverified without a Lean build.

## Comparator challenge suitability

It is suitable.

1. The current `simpa [Nat.sub_add_cancel hyz] using ...` proof.
2. A proof separating `rw` and `exact`.
3. A direct proof after unfolding `GN5`.

Useful comparison axes are proof length, reuse of the upstream API, visibility of the subtraction condition, and maintainability.

## Next theorem to read

The next declaration is `DkMath.FLT.Five.GN5_one_one`.

$$
GN5(1,1)=31
$$

It is the first concrete evaluation moving from the general identity to the finite-prime escape demonstration.

## Facts versus interpretation

The type, proof, declaration order, and direct dependencies were verified in the `DkMath/FLT/Five/GN5.lean` section of `Flt5DkMath/FLT5StandAlone.lean`. The role analysis, minimal-import discussion, and Comparator assessment include unverified proposals. The Lean source is the formal authority. No Lean build was run.
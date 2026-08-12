# 0011 — `add_pow_five_sub_eq_mul_GN5`

> This document is the English translation corresponding to the canonical Japanese article.

## Lean type

```lean
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y := by
  rw [add_pow_five_eq_add_mul_GN5]
  omega
```

The fully qualified name is `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5`.

## Mathematical statement

The difference of fifth powers is the product of the gap $g$ and the homogeneous residual kernel `GN5 g y`.

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

This is the standard factorization of a fifth-power difference written in the gap coordinate $z=g+y$.

## Role in the complete proof

The preceding theorem `add_pow_five_eq_add_mul_GN5` established the subtraction-free additive form

$$
(g+y)^5=y^5+g\,GN5(g,y)
$$

This theorem converts it into the difference form used directly by later divisibility and factor-separation arguments.

The next theorem, `pow_five_sub_pow_five_eq_gap_mul_GN5`, substitutes $g=z-y$ and rewrites a general difference $z^5-y^5$ as the product of the natural-number gap and `GN5`.

## Direct dependencies

The only project-specific direct dependency is:

- `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5`

It depends indirectly on the definition of `GN5`. The proof uses Mathlib rewriting and the `omega` tactic.

## Proof flow

1. `rw [add_pow_five_eq_add_mul_GN5]` rewrites the left side as
   `(y ^ 5 + g * GN5 g y) - y ^ 5`.
2. `omega` handles the resulting natural-number addition and subtraction.
3. Removing the explicitly added term `y ^ 5` leaves `g * GN5 g y`.

No polynomial expansion is repeated here; it was completed in the preceding theorem.

## Lean-specific processing

Subtraction on `ℕ` is truncated, so it should not be treated as unrestricted ring subtraction. After rewriting, however, the left side has the explicit form

$$
(y^5+g\,GN5(g,y))-y^5
$$

so the subtracted term is visibly present as a summand. `omega` solves this natural-number arithmetic problem; it does not inspect fifth powers or the polynomial structure of `GN5`.

## Redundancy and overlap

Mathematically this theorem is very close to the preceding additive form, but the APIs serve different purposes.

- The additive form is a subtraction-free semiring identity.
- This theorem is the operational form for differences, divisibility, and gap factorization.

It is therefore a thin but useful wrapper that improves readability and stabilizes downstream rewriting.

## Optimization candidates

A possible alternative avoids `omega` and closes the rewritten goal with a standard natural-number add/subtract cancellation lemma, such as an appropriate orientation of the `Nat.add_sub_cancel_left` family. The exact lemma and orientation have not been build-verified.

The current two-line proof is already short and introduces no extra hypotheses, so it is practically near-minimal.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`. This theorem mainly needs natural-number addition and subtraction, rewriting, and the `omega` tactic.

A narrower combination involving basic natural-number arithmetic and `Mathlib.Tactic.Omega` is a candidate, but the exact minimal import set cannot be confirmed without a Lean build. No imports were changed.

## Comparator challenge suitability

This theorem is suitable for a small Comparator challenge. Candidate proofs are:

1. The current `rw` plus `omega` proof.
2. Rewriting followed by an explicit natural-number cancellation lemma.
3. A direct `unfold GN5; ring` proof that repeats the polynomial normalization.

Useful comparison axes are tactic dependencies, proof time, clarity about truncated subtraction, and reuse of the upstream theorem. Approaches 1 or 2 are normally more structural than 3.

## Next theorem to read

Next: `DkMath.FLT.Five.pow_five_sub_pow_five_eq_gap_mul_GN5`.

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

Under the hypothesis $y\le z$, it uses `Nat.sub_add_cancel` to move from the abstract gap $g$ to the concrete natural-number difference $z-y$.

## Sources and status of inferences

The theorem type, proof, direct dependency, declaration order, and next theorem were verified in the generated `DkMath/FLT/Five/GN5.lean` section of `Flt5DkMath/FLT5StandAlone.lean`. The minimal-import proposal, the alternative cancellation proof, and the Comparator assessment are unverified suggestions. Existing PDFs provide narrative context for the whole proof, while the Lean source is the formal authority for this article. No Lean build was run.
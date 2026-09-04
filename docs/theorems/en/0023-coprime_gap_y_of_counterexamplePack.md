# 0023 — `coprime_gap_y_of_counterexamplePack`

## Lean type

```lean
theorem coprime_gap_y_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y
```

From `CounterexamplePack x y z`, this theorem derives that the natural-number gap `z - y` is coprime to the second base `y`.

## Mathematical statement

Suppose positive natural numbers satisfy

$$
x^5+y^5=z^5
$$

and the input is primitive. From the previous article's result

$$
\gcd(y,z)=1,
$$

we obtain

$$
\gcd(z-y,y)=1.
$$

A common divisor is preserved when taking a difference, so if `y` and `z` are coprime, then `y` and `z-y` are coprime as well.

## Role in the complete proof

This theorem transfers coprimality from the original coordinates `(y,z)` to the local fifth-power-difference coordinates `(g,y)`, where `g=z-y`.

The following Reduction layer uses

$$
GN5(g,y)\equiv 5y^4\pmod g
$$

to analyze common prime divisors of `g` and `GN5(g,y)`. The fact `Nat.Coprime g y` excludes the possibility that such a common prime comes from `y`, reducing the exceptional case to the prime `5`. Thus this theorem is the coprimality bridge from the global Fermat equation to the local gap factorization.

## Direct dependencies

- `CounterexamplePack`
- `right_lt_of_fermat5Equation`
- `coprime_y_z_of_counterexamplePack`
- `Nat.coprime_sub_self_right`
- `Nat.coprime_comm`

The direct mathematical input is the previous theorem's `Nat.Coprime y z`. The fields `hPack.hx` and `hPack.hEq` are used to derive `y ≤ z`, which is required to treat natural-number subtraction as the intended difference.

## Proof flow

The Lean proof has three stages.

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
have hyGap : Nat.Coprime y (z - y) :=
  (Nat.coprime_sub_self_right hyz).2
    (coprime_y_z_of_counterexamplePack hPack)
simpa [Nat.coprime_comm] using hyGap
```

1. Derive `y < z` from positivity of `x` and the Fermat equation, then weaken it to `y ≤ z`.
2. Apply `Nat.coprime_sub_self_right hyz` to the previous result `Nat.Coprime y z`, obtaining `Nat.Coprime y (z-y)`.
3. The goal uses the opposite argument order, so normalize by symmetry with `Nat.coprime_comm`.

## Lean-specific processing

Subtraction on natural numbers is truncated subtraction, so `Nat.coprime_sub_self_right` requires the explicit order hypothesis `y ≤ z`. Lean receives this condition from `right_lt_of_fermat5Equation`, even though the corresponding mathematical step is usually left implicit.

`(Nat.coprime_sub_self_right hyz).2` selects the reverse direction of the equivalence, converting `Nat.Coprime y z` into `Nat.Coprime y (z-y)`. The final `simpa [Nat.coprime_comm]` changes only the order of the coprimality arguments.

## Redundancy and duplication

The theorem calls `right_lt_of_fermat5Equation` again to obtain `y ≤ z`. If many later lemmas require gap positivity or this order relation, a small API derived from `CounterexamplePack` could package `y<z`, `y≤z`, and `0<z-y`. The present one-line derivation is nevertheless lightweight.

The intermediate fact `hyGap` differs from the goal only by argument order. Returning `Nat.Coprime y (z-y)` would remove the last symmetry step, but the current result is better aligned with later factorization APIs that place the gap first.

## Optimization candidates

- An audit may find an existing Mathlib theorem returning `Nat.Coprime (z-y) y` directly, which could eliminate the final `simpa`. This is unverified.
- Defining a namespace method such as `CounterexamplePack.coprime_gap_y` would let later code read `hPack.coprime_gap_y`.
- A new general lemma for transferring coprimality across subtraction is unnecessary unless it provides a clearer API, because Mathlib already supplies the essential result.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The directly used Mathlib functionality concerns natural-number order, truncated subtraction, `Nat.Coprime`, `Nat.coprime_sub_self_right`, and `Nat.coprime_comm`. The theorem also depends on DkMath's `Basic` declarations and the immediately preceding Reduction theorem.

The exact minimal imports of the split source module were not build-checked for this article. Narrowing the imports to individual natural-number gcd and coprimality modules may be possible, but this remains an unverified import-optimization proposal.

## Comparator challenge suitability

This theorem is suitable for a small Comparator challenge.

- The current three-stage proof using `Nat.coprime_sub_self_right`
- A proof expanded through gcd equalities and arithmetic on the difference
- An API design that chooses the argument order best suited for subsequent use

Useful evaluation criteria are safety around natural-number subtraction, appropriate use of high-level Mathlib APIs, proof length, and convenience for downstream code. Rebuilding the prime-divisor contradiction would likely be more redundant than the current proof.

## Sources and explicit uncertainty

The theorem type, proof body, declaration order, and role in the Reduction layer are grounded in the `DkMath/FLT/Five/Reduction.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean`. Import minimization, a namespace method, and auxiliary API additions are unverified proposals. Existing PDFs provide broader FLT5 context, but the Lean source is the formal authority for this article.

## Next theorem to read

`DkMath.FLT.Five.dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`

This theorem uses the decomposition

$$
GN5(g,y)=gA+5y^4
$$

to show that any divisor of both the gap and `GN5(g,y)` must divide

$$
5y^4.
$$

Combined with the coprimality established here, it begins the reduction of common prime divisors to the exceptional prime `5`.
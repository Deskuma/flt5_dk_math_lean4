# 0108 — `sumGN5_eq_goldenNorm_signed`

## Lean type

```lean
/-- The sum residual is the golden norm with a negative cross-beam coordinate. -/
theorem sumGN5_eq_goldenNorm_signed (u v : ℕ) :
    GoldenNorm
        ((u : ℤ) ^ 2 + (v : ℤ) ^ 2)
        (-((u : ℤ) * (v : ℤ))) =
      (SumGN5 u v : ℤ) := by
  unfold GoldenNorm SumGN5
  by_cases h : v ≤ u
  · rw [if_pos h]
    push_cast
    rw [Nat.cast_sub h]
    ring
  · rw [if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    push_cast
    rw [Nat.cast_sub huv]
    ring
```

## Mathematical statement

For natural numbers $u,v$, define the square-sum coordinate

$$
M=u^2+v^2
$$

and the sign-reversed cross coordinate

$$
N=-uv.
$$

Then the golden norm

$$
\operatorname{GoldenNorm}(M,N)=M^2+MN-N^2
$$

coincides with `SumGN5 u v`.

Equivalently,

$$
\operatorname{GoldenNorm}(u^2+v^2,-uv)=\operatorname{SumGN5}(u,v).
$$

`SumGN5` has two branches, $v\le u$ and $u\le v$, so that subtraction remains nonnegative over the natural numbers. After moving to the integer-valued golden norm, the two branches are unified into one signed quadratic form.

## Role in the full proof

This theorem appears at the entrance of `SignedSquareGoldenExceptional.lean` and is the bridge that sends the sum-oriented signed five-adic source into square/golden coordinates.

The preceding `SquareGoldenNormalForm` stage used the difference-oriented coordinates

$$
M=z^2+y^2,\qquad N=zy.
$$

At the signed exceptional stage, the sum-oriented source must also be represented by the same packet interface. For that orientation, the cross coordinate is chosen as

$$
N=-uv,
$$

so that `SumGN5` lands in the same `GoldenNorm` API.

In the `sum` branch of the later `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`, this theorem is used directly:

```lean
have hGoldenBase : GoldenNorm M N = (SumGN5 u v : ℤ) := by
  simpa [M, N] using sumGN5_eq_goldenNorm_signed u v
```

The five-adic residual equation is then transported to the golden norm equation $5b^5$. Thus this theorem is the sum-side entry point that allows the difference and sum orientations to merge into a common `SignedSquareGoldenExceptionalPacket`.

## Direct dependencies

The two principal direct dependencies are:

- `GoldenNorm` — the integral binary golden quadratic form.
- `SumGN5` — the fifth-power residual associated with $(u+v)$, defined piecewise in order to manage natural-number subtraction.

At the proof-engineering level, the theorem also uses `Nat.cast_sub`, `Nat.le_of_not_ge`, `push_cast`, and `ring`.

## Proof flow

The proof first unfolds `GoldenNorm` and `SumGN5`, exposing explicit polynomial expressions on both sides.

It then performs

```lean
by_cases h : v ≤ u
```

which mirrors the branch structure in the definition of `SumGN5`.

### Branch $v\le u$

`if_pos h` selects the first `SumGN5` branch. `push_cast` pushes natural-number casts through the polynomial expression, and

```lean
rw [Nat.cast_sub h]
```

rewrites

$$
\uparrow{(u-v)}=(u:\mathbb Z)-(v:\mathbb Z).
$$

The remaining identity is a polynomial identity over the integers and is closed by `ring`.

### Branch $v\nleq u$

`if_neg h` selects the second branch. Totality of the natural-number order gives

```lean
have huv : u ≤ v := Nat.le_of_not_ge h
```

and the same `push_cast`, `Nat.cast_sub huv`, and `ring` sequence finishes the proof.

## Lean-specific processing

Mathematically this is a single symmetric identity, but Lean cannot solve it by `ring` immediately because `SumGN5` contains truncated subtraction in `ℕ`.

The key point is that `Nat.cast_sub` requires an ordering hypothesis. Natural-number subtraction does not behave like integer subtraction when the result would be negative, so the rewrite

$$
\uparrow{(u-v)}=\uparrow u-\uparrow v
$$

requires a proof of $v\le u$. In the second branch, `huv : u ≤ v` plays the symmetric role.

`push_cast` normalizes casts through coefficients, products, and powers so that `ring` can see a pure integer polynomial identity.

## Redundancy and duplication

The two branches differ only in the selected `if` branch and the ordering hypothesis supplied to `Nat.cast_sub`. Their final sequence

```lean
push_cast
rw [Nat.cast_sub ...]
ring
```

is essentially duplicated.

This is implementation-level duplication caused by the piecewise natural-number definition of `SumGN5`, not a mathematical duplication.

There is also a structural counterpart on the difference side, namely `GN5_eq_goldenNorm_squareLink`. The present theorem may be viewed as its signed-sum analogue. A higher-level signed-coordinate API could potentially unify the two bridge patterns.

## Optimization candidates

1. Introduce a helper lemma that normalizes the two branches of `SumGN5` into integer polynomial form, centralizing the order and cast handling.
2. Abstract this theorem together with `GN5_eq_goldenNorm_squareLink` into one bridge over a signed cross coordinate.
3. Compare a shorter `simpa` / `norm_cast` formulation. Care is needed because hiding the `Nat.sub` side conditions may reduce auditability; the explicit `by_cases` proof is pedagogically valuable.
4. Let the signed source itself construct $M,N$ and expose the residual-to-norm bridge as a source-specific field theorem.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

for the whole generated file.

This theorem itself needs integer/natural casts, `Nat.cast_sub`, `push_cast`, `ring`, and the existing definitions `GoldenNorm` and `SumGN5`. On the tactic side, cast normalization and ring normalization are therefore required.

Likely import-reduction candidates include `Mathlib.Tactic.PushCast`, `Mathlib.Tactic.Ring`, and the algebra/cast modules providing `Nat.cast_sub`. The actual minimal module-level import set cannot be certified without a Lean build, so these remain candidates rather than asserted minima.

## Comparator challenge suitability

This theorem is well suited for a Comparator challenge.

Three clear implementations can be compared:

- Current approach: `by_cases` + `push_cast` + `Nat.cast_sub` + `ring`.
- Helper-lemma approach: normalize both `SumGN5` branches to integer polynomial form first, then use one algebraic closure step.
- API-abstraction approach: define signed square coordinates and handle difference and sum sources through one theorem.

The comparison should consider not only proof length, but also visibility of the safety conditions for `Nat.sub`, structural correspondence with the difference-oriented bridge, and downstream reusability in packet construction.

## Correspondence with existing materials

The formal source of record is the `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The exact page/section correspondence in the existing Japanese and English PDFs could not be established through the GitHub connector in this run, so no page or section number is guessed. If narrative PDF text and Lean source differ, this museum treats the Lean source as authoritative.

## Next theorem to read

The next theorem in dependency order is

```lean
theorem signed_endpoint_square_discriminant (x y : ℤ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * (-(x * y)) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 := by
  ring
```

The present theorem connects the sum residual to a golden norm with a negative cross coordinate. The next theorem shows that the same signed endpoint coordinates also preserve the square discriminant. Once these two bridges are in place, the development can proceed naturally to `SignedSquareGoldenSource` and `SignedSquareGoldenExceptionalPacket`.

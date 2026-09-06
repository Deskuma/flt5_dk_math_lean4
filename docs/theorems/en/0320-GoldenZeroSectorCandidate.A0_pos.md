# 0320 — `GoldenZeroSectorCandidate.A0_pos`

## Declaration kind

This declaration is a **`theorem`**.

It is the positivity bridge asserting that the natural representative $A_0$ of the lower inversion factor, introduced in 0316 `GoldenZeroSectorCandidate.A0`, is not merely a natural number but is in fact strictly positive.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The natural representatives are both positive. -/
theorem A0_pos (p : GoldenZeroSectorCandidate) : 0 < p.A0 := by
  by_contra hpos
  have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.A0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hApos := p.A_pos
  omega
```

Its type is

```lean
0 < p.A0
```

where the strict order is the order on `ℕ`. Here `p.A0 : ℕ` is defined as the `natAbs` of the signed lower inversion factor `zeroSectorA p.r p.s p.d : ℤ`.

## Mathematical statement

In 0316,

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

was introduced, while 0314 `A_pos` already established

$$
0<A.
$$

Moreover, 0318 `A0_cast` gives

$$
(A_0:\mathbb Z)=A.
$$

Therefore, if $A_0=0$, its cast to the integers is also zero, forcing $A=0$, which contradicts $A>0$. Hence

$$
A_0>0.
$$

The theorem records this elementary but important fact in a form that can be consumed directly by the subsequent natural-number arithmetic.

## Role in the overall proof

In the signed-integer phase of the zero-sector inversion, the development has already established

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
$$

$$
0<A<B.
$$

Declarations 0316–0319 then construct the bridge

$$
A_0=|A|,\qquad B_0=|B|,
$$

$$
(A_0:\mathbb Z)=A,\qquad(B_0:\mathbb Z)=B.
$$

The present theorem is the first declaration that makes explicit that the natural representative itself is a **nonzero positive factor**, rather than merely a value obtained by a type conversion.

Together with the immediately following `B0_pos`, it yields

$$
0<A_0,\qquad0<B_0.
$$

This supplies the positivity hypotheses required for the later natural-number factorization layer, including `A0_mul_B0`, `B0_eq_A0_add`, coprimality, divisibility, and power-splitting arguments.

## Direct dependencies

### `GoldenZeroSectorCandidate.A0`

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

This is the direct definition of the object appearing in the goal. The current proof deliberately does not unfold `A0`; it instead uses the public cast theorem below.

### `GoldenZeroSectorCandidate.A0_cast`

0318 established

```lean
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

The current proof obtains it with

```lean
have hcast := p.A0_cast
```

and uses it as the equality bridge between the natural number $A_0$ and the signed integer factor $A$.

### `GoldenZeroSectorCandidate.A_pos`

0314 supplies

$$
0<A.
$$

At the end of the proof it is introduced as

```lean
have hApos := p.A_pos
```

and `omega` combines it with the consequence $A=0$.

### `Nat.eq_zero_of_not_pos`

For a natural number $n$, this Mathlib lemma turns `¬ 0 < n` into `n = 0`. In the present theorem it converts the contradiction hypothesis `hpos` into

```lean
have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
```

which is the key natural-number discreteness step.

## Proof flow

1. `by_contra hpos` assumes `¬ 0 < p.A0`.
2. Since a natural number that is not positive must be zero, `Nat.eq_zero_of_not_pos hpos` yields `p.A0 = 0`.
3. `p.A0_cast` is copied into `hcast`, retaining $(A_0:\mathbb Z)=A$.
4. `rw [hzero] at hcast` rewrites the left side of that cast equality using $A_0=0$.
5. `norm_num at hcast` normalizes the cast of natural zero and related numerical syntax, leaving essentially the information $0=A$.
6. `p.A_pos` supplies $0<A$.
7. `omega` closes the contradiction between $A=0$ and $A>0$.

Mathematically, the proof says only that a natural number identified with a positive integer is positive. In Lean, the explicit sequence is needed because the argument crosses the `ℕ` / `ℤ` type boundary.

## Lean-specific processing

### `by_contra` and zero reduction in `ℕ`

Rather than constructing `0 < p.A0` directly, the proof assumes its negation. Since `ℕ` has no negative values, `¬ 0 < p.A0` can be sharpened to `p.A0 = 0`; `Nat.eq_zero_of_not_pos` packages exactly this discrete-order fact.

### Crossing the type boundary through `A0_cast`

Instead of reopening the `natAbs` definition of `A0`, the proof reuses the public API theorem `A0_cast`. This keeps the positivity proof independent of the internal `natAbs` implementation details and validates the cast bridge introduced immediately beforehand.

### Local rewriting with `rw ... at ...`

```lean
rw [hzero] at hcast
```

rewrites only the local hypothesis `hcast`, not the goal. It transports the natural-number fact `A0 = 0` into the integer equality used for the contradiction.

### `norm_num`

After rewriting, `norm_num` simplifies casts such as the integer cast of natural zero and places `hcast` in a form suitable for arithmetic automation. It contributes normalization rather than new number-theoretic content.

### `omega`

The final contradiction is Presburger arithmetic: an integer cannot simultaneously equal zero and be strictly positive. All nonlinear polynomial structure has already been hidden behind earlier theorem interfaces, so `omega` sees only linear order and equality facts.

## Redundancy and duplication

The immediately following `B0_pos` has an almost perfectly symmetric proof. The only substitutions are

- `A0` ↔ `B0`,
- `A0_cast` ↔ `B0_cast`,
- `A_pos` ↔ `B_pos`.

Thus there is clear implementation-level duplication.

Keeping the two named theorems separately is nevertheless reasonable. It preserves the semantic distinction between the lower and upper factors, gives convenient dot-notation APIs to downstream proofs, and makes failures easier to diagnose. A generic helper would save little code while potentially obscuring that meaning.

There may also be a shorter tactic presentation in which `hApos` is not separately named or `norm_num` is avoided, but the current proof makes the logical stages explicit and readable.

## Optimization candidates

Because `A0` is literally `natAbs A` and `A_pos` is already available, a suitable Mathlib positivity lemma for `natAbs` may allow a shorter direct proof. Conceptually one could pursue

```lean
  unfold A0
  -- derive `zeroSectorA ... ≠ 0` from `A_pos`
  -- apply an appropriate positivity theorem for `natAbs`
```

However, this run deliberately performs no Lean build, so the exact available lemma name, its argument order, and the minimal imports needed for that version are **unverified**.

Another possible comparison is to retain the current API-based route but see whether `A0_cast` and `A_pos` allow `omega` to close the goal with fewer preprocessing steps, perhaps eliminating `norm_num`. That possibility is also unverified without compilation.

The current proof has an architectural advantage: it consumes `A0_cast` immediately after that bridge was introduced, demonstrating that the natural representative API is sufficient without exposing `natAbs` again. Therefore a shorter direct proof is not automatically a better design.

## Required Mathlib imports and import-minimization candidates

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

as its import.

The main Mathlib-side ingredients used directly by this theorem are

- `Nat.eq_zero_of_not_pos`,
- the `norm_num` tactic,
- the `omega` tactic,
- the natural/integer coercion and order infrastructure.

`GoldenZeroSectorCandidate.A0`, `A0_cast`, and `A_pos` are upstream project declarations.

This theorem almost certainly needs less than all of `Mathlib`; modules supporting natural-number order, integer casts, `Mathlib.Tactic.Omega`, and `Mathlib.Tactic.NormNum` are plausible ingredients. The **exact minimal import set has not been verified**, because no Lean build is performed in this task and the generated standalone file has a much larger transitive dependency closure. Import reduction is therefore recorded only as an optimization candidate.

## Comparator challenge suitability

**Yes. It is well suited to a compact, intermediate-level Lean proof challenge.**

Useful competing implementations would include

1. the current `A0_cast` → contradiction → `norm_num` → `omega` route,
2. a direct proof using a positivity/nonzero lemma for `natAbs`,
3. an API-preserving version with fewer tactics,
4. a common helper abstracting both `A0_pos` and `B0_pos`.

The comparison should not measure token count alone. More informative criteria are reuse of the existing API, explicitness of the type boundary, coupling to Mathlib implementation lemmas, readability, and robustness under later changes to the representation of `A0`.

## PDF cross-check

The target branch repository tree contains both existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the GitHub connector does not return the binary PDF body through its normal text fetch, and the public raw PDF body could not be retrieved successfully in this run. Therefore the exact PDF page, section, and equation corresponding to 0320 `A0_pos` are **unverified**, and no location is guessed here.

The Lean code, declaration order, dependencies on `A0_cast` / `A_pos`, and the immediately following `B0_pos` were verified against the latest branch version of `Flt5DkMath/FLT5StandAlone.lean`, which is treated as the authoritative source.

## Next declaration to read

The next declaration is 0321 `GoldenZeroSectorCandidate.B0_pos`, also a **`theorem`**.

The authoritative Lean source places immediately after `A0_pos`:

```lean
theorem B0_pos (p : GoldenZeroSectorCandidate) : 0 < p.B0 := by
  by_contra hpos
  have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.B0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hBpos := p.B_pos
  omega
```

Declarations 0320 and 0321 together establish positivity of both natural representatives and prepare the development for the subsequent natural-number factorization arithmetic.
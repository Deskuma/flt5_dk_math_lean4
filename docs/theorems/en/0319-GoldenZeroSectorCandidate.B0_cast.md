# 0319 — `GoldenZeroSectorCandidate.B0_cast`

## Declaration kind

This is a **`theorem`**.

It is the cast bridge that identifies the natural representative $B_0$, introduced by 0317 `GoldenZeroSectorCandidate.B0`, exactly with the original signed upper inversion factor $B$, using the positivity already established by 0313 `GoldenZeroSectorCandidate.B_pos`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Cast equation for the positive upper natural representative. -/
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

For a candidate `p`, the theorem returns the integer equality

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

The left-hand side is a coercion from `ℕ` to `ℤ`, while the right-hand side already lives in `ℤ`.

## Mathematical statement

0317 defines

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

so mathematically

$$
B_0=|B|,
$$

where

$$
B=\operatorname{zeroSectorB}(r,s,d)=U+W.
$$

By 0313 `B_pos`,

$$
B>0
$$

has already been proved. Hence $B\ge0$, so

$$
|B|=B.
$$

Therefore

$$
(B_0:\mathbb Z)=B.
$$

The theorem fixes this elementary fact as an explicit equality across Lean's `ℕ` / `ℤ` type boundary.

## Role in the full proof

The zero-sector inversion first constructs, in the signed integer world,

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
$$

and

$$
0<A<B.
$$

Then 0316 `A0` and 0317 `B0` move to natural representatives

$$
A_0=|A|,\qquad B_0=|B|.
$$

0318 `A0_cast` recovers

$$
(A_0:\mathbb Z)=A,
$$

and the present 0319 `B0_cast` recovers

$$
(B_0:\mathbb Z)=B.
$$

Once both bridges are available, the product, difference, and order information obtained in the signed world can be transported to natural-number arithmetic without loss of meaning.

Indeed, after the immediate natural positivity lemmas, the later theorem `A0_mul_B0` uses `A0_cast` and `B0_cast` to obtain

$$
A_0B_0=4Q^5
$$

in `ℕ`. Likewise `B0_eq_A0_add` converts the signed difference into the subtraction-free natural identity

$$
B_0=A_0+8d^5.
$$

Thus this theorem does not add a new number-theoretic restriction. It is a **correctness bridge preserving the meaning and sign of the upper factor when entering the natural-number factorization layer**.

## Direct dependencies

### `GoldenZeroSectorCandidate.B0`

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

This is the direct definition of the left-hand side.

### `GoldenZeroSectorCandidate.B_pos`

0313 supplies

$$
0<B.
$$

The proof term uses

```lean
p.B_pos.le
```

to weaken this to

$$
0\le B.
$$

### `Int.ofNat_natAbs_of_nonneg`

This Mathlib lemma states, conceptually, that for an integer $z$ with $0\le z$, casting `z.natAbs` back to `ℤ` returns $z$. Here it is instantiated with $z=\operatorname{zeroSectorB}(p.r,p.s,p.d)$.

### `zeroSectorB`

This project definition is the signed upper inversion factor. `B0_cast` does not unfold its internal formula `U+W`; it depends only on its already-proved positivity and on the behavior of `natAbs`.

## Proof flow

1. The goal is `(p.B0 : ℤ) = zeroSectorB p.r p.s p.d`.
2. Definitionally, `p.B0` is `(zeroSectorB p.r p.s p.d).natAbs`.
3. `p.B_pos.le` yields `0 ≤ zeroSectorB ...`.
4. Apply `Int.ofNat_natAbs_of_nonneg p.B_pos.le`.
5. The resulting equality definitionally matches the goal after reduction of `B0`, so `exact` closes the proof.

## Lean-specific processing

### `ℕ` / `ℤ` coercion

The explicit term

```lean
(p.B0 : ℤ)
```

makes the boundary between the natural factorization API and the signed integer inversion API visible in the theorem type itself.

### Weakening strict positivity

The proof does not use `B_pos : 0 < B` directly. It uses `p.B_pos.le : 0 ≤ B`, exactly matching the weakest hypothesis needed by `Int.ofNat_natAbs_of_nonneg`.

### Definitional reduction

There is no explicit `unfold B0`. Lean can reduce `p.B0` to its definition while checking the expected type, so

```lean
exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

is sufficient.

### Dot notation

The candidate-centered API appears as `p.B0` and `p.B_pos`, keeping the dependency on the source candidate explicit and readable.

## Redundancy and duplication

The theorem is completely symmetric with 0318 `A0_cast`. The implementation pattern differs only by replacing

```lean
p.A_pos.le
```

with

```lean
p.B_pos.le.
```

Nevertheless, keeping `A0_cast` and `B0_cast` as separate named theorems preserves the lower/upper factor semantics in the public API. A generic helper would save almost no proof text and could make downstream uses less readable, so this duplication is reasonable.

## Optimization candidates

The current one-line proof is already essentially minimal.

For explanatory purposes, an unverified alternative is

```lean
  simpa [B0] using
    (Int.ofNat_natAbs_of_nonneg p.B_pos.le)
```

which exposes the definition of `B0`. It is longer than the current `exact`, however, and the current proof uses definitional equality naturally.

A generic helper shared by `A0_cast` and `B0_cast` is also possible in principle, but the abstraction gain appears too small to justify the extra API layer. The current implementation is therefore the most natural choice.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The principal Mathlib facilities directly needed by this theorem are

- `Int.ofNat_natAbs_of_nonneg`,
- the order conversion `LT.lt.le`,
- coercion from `ℕ` to `ℤ`.

`GoldenZeroSectorCandidate`, `B0`, `B_pos`, and `zeroSectorB` are project-side upstream declarations.

This theorem alone almost certainly needs a much narrower import than all of `Mathlib`, but the minimal Mathlib module and the import closure of the generated standalone source were not established here because this run does not perform a Lean build. Any concrete import reduction is therefore an **unverified optimization candidate**.

## Comparator challenge suitability

**Yes. It is suitable as a beginner-to-intermediate Lean bridge-theorem challenge.**

Useful comparison points include the current one-line `exact`, `simpa [B0] using ...`, a proof that first unfolds `B0`, and a design that introduces a generic helper shared with `A0_cast`.

The mathematics is elementary, but the example exercises definitional equality, coercion, `natAbs`, strict-to-weak order conversion, and library-lemma selection in a compact form.

## Cross-check against the PDFs

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the normal GitHub connector does not return binary PDF bodies, and direct retrieval of the public raw PDF URLs also failed in this execution environment. Consequently, no concrete PDF page, section, or equation number was verified, and none is guessed here.

The Lean code, declaration order, dependency on `B0` / `B_pos`, and connection to the following `A0_pos` declaration were verified against the latest branch version of `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0320 `GoldenZeroSectorCandidate.A0_pos`, again a **`theorem`**:

```lean
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

By 0319, the signed upper factor $B$ has now been faithfully identified with its natural representative $B_0$. From 0320 onward, positivity is explicitly re-established on the natural representatives themselves, followed by `B0_pos`, `A0_mul_B0`, and `B0_eq_A0_add`.

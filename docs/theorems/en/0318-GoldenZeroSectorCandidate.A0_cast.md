# 0318 — `GoldenZeroSectorCandidate.A0_cast`

## Declaration kind

This declaration is a **`theorem`**.

It is the cast bridge that identifies the natural-number representative $A_0$ introduced by 0316 `GoldenZeroSectorCandidate.A0` with the original signed inversion factor $A$, using the positivity already established by 0314 `GoldenZeroSectorCandidate.A_pos`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Cast equation for the positive lower natural representative. -/
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

Read with its dependency structure exposed, the theorem returns the integer equality

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

for a candidate `p`.

The left-hand side `p.A0` has type `ℕ` and is coerced to `ℤ`; the right-hand side `zeroSectorA ...` already has type `ℤ`.

## Mathematical statement

0316 defined

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

so mathematically

$$
A_0=|A|,
$$

where

$$
A=\operatorname{zeroSectorA}(r,s,d).
$$

By 0314 `A_pos`, however,

$$
A>0
$$

has already been proved. Hence $A\ge0$ and therefore

$$
|A|=A.
$$

Thus, when the natural number $A_0$ is cast back to an integer, it is exactly the original lower factor:

$$
(A_0:\mathbb Z)=A.
$$

This theorem records that elementary fact precisely at the Lean `ℕ` / `ℤ` boundary.

## Role in the overall proof

The zero-sector inversion is first developed in the signed integer world, where the proof has already established

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

Then 0316 `A0` and 0317 `B0` move to the natural representatives

$$
A_0=|A|,\qquad B_0=|B|.
$$

Applying `natAbs` alone, however, leaves only natural numbers whose sign information is no longer present in their type. The present 0318 `A0_cast` reuses the already-proved positivity of $A$ to recover

$$
(A_0:\mathbb Z)=A,
$$

making it possible to move safely between natural-number factorization and the signed inversion identities.

Together with the immediately following `B0_cast`, it yields

$$
(A_0:\mathbb Z)=A,
\qquad
(B_0:\mathbb Z)=B.
$$

Once these two bridges are available, product, difference, and order information proved in the signed world can be transported into natural-number arithmetic. Therefore this theorem does not introduce a new number-theoretic constraint; it is a **correctness bridge that connects the signed inversion data to the later `Nat` factorization machinery without losing meaning**.

## Direct dependencies

### `GoldenZeroSectorCandidate.A0`

This is the direct definition of the natural representative appearing on the left-hand side.

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

After definition reduction, the left-hand side of the theorem becomes

```lean
((zeroSectorA p.r p.s p.d).natAbs : ℤ)
```

### `GoldenZeroSectorCandidate.A_pos`

This is the semantic core of the theorem.

It has already established

$$
0<A.
$$

The proof uses

```lean
p.A_pos.le
```

to weaken this to

$$
0\le A.
$$

The cast theorem only needs nonnegativity, so `.le` supplies exactly the hypothesis required by the Mathlib lemma.

### `Int.ofNat_natAbs_of_nonneg`

This is the Mathlib lemma that closes the proof in one line.

Conceptually, for an integer $z$ with $0\le z$, it states

$$
(\operatorname{natAbs}(z):\mathbb Z)=z.
$$

Here it is instantiated with $z=\operatorname{zeroSectorA}(p.r,p.s,p.d)$.

### `zeroSectorA`

This project definition provides the signed lower inversion factor on the right-hand side. `A0_cast` does not unfold its internal formula, so the theorem is independent of the detailed polynomial expression for $A$.

## Proof flow

1. The goal is

   ```lean
   (p.A0 : ℤ) = zeroSectorA p.r p.s p.d
   ```

2. Definitionally, `p.A0` is

   ```lean
   (zeroSectorA p.r p.s p.d).natAbs
   ```

3. From 0314 `A_pos`,

   ```lean
   p.A_pos.le
   ```

   provides

   ```lean
   0 ≤ zeroSectorA p.r p.s p.d
   ```

4. This nonnegativity proof is passed to `Int.ofNat_natAbs_of_nonneg`.
5. The resulting equality matches the current goal after definitional reduction of `A0`, so `exact` finishes the proof.

## Lean-specific processing

### Coercion from `ℕ` to `ℤ`

The theorem explicitly writes

```lean
(p.A0 : ℤ)
```

because `A0 : ℕ` while the inversion identities live in `ℤ`. The carrier transition is therefore visible directly in the theorem statement.

### Weakening strict positivity to nonnegativity

The expression

```lean
p.A_pos.le
```

turns

```lean
0 < A
```

into

```lean
0 ≤ A
```

because `Int.ofNat_natAbs_of_nonneg` requires only nonnegativity. The proof therefore uses no stronger hypothesis than necessary at the library-lemma boundary.

### No explicit `unfold A0`

The proof is only

```lean
exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

and contains neither `unfold A0` nor `simp [A0]`.

Lean can reduce the reducible definition `A0` while comparing the expected type with the type of the proof term. Thus

```lean
p.A0
```

and

```lean
(zeroSectorA p.r p.s p.d).natAbs
```

are identified by definitional reduction.

### Dot notation

Because `A0` and `A_pos` are candidate-centered declarations in the `GoldenZeroSectorCandidate` namespace, they can be used as

```lean
p.A0
p.A_pos
```

which keeps the bridge theorem compact and readable.

## Redundancy and duplication

The theorem itself has a one-line proof and contains no local redundancy.

The immediately following `B0_cast` is structurally symmetric:

```lean
exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

so the implementation pattern is duplicated.

Nevertheless, keeping separate named theorems `A0_cast` and `B0_cast` preserves the semantic distinction between the lower and upper factors in the public API. A generic helper would save little code and could make downstream proofs less self-documenting. This symmetric duplication is therefore reasonable API-level duplication rather than accidental repetition.

## Optimization candidates

The current proof is already close to minimal and offers essentially no meaningful proof-length optimization.

For explanatory explicitness, one could consider

```lean
  simpa [A0] using
    (Int.ofNat_natAbs_of_nonneg p.A_pos.le)
```

which makes the definition reduction of `A0` visible. This is arguably easier for a reader learning Lean, but it is longer than the current `exact` proof.

A generic cast helper shared by `A0_cast` and `B0_cast` is also theoretically possible, but it would likely be only a thin wrapper that takes an integer and a nonnegativity proof, and may not improve the API.

Accordingly, the present one-line proof is the most natural design. These alternatives are **unverified candidates** because this run does not perform a Lean build.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib functionality directly visible in this theorem is centered on

- `Int.ofNat_natAbs_of_nonneg`,
- order weakening via `LT.lt.le`,
- coercion from `ℕ` to `ℤ`.

`GoldenZeroSectorCandidate`, `A0`, `A_pos`, and `zeroSectorA` are project declarations supplied upstream.

This theorem in isolation almost certainly requires less than the full `Mathlib` import. However, the minimal import set compatible with the generated standalone module, and the smallest Mathlib module exporting `Int.ofNat_natAbs_of_nonneg`, were not verified because Lean build execution is explicitly excluded. Any concrete import reduction should therefore be treated as an **unverified optimization candidate**.

## Comparator challenge suitability

**Suitable. This is a good beginner-to-intermediate Lean bridge-theorem challenge.**

Useful variants to compare include:

- the current `exact Int.ofNat_natAbs_of_nonneg p.A_pos.le`,
- `simpa [A0] using ...` with explicit definition reduction,
- normalizing the goal first with `rw [A0]` and then applying the library lemma,
- introducing a generic helper used by both `A0_cast` and `B0_cast`.

The mathematics is elementary, but the declaration simultaneously exposes **definitional equality, coercions, strict-to-weak order conversion, and library-lemma selection**, which makes it valuable as a Comparator exercise.

## PDF cross-check

The target branch contains the existing Japanese and English PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed in the repository.

The normal GitHub text fetch does not return binary PDF contents, so this run could not directly verify the precise page, section, or equation number corresponding to this declaration. No such location is inferred.

The Lean code, declaration order, dependencies on `A0` and `A_pos`, and transition to the following `B0_cast` were verified against the latest `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is 0319 `GoldenZeroSectorCandidate.B0_cast`, also a **`theorem`**.

```lean
/-- Cast equation for the positive upper natural representative. -/
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

Where 0318 recovers the lower factor identity

$$
(A_0:\mathbb Z)=A,
$$

0319 recovers the upper factor identity

$$
(B_0:\mathbb Z)=B.
$$

Once both are available, the natural pair $(A_0,B_0)$ can be identified exactly with the signed pair $(A,B)$ before proceeding to positivity, product, difference, coprimality, and power splitting.

# 0100 — `SquareGoldenM`

## Lean type

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

## Mathematical statement

`SquareGoldenM` is not a theorem but the first coordinate definition in `SquareGoldenNormalForm.lean`.

From natural numbers `z,y`, it forms the integer

$$
M=z^2+y^2.
$$

Because the squaring is definitionally carried out in `ℤ`, the Lean right-hand side is

```lean
(z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

Mathematically, this is the endpoint-square mass coordinate: it packages the sum of the two endpoint squares into the named coordinate `M`.

## Role in the full proof

In articles 0093–0099, inside `SquareGoldenBridge.lean`, the passage from `GN5` to the golden-ratio quadratic form directly used the coordinates

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y.
$$

The new module `SquareGoldenNormalForm.lean` promotes the first endpoint-square coordinate to the named API

$$
M:=\mathrm{SquareGoldenM}(z,y)=z^2+y^2.
$$

This lets the later normal form avoid repeating long coordinate expressions and instead state several preserved quantities over the same coordinate pair `(M,N)`:

$$
\mathrm{GoldenNorm}(M,N),\qquad M-2N,\qquad M^2-4N^2,\qquad (2M+N)^2-5N^2.
$$

In particular, the immediately following `squareGolden_tenth_boundary_base` proves

$$
M-2N=(z-y)^2,
$$

while `squareGolden_square_discriminant` proves

$$
M^2-4N^2=(z^2-y^2)^2.
$$

Thus `SquareGoldenM` is the first component of the common coordinate system that binds the golden norm and the square boundary together.

## Direct dependencies

There are no project-local direct dependencies. The definition itself only uses:

1. `ℕ` and `ℤ`.
2. Coercions from naturals to integers, `(z : ℤ)` and `(y : ℤ)`.
3. Integer addition.
4. Integer powers `^ 2`.

Conceptually, article 0096 `GN5_eq_goldenNorm_squareLink` is the important predecessor: the same endpoint-square coordinate already appears there, and the present definition simply gives that expression a reusable name for the later normal-form layer.

## Proof flow

Since this is a `def`, there is no proof script. Lean registers

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

as a definitional equality.

Later proofs can expose the right-hand side with `unfold SquareGoldenM`, `simp [SquareGoldenM]`, or `simpa [SquareGoldenM, ...]`.

## Lean-specific processing

The most important Lean design choice is that the codomain is `ℤ` from the beginning.

The inputs are `z y : ℕ`, but later statements naturally use subtraction, such as

$$
M-2N
$$

and

$$
M^2-4N^2.
$$

Defining the coordinate in `ℕ` would introduce truncated subtraction and would also complicate its connection to `GoldenNorm : ℤ → ℤ → ℤ`.

The definition therefore casts `z,y` at the boundary and fixes the coordinate itself in `ℤ`. This makes the later golden-norm layer type-correct without repeated coercions.

The use of `def` rather than `abbrev` also provides a useful named abstraction boundary instead of an alias that tends to unfold transparently everywhere.

## Redundancy and duplication

The expression

$$
z^2+y^2
$$

has already appeared in article 0096 `GN5_eq_goldenNorm_squareLink` and article 0098 `endpoint_square_discriminant`.

So at the level of raw algebra the definition is repetitive. Its purpose, however, is not to add a new identity but to introduce coordinate vocabulary shared by the `SquareGoldenNormalForm` layer.

This duplication is therefore intentional from the viewpoint of proof architecture: it shortens later structure fields and lets the same `M` participate simultaneously in the golden norm, the tenth boundary, the square discriminant, and the discriminant-five relation.

## Optimization candidates

1. Keep the current design. A small named coordinate is already effective.
2. Combine `SquareGoldenM` and the following `SquareGoldenN` into one coordinate structure, for example `SquareGoldenCoords` with fields `M N : ℤ`.
3. Generalize the inputs to `(z y : ℤ)`. The current proof graph starts from natural-number FLT data, however, so the explicit `ℕ → ℤ` boundary preserves provenance clearly.
4. Refactor article 0096 to reuse this definition. Doing so would reverse the current module dependency and therefore require changing the module split.
5. Replace `def` by `abbrev`. This is possible, but easier automatic unfolding is not necessarily an improvement here.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This definition by itself needs only very small foundations: naturals, integers, coercions, addition, and powers. Therefore the umbrella import is clearly larger than necessary for this declaration alone.

However, later theorems in the source module `SquareGoldenNormalForm.lean` use tactics and utilities such as `ring`, `exact_mod_cast`, and `simpa`. Without running a Lean build, this article does not claim a precise minimal import set for the whole module. It is nevertheless clear that `SquareGoldenM` itself does not require all of `Mathlib`.

A safe import-optimization experiment would enumerate the tactics and integer APIs actually used by `SquareGoldenNormalForm.lean`, then test whether the module can be reduced to imports centered on items such as `Mathlib.Tactic.Ring` plus the needed algebraic foundations.

## Comparator challenge suitability

As a standalone proof challenge it is weak, because this is an API-design declaration rather than a theorem.

It is useful, however, as a coordinate-design Comparator. Possible variants are:

1. The current separate `SquareGoldenM` / `SquareGoldenN` definitions.
2. One function returning `(ℤ × ℤ)`.
3. A `structure SquareGoldenCoords` with named fields.
4. Keeping coordinates in `ℕ` and casting only at use sites.
5. The current design, which lifts to `ℤ` at the coordinate boundary.

Useful evaluation axes are readability of downstream theorems, number of casts, rewrite ergonomics, provenance in the proof graph, and compactness of the normal-form structure.

## Relation to existing materials

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its generated-source marker confirms that this definition is the first declaration of `DkMath/FLT/Five/SquareGoldenNormalForm.lean`, immediately after `SquareGoldenBridge.lean`.

The standalone manifest likewise places `SquareGoldenNormalForm.lean` directly after `SquareGoldenBridge.lean`.

For the existing Japanese and English PDFs, GitHub code search returned an upstream 502 error during this run, so no concrete page or section correspondence could be verified. No PDF location is guessed here.

## Next declaration to read

The immediately following declaration in dependency order is the second coordinate:

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

Therefore article 0101 should naturally cover `SquareGoldenN`. After that, the first theorem using both coordinates is

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

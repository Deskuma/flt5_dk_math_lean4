# 0096 — `GN5_eq_goldenNorm_squareLink`

## Lean type

```lean
theorem GN5_eq_goldenNorm_squareLink (g y : ℕ) :
    (GN5 g y : ℤ) =
      GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) := by
  unfold GN5 GoldenNorm
  push_cast
  ring
```

## Mathematical statement

For natural numbers `g, y`, the integer cast of the fifth-cyclotomic factor `GN5 g y` is exactly the golden-ratio quadratic form evaluated at the endpoint-square coordinates

$$
M=(g+y)^2+y^2,
\qquad
N=(g+y)y.
$$

Thus

$$
\mathrm{GN5}(g,y)
=\mathrm{GoldenNorm}\bigl((g+y)^2+y^2,(g+y)y\bigr),
$$

where

$$
\mathrm{GoldenNorm}(M,N)=M^2+MN-N^2.
$$

Expanding `GN5` gives

$$
\mathrm{GN5}(g,y)
=g^4+5g^3y+10g^2y^2+10gy^3+5y^4,
$$

and expanding the right-hand side yields the same polynomial.

## Role in the full proof

Article 0093 introduced `GoldenNorm`; 0094 rewrote `GN5` into the square/cross form

$$
(g^2)^2+5g^2y(g+y)+5\bigl(y(g+y)\bigr)^2,
$$

and 0095 isolated the coordinate identity

$$
g^2+2y(g+y)=(g+y)^2+y^2.
$$

The present theorem is the actual bridge that combines those preparations into one API. In the proof graph it closes the chain

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross coordinates}
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}.
$$

After this point, later arguments no longer need to manipulate the quartic coefficients of `GN5` directly; they can move into arithmetic of the quadratic form `GoldenNorm`. The standalone source later reuses the symmetric form of this theorem to turn a `GoldenNorm` value back into `(GN5 g y : ℤ)` and connect it to fifth-power information. It is also reused in the signed square/golden exceptional construction after substituting `g = w - v` and `y = v`.

## Direct dependencies

The direct project-local dependencies are:

1. `GN5 : ℕ → ℕ → ℕ`
2. `GoldenNorm : ℤ → ℤ → ℤ`

Articles 0094 `GN5_eq_square_cross_form` and 0095 `square_cross_coordinate_change` are mathematically explanatory intermediate results, but the Lean proof body does not invoke them directly.

On the Mathlib side, the proof mainly needs:

1. coercions from naturals to integers,
2. `push_cast` to distribute casts through arithmetic expressions,
3. `ring` for polynomial normalization in a commutative ring.

## Proof flow

The proof consists of three steps:

```lean
unfold GN5 GoldenNorm
push_cast
ring
```

First, `GN5` and `GoldenNorm` are unfolded. Next, `push_cast` pushes the coercions from natural-number expressions into integer addition, multiplication, and powers so that both sides become polynomials in `ℤ`. Finally, `ring` normalizes both sides and proves equality.

Mathematically, this is the verification that expanding

$$
\bigl((g+y)^2+y^2\bigr)^2
+\bigl((g+y)^2+y^2\bigr)(g+y)y
-\bigl((g+y)y\bigr)^2
$$

produces the coefficient pattern `1,5,10,10,5` of `GN5 g y`.

## Lean-specific processing

### 1. Type boundary from `ℕ` to `ℤ`

`GN5 g y` is natural-valued, while `GoldenNorm` is defined over integers because it contains subtraction. Therefore the theorem explicitly casts the left-hand side as `(GN5 g y : ℤ)`.

### 2. `push_cast`

Before `ring` can compare the expressions, casts such as `↑((g+y)^2+y^2)` and `↑((g+y)y)` must be distributed into integer arithmetic. `push_cast` performs this boundary normalization.

### 3. `ring`

After casts are pushed through, the goal is a pure polynomial identity in `ℤ`, and `ring` closes it. Unlike 0094 and 0095, which live entirely in the natural-number semiring, this theorem essentially crosses into the integer ring because of the subtraction in `GoldenNorm`.

## Redundancy and overlap

The proof does not call 0094 or 0095; instead it unfolds both definitions and asks `ring` to prove the whole identity at once. From the perspective of proof terms, this makes the two previous lemmas appear computationally redundant.

Their roles are nevertheless distinct. Article 0094 exposes the compression from a quartic polynomial to square/cross coordinates, while 0095 exposes the move from square/cross coordinates to endpoint-square coordinates. The present theorem packages the final equality as the downstream API. The development therefore separates shortest kernel proof from explanatory proof graph.

## Optimization candidates

### Candidate A — keep the current proof

This is compact and robust. `unfold`, `push_cast`, and `ring` close the result while exposing one semantically clear bridge theorem to downstream code.

### Candidate B — structural proof using 0094 and 0095

A staged proof could explicitly rewrite by the square/cross form from 0094 and the coordinate change from 0095 before reaching `GoldenNorm`. That would align the Lean script more closely with the mathematical exposition.

The cost is extra rewriting and coercion management, which may make the proof longer and more brittle than the current three-line normalization.

### Candidate C — helper definitions for endpoint coordinates

Named definitions for `M(g,y)` and `N(g,y)` could shorten repeated expressions such as

```lean
((g + y) ^ 2 + y ^ 2)
((g + y) * y)
```

Later source reuses the same coordinate pattern, so this becomes more attractive if reuse continues to grow.

### Candidate D — integration with the Golden-order norm layer

When later modules identify `GoldenNorm` with the norm in the actual golden integer order, the API could be organized into two layers: a polynomial bridge and an algebraic-integer norm bridge. The lightweight nature of the current theorem should still be preserved.

## Required Mathlib imports and import optimization

The generated standalone artifact uses `import Mathlib`.

For this theorem alone, the directly needed facilities are natural/integer coercions, basic commutative-ring arithmetic, `push_cast`, and `ring`. Therefore the umbrella import is larger than necessary for this isolated result, and it is likely possible to reduce imports to the Mathlib modules supplying cast tactics and ring normalization.

However, the generated artifact places this theorem inside the `SquareGoldenBridge.lean` section, followed by further discriminant identities over integers. No Lean build is performed in this museum run, so the exact minimal import set is not asserted.

## Comparator challenge suitability

This theorem is a good Comparator challenge. The main comparison is between proof brevity and explicit exposure of mathematical structure.

At least three approaches are natural:

1. the current `unfold; push_cast; ring` proof,
2. a staged rewrite proof explicitly using 0094 and 0095,
3. a proof based on named endpoint-coordinate helpers and a general quadratic-form identity.

Useful evaluation criteria are not merely line count, but stability of cast handling, downstream reuse, visibility of mathematical intent, and robustness against Mathlib changes.

## Relation to existing materials

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its generated manifest places this theorem in the `DkMath/FLT/Five/SquareGoldenBridge.lean` section.

For the existing Japanese and English PDFs, GitHub code search returned an upstream 502 error during this run, so a concrete matching page or section could not be established. No PDF page number or textual correspondence is guessed here.

## Next theorem to read

The next theorem in the standalone source is

```lean
theorem four_mul_goldenNorm_eq_discriminant_five (m n : ℤ) :
    4 * GoldenNorm m n = (2 * m + n) ^ 2 - 5 * n ^ 2 := by
  unfold GoldenNorm
  ring
```

The next article will therefore study the diagonalization

$$
4\,\mathrm{GoldenNorm}(m,n)
=(2m+n)^2-5n^2,
$$

which makes the discriminant-five structure of the golden-ratio quadratic form explicit.
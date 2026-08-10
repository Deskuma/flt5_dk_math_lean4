# 0095 — `square_cross_coordinate_change`

## Lean type

```lean
theorem square_cross_coordinate_change (g y : ℕ) :
    g ^ 2 + 2 * (y * (g + y)) = (g + y) ^ 2 + y ^ 2 := by
  ring
```

## Mathematical statement

For natural numbers $g,y$, this theorem states

$$
g^2+2y(g+y)=(g+y)^2+y^2.
$$

Using the square/cross coordinates introduced by 0094 `GN5_eq_square_cross_form`,

$$
A=g^2,\qquad B=y(g+y),
$$

the left-hand side is simply

$$
A+2B,
$$

while the right-hand side is the sum of the two endpoint squares

$$
(g+y)^2+y^2.
$$

Thus the theorem is better read not merely as a quadratic identity but as the lemma certifying the first coordinate of the change of variables

$$
(g^2,\,y(g+y))
\longrightarrow
((g+y)^2+y^2,\,(g+y)y)
$$

used to send `GN5` into the golden-ratio quadratic form.

## Role in the overall proof

In 0094 we obtained

$$
\mathrm{GN5}(g,y)
=(g^2)^2+5g^2y(g+y)+5\bigl(y(g+y)\bigr)^2,
$$

a square/cross form.

The next theorem, `GN5_eq_goldenNorm_squareLink`, identifies this expression with 0093 `GoldenNorm`,

$$
\mathrm{GoldenNorm}(m,n)=m^2+mn-n^2.
$$

The coordinates used there are

$$
m=(g+y)^2+y^2,
\qquad
n=(g+y)y.
$$

The present theorem guarantees that this $m$ may also be written from the previous square/cross coordinates as

$$
m=g^2+2y(g+y).
$$

Hence, in the proof graph, this theorem is the middle coordinate-change step

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross form}
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}.
$$

The following theorem may not need to invoke this lemma by name because `ring` can perform the same algebraic normalization internally. Nevertheless, keeping this equality as a named theorem exposes why the endpoint-square coordinates arise naturally.

## Direct dependencies

There are no direct project-local definition or theorem dependencies.

The proof directly needs only:

1. addition, multiplication, and powers on `ℕ`;
2. the `ring` tactic for polynomial identities over a commutative semiring.

0094 `GN5_eq_square_cross_form` and 0093 `GoldenNorm` are not referenced in the proof term itself, but they are essential semantic neighbors in the overall argument.

## Proof flow

The proof is just

```lean
ring
```

and closes immediately.

By hand, the right-hand side expands as

$$
(g+y)^2+y^2
=g^2+2gy+y^2+y^2,
$$

while the left-hand side is

$$
g^2+2y(g+y)
=g^2+2gy+2y^2,
$$

so the two expressions agree.

There is no subtraction or division. The statement is purely a commutative-semiring polynomial identity over the natural numbers, making `ring` one of the most appropriate proof methods.

## Lean-specific processing

### 1. Semiring normalization by `ring`

Lean does not automatically identify the two sides merely from associativity, commutativity, and distributivity. The `ring` tactic normalizes both sides and verifies that they represent the same polynomial.

### 2. The theorem remains entirely in `ℕ`

This theorem uses only natural numbers and introduces no coercion to integers. The next theorem, `GN5_eq_goldenNorm_squareLink`, connects to `GoldenNorm : ℤ → ℤ → ℤ`, so casts from `ℕ` to `ℤ` appear there. The present lemma remains on the natural-number side immediately before that transition.

### 3. The design avoids coercion lemmas here

By isolating the coordinate identity over `ℕ`, the proof avoids mixing in `norm_cast`, `push_cast`, or `Int.ofNat` reasoning. This localizes the coercion complexity to the subsequent bridge theorem.

## Redundant or overlapping parts

Viewed purely as proof code, this theorem could be completely inlined into the `ring` proof of the following `GN5_eq_goldenNorm_squareLink` theorem.

Mathematically it is also only a specialization of the general identity

$$
(a-b)^2+2ba=a^2+b^2
$$

with $a=g+y$ and $b=y$.

However, the declaration is named `square_cross_coordinate_change`: its purpose is not to add a general algebra lemma but to make the coordinate change explicit in the proof architecture. The formula is therefore algebraically redundant but useful as an explanatory interface.

## Optimization candidates

### Candidate A — Keep the theorem as is

This gives the best explanatory value. A tiny theorem fixes the meaning of the coordinate change and provides a visible intermediate point before the golden bridge.

### Candidate B — Inline it into the following theorem

Inside `GN5_eq_goldenNorm_squareLink`, one could potentially use a single normalization proof such as `unfold GN5 GoldenNorm; push_cast; ring`, removing this declaration.

That reduces line count, but makes the square/cross-to-endpoint-square transition less visible in the proof graph.

### Candidate C — Generalize the identity

One could introduce a theorem over a commutative semiring expressing

$$
x^2+2y(x+y)=(x+y)^2+y^2.
$$

If there are no other call sites, however, the abstraction cost would likely exceed the benefit.

### Candidate D — Introduce a coordinate structure

If square/cross coordinates are reused later, one could define named coordinates such as

```lean
A := g ^ 2
B := y * (g + y)
M := (g + y) ^ 2 + y ^ 2
N := (g + y) * y
```

and expose an API like `M = A + 2 * B`.

At present this appears to be a one-off bridge, so such a structure would likely be over-engineering.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact on the target branch uses `import Mathlib`.

For this theorem in isolation, only the basic semiring structure of natural numbers and the `ring` tactic are required. Therefore the umbrella `Mathlib` import is larger than necessary for this single declaration, and import optimization could likely reduce it to the Mathlib module providing `ring` together with basic natural-number algebra.

However, the split source file `SquareGoldenBridge.lean` could not be fetched directly from the target branch, so the concrete minimal import module names are not asserted without a build check.

The whole `SquareGoldenBridge.lean` module involves integer coercions and `GoldenNorm` starting with the next theorem, so module-level import optimization should not be decided from this lemma alone.

## Comparator challenge suitability

This theorem is suitable, although the challenge concerns proof engineering and explanatory value rather than difficult mathematics.

Possible competitors are:

1. the current one-line `ring` proof;
2. a `ring_nf` proof;
3. a rewrite-oriented proof using `simp [pow_two, mul_add, add_mul]` or similar;
4. deleting the theorem and inlining the equality into `GN5_eq_goldenNorm_squareLink`;
5. proving a generic commutative-semiring identity and specializing it here.

Evaluation criteria should include proof-term size, readability, import weight, whether the meaning of the coordinate change survives as a named edge, and whether the following bridge theorem becomes easier to audit.

The current `ring` proof is already essentially minimal locally; the main Comparator question is whether this theorem deserves to remain an independent architectural node.

## PDF and source basis

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. It places this theorem immediately after 0094 `GN5_eq_square_cross_form` and immediately before `GN5_eq_goldenNorm_squareLink`.

The standalone manifest comment records this section as originating from `DkMath/FLT/Five/SquareGoldenBridge.lean`.

A GitHub code-search attempt for the exact corresponding locations in the existing Japanese and English PDFs again returned an upstream 502 error during this run, so no PDF page or section number is asserted. No PDF-specific statement has been filled in by guesswork.

A direct fetch of the presumed split-source repository path also returned 404, so the split file's import header is likewise not guessed.

## Next declaration to read

The next source declaration is

```lean
theorem GN5_eq_goldenNorm_squareLink (g y : ℕ) :
    (GN5 g y : ℤ) =
      GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) := by
  unfold GN5 GoldenNorm
  ...
```

This is the first theorem to identify

$$
\mathrm{GN5}(g,y)
$$

directly with

$$
\mathrm{GoldenNorm}\bigl((g+y)^2+y^2,\,(g+y)y\bigr).
$$

0094 compressed `GN5` into the square/cross form, and 0095 exposed the endpoint-square coordinates. The next article, 0096, is where those two steps finally become the golden-ratio quadratic-form bridge itself.
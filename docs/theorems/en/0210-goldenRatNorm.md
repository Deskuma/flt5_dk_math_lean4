# 0210 — `goldenRatNorm`

## Lean type

```lean
/-- The golden norm polynomial on rational coordinates. -/
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

This is a `def`, not a theorem. It defines on 0209 `GoldenRat = ℚ × ℚ` the same quadratic golden-norm polynomial as for golden integers, now with rational values.

## Mathematical statement and meaning of the declaration

Read `x : GoldenRat` as coordinates `(u,v)`, representing

$$
u+v\varphi,\qquad u,v\in\mathbb Q.
$$

Then `goldenRatNorm x` is

$$
Q(u,v)=u^2+uv-v^2.
$$

This is the same polynomial as the integer-coordinate norm from 0164 `goldenNorm`,

$$
N(a+b\varphi)=a^2+ab-b^2,
$$

with the coefficient domain extended from $\mathbb Z$ to $\mathbb Q$.

The value is not always nonnegative, so it is not a length or a norm in the usual analytic sense. The Euclidean-remainder argument later uses its absolute value

$$
|Q(u,v)|
$$

to measure contraction.

## Role in the full proof

The purpose of `GoldenEuclidean.lean` is to construct norm-Euclidean division on `GoldenInt`. The module comment explains the strategy: represent the rational quotient in the golden basis, round both coordinates to nearest integers, and place the resulting error `(u,v)` inside the fundamental cell

$$
|u|\le\frac12,\qquad |v|\le\frac12.
$$

On that cell one proves

$$
|u^2+uv-v^2|\le\frac{5}{16}<1.
$$

After restoring the divisor norm, this gives a remainder whose absolute norm is strictly smaller than that of the divisor.

`goldenRatNorm` is the central definition naming the quadratic quantity of the rounding error. Later, `goldenRemainder_norm_rat_identity` expresses the rationalized remainder norm as

$$
N(y)\,Q(\text{quotient error}),
$$

and the strict-decrease proof explicitly uses that the absolute value of `goldenRatNorm` on the rounding cell is less than `1`.

Thus 0210 is not merely a copy of the integer norm. It is the bridge from divisibility arguments in the integral order to the local contraction factor used by the Euclidean algorithm.

## Direct dependencies

The direct dependency surface is small:

- 0209 `GoldenRat := ℚ × ℚ`
- product projections `.1` and `.2`
- rational addition, multiplication, subtraction, and natural-number powers

Because this is a definition, it has no direct proof-theorem dependency.

Conceptually,

$$
\texttt{GoldenRat}
\longrightarrow
Q(u,v)=u^2+uv-v^2
\longrightarrow
\texttt{goldenRatNorm}.
$$

It uses the same mathematical polynomial as the integer `goldenNorm`, but the current source keeps the two definitions separate.

## Construction flow

The definition directly returns the coordinate quadratic form:

```lean
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

1. Square the first coordinate `x.1`.
2. Add the cross term `x.1 * x.2`.
3. Subtract the square of the second coordinate `x.2`.

This extends to $\mathbb Q^2$ the quadratic form associated with the golden-basis relation $\varphi^2=\varphi+1$.

## Lean-specific processing

Because 0209 `GoldenRat` is an `abbrev`, Lean treats `x : GoldenRat` essentially as `x : ℚ × ℚ`. The projections `.1` and `.2` therefore work without additional coercions or custom projection lemmas.

In `x.1 ^ 2`, the exponent `2` is a natural-number power and the expected type determines the base as `ℚ`. The remaining operations are likewise elaborated as rational ring operations.

This transparency is useful downstream: proofs can unfold the definition with forms such as `simp [goldenRatNorm]` or `dsimp only [goldenNorm, goldenRatNorm]`, expose an explicit polynomial, and then hand it to `ring` or ordered-arithmetic reasoning.

## Redundancy and duplication

The clearest duplication is with 0164 `goldenNorm`:

```lean
goldenNorm x = x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

and

```lean
goldenRatNorm x = x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

differ essentially only in coefficient type.

One could define the same quadratic polynomial once over a suitable generic commutative ring and specialize it to integers and rationals. The current design, however, keeps unfolded goals extremely simple and avoids introducing extra coercions or abstraction layers into the Euclidean estimates.

## Optimization candidates

1. **Generalize the common quadratic polynomial**
   - define a suitable `goldenNormPoly` once and specialize it to the integer and rational APIs.

2. **Publish a cast bridge from the integer norm**
   - when `GoldenInt` coordinates are cast to `ℚ`, a theorem identifying `goldenRatNorm` with `(goldenNorm x : ℚ)` could simplify later cast-heavy proofs.

3. **Use a Mathlib quadratic-form abstraction**
   - structurally natural, but possibly too heavy for the explicit two-variable calculations used here.

4. **Keep the current explicit formula**
   - easy to unfold into `ring` and inequality tactics and highly auditable.

At present option 4 has strong practical advantages. Options 1 or 2 become more attractive if integer/rational duplication grows further.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct surface needed by 0210 alone is very small, essentially:

- `ℚ`
- `Prod`
- basic ring operations and natural-number powers

The complete `GoldenEuclidean.lean` module later uses rounding, absolute values, inequalities, integer/rational casts, and Euclidean-domain construction, so its true minimal import set is substantially broader.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful comparison variants are:

- A: current `GoldenRat := ℚ × ℚ` with a direct quadratic formula
- B: a generic `goldenNormPoly` shared by integer and rational versions
- C: bundle the form using Mathlib `QuadraticForm` or related infrastructure
- D: center the rational API around a cast bridge from the integer norm

Useful metrics include proof size, coercion burden, effectiveness of `simp` / `ring`, readability of the Euclidean-contraction proof, generalizability, and transparency of unfolding.

The contrast between A and B is especially instructive: it measures the trade-off between explicit-coordinate duplication and the coercion/abstraction cost of sharing a generic polynomial.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this definition follows 0209 `GoldenRat` and is immediately followed by 0211 `exists_int_near_rat`, stating that every rational lies within `1/2` of an integer. Later, both `goldenRemainder_norm_rat_identity` and the Euclidean-size strict-decrease proof use `goldenRatNorm` explicitly.

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0211 `exists_int_near_rat`**:

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩
```

Declaration 0210 prepares the quadratic form measuring rounding error; 0211 guarantees that each rational coordinate can be rounded with error at most `1/2`. From there the development moves to simultaneous two-coordinate rounding, the norm bound on the fundamental cell, and strict contraction of the Euclidean remainder.

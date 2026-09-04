# 0225 — `goldenEuclideanSize_pos_of_ne_zero`

## Lean type

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

This is a `theorem` stating that every nonzero golden integer has strictly positive Euclidean size.

## Mathematical statement

Declaration 0224 defines

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N,
$$

where the golden norm is

$$
N(a+b\varphi)=a^2+ab-b^2\in\mathbb Z.
$$

The present theorem states

$$
x\neq0\Longrightarrow 0<|N(x)|.
$$

Declaration 0215 `goldenNorm_ne_zero_of_ne_zero` has already established

$$
x\neq0\Longrightarrow N(x)\neq0.
$$

Therefore the natural-number absolute value `Int.natAbs` of the integer norm is positive, and the Euclidean size is strictly positive on nonzero elements.

## Role in the full proof

Declarations 0220–0223 construct quotient and remainder and prove the reconstruction law. Declaration 0224 then introduces the Euclidean measure

$$
\operatorname{size}(x)=|N(x)|.
$$

The present theorem guarantees that this measure does not collapse a nonzero element to zero.

This positivity is used directly in the final `EuclideanDomain GoldenInt` construction. In the source proof of `mul_left_not_lt`, for a nonzero `b` one obtains

```lean
have hbSize : 1 ≤ goldenEuclideanSize b :=
  goldenEuclideanSize_pos_of_ne_zero hb
```

and combines this with 0226 `goldenEuclideanSize_mul` to derive

$$
\operatorname{size}(a)
\le
\operatorname{size}(a)\operatorname{size}(b)
=
\operatorname{size}(ab).
$$

Thus 0225 is not merely a sanity check. It is a basic certificate ensuring that the Euclidean relation cannot become spuriously smaller under multiplication by a nonzero factor.

The same positivity also expresses the discreteness of the natural-number measure used when interpreting strict remainder decrease.

## Direct dependencies

The direct dependencies are:

- 0224 `goldenEuclideanSize`
- 0215 `goldenNorm_ne_zero_of_ne_zero`
- Mathlib's `Int.natAbs_pos`

Conceptually,

$$
x\neq0
\Longrightarrow
N(x)\neq0
\Longrightarrow
|N(x)|_{\mathbb N}>0
\Longrightarrow
\operatorname{size}(x)>0.
$$

The golden-order-specific algebra is already contained in 0215; the present theorem is a light transport step into the natural-number Euclidean measure API.

## Proof flow

The proof has only two stages.

```lean
rw [goldenEuclideanSize, Int.natAbs_pos]
```

First, `goldenEuclideanSize x` unfolds to `Int.natAbs (goldenNorm x)`, and `Int.natAbs_pos` rewrites

```lean
0 < Int.natAbs (goldenNorm x)
```

into

```lean
goldenNorm x ≠ 0.
```

Then

```lean
exact goldenNorm_ne_zero_of_ne_zero hx
```

applies 0215 to the assumption `hx : x ≠ 0` and closes the goal.

## Lean-specific processing

`Int.natAbs_pos` connects positivity of an integer's natural absolute value with nonzeroness of the integer. By using it as a rewrite theorem, the proof moves from a goal in `ℕ` back to a nonzero statement in `ℤ`.

This cleanly handles the type boundary:

- `goldenNorm x : ℤ`
- `Int.natAbs (goldenNorm x) : ℕ`
- `0 < goldenEuclideanSize x : Prop`

without introducing any manual coercion arithmetic.

The element `x` is an implicit argument `{x : GoldenInt}`. At call sites Lean can infer it from the nonzero hypothesis, so the final Euclidean-domain proof can write `goldenEuclideanSize_pos_of_ne_zero hb` without supplying `x` explicitly.

## Redundancy and duplication

Mathematically, 0225 is a thin wrapper around 0215 plus the definition from 0224. It does not establish new golden-order arithmetic.

The wrapper is nevertheless useful at the API boundary. The final `EuclideanDomain` construction needs a proposition about the natural-number measure, not merely `goldenNorm x ≠ 0`. This theorem absorbs the `ℤ → ℕ` conversion once and gives downstream proofs a statement in exactly the required form.

Without it, clients would repeatedly write

```lean
rw [goldenEuclideanSize, Int.natAbs_pos]
exact goldenNorm_ne_zero_of_ne_zero ...
```

which would obscure the proof intent.

## Optimization candidates

1. **Keep the current theorem**
   - it is short, has a transparent dependency chain, and is convenient downstream.

2. **Try a one-line `simpa` proof**
   - a form such as `simpa [goldenEuclideanSize, Int.natAbs_pos] using goldenNorm_ne_zero_of_ne_zero hx` may elaborate.
   - Exact elaboration is unverified here because no Lean build is run.

3. **Expose `goldenEuclideanSize_eq_zero_iff`**
   - a theorem `goldenEuclideanSize x = 0 ↔ x = 0` could package zero-detection and allow positivity to be derived from a more reusable interface.

4. **Generalize the norm-to-measure bridge**
   - if further quadratic integer rings are developed, the step from nonzero norm to positive `natAbs` measure can be factored into a generic helper.

The current proof is already small enough that local compression is not a high-priority optimization.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface needed by this theorem is mainly:

- `Int.natAbs_pos`
- basic rewrite and equality machinery

The golden-order-specific declarations `goldenNorm_ne_zero_of_ne_zero` and `goldenEuclideanSize` are upstream in the same development.

The theorem in isolation should require much less than all of `Mathlib`. However, the surrounding `GoldenEuclidean.lean` module also uses rational rounding, `field_simp`, `nlinarith`, well-founded measures, and Euclidean-domain construction, so meaningful import minimization must be measured at module scope. No Lean build is performed in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. The theorem is small enough that proof-style differences are easy to compare.

Possible contestants are:

- A: current `rw` + `exact`
- B: a `simpa [...] using goldenNorm_ne_zero_of_ne_zero hx` proof
- C: derive positivity from a prior `goldenEuclideanSize_eq_zero_iff`
- D: use a generic norm-measure helper

Useful metrics include proof-term size, visibility of the type conversion, downstream reuse, generalizability, and dependency depth on Mathlib lemmas.

Variant A makes the `ℤ → ℕ` boundary especially explicit and is therefore strong from an auditability perspective.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source order is:

```lean
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)

theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx

theorem goldenEuclideanSize_mul (x y : GoldenInt) :
  ...
```

The final Euclidean-domain instance also uses this theorem directly inside its `mul_left_not_lt` proof.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0226 `goldenEuclideanSize_mul`**:

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

Declaration 0225 establishes positivity of the measure on nonzero elements. Declaration 0226 then proves the multiplicative law

$$
\operatorname{size}(xy)=\operatorname{size}(x)\operatorname{size}(y),
$$

and together these facts support the measure laws and nondecrease-under-left-multiplication argument in the final `EuclideanDomain` instance.
# 0226 — `goldenEuclideanSize_mul`

## Lean type

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

This is a `theorem` stating that the natural-valued Euclidean size introduced in 0224 is multiplicative with respect to golden multiplication.

## Mathematical statement

Declaration 0224 defines

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N.
$$

By 0174 `goldenNorm_mul`, the golden norm satisfies

$$
N(xy)=N(x)N(y).
$$

Therefore multiplicativity of integer absolute value gives

$$
\operatorname{size}(xy)
=|N(xy)|
=|N(x)N(y)|
=|N(x)|\,|N(y)|
=\operatorname{size}(x)\operatorname{size}(y).
$$

The present theorem exposes this fact for the `Int.natAbs`-based Euclidean measure used by Lean.

## Role in the full proof

Declarations 0224–0226 form the Euclidean-measure block for `GoldenInt`.

- 0224 `goldenEuclideanSize` defines the natural-valued size `|N(x)|`.
- 0225 `goldenEuclideanSize_pos_of_ne_zero` proves positivity on nonzero elements.
- 0226 proves multiplicativity of that size.

These two properties are used directly in the final `EuclideanDomain GoldenInt` construction, whose relation is defined by

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
```

In particular, the `mul_left_not_lt` proof takes a nonzero `b`, obtains

$$
1\le\operatorname{size}(b)
$$

from 0225, and then uses the present theorem to derive

$$
\operatorname{size}(ab)
=\operatorname{size}(a)\operatorname{size}(b)
\ge\operatorname{size}(a).
$$

Thus left multiplication by a nonzero element cannot incorrectly decrease the Euclidean measure.

The later remainder argument also compares

$$
\operatorname{size}(r)<\operatorname{size}(y),
$$

so 0226 is the theorem ensuring that the chosen measure remains compatible with the multiplicative structure of the golden order.

## Direct dependencies

The direct dependencies are:

- 0224 `goldenEuclideanSize`
- 0174 `goldenNorm_mul`
- Mathlib's `Int.natAbs_mul`
- 0124 `goldenMul`

Conceptually,

$$
N(xy)=N(x)N(y)
\Longrightarrow
|N(xy)|=|N(x)|\,|N(y)|
\Longrightarrow
\operatorname{size}(xy)=\operatorname{size}(x)\operatorname{size}(y).
$$

The golden-order-specific algebraic content is already encapsulated in 0174; 0226 is a thin transport layer from the integer norm to the natural-valued Euclidean measure.

## Proof flow

The proof has two steps.

First,

```lean
change (goldenNorm (goldenMul x y)).natAbs =
  (goldenNorm x).natAbs * (goldenNorm y).natAbs
```

changes the goal to the definitional expansion of `goldenEuclideanSize`.

Then

```lean
rw [goldenNorm_mul, Int.natAbs_mul]
```

performs two rewrites:

1. `goldenNorm_mul` replaces the norm of the product by the product of norms.
2. `Int.natAbs_mul` distributes natural absolute value over the integer product.

Both sides then become identical.

## Lean-specific processing

The use of `change` is important. The visible goal is expressed through `goldenEuclideanSize`, but definitionally that term is `Int.natAbs (goldenNorm ...)`. The proof explicitly switches to the internal representation on which the two rewrite theorems apply directly.

This is more controlled than globally unfolding `goldenEuclideanSize` and keeps the intended proof boundary visible.

`Int.natAbs_mul` also absorbs all sign issues. The golden norm can be negative—for example `N(φ)=-1`—but the Euclidean measure discards the sign while retaining multiplicativity in `ℕ`.

## Redundancy and duplication

Mathematically, this theorem is essentially the direct composition of 0174 `goldenNorm_mul` with `Int.natAbs_mul`, so it contains little new golden arithmetic.

As an API theorem, however, it is useful. The final Euclidean-domain construction is written in terms of `goldenEuclideanSize`, not directly in terms of `goldenNorm`, so downstream code should not need to repeatedly unfold the measure and replay the transport from `ℤ` to `ℕ`.

Like 0225, this theorem cleanly absorbs the boundary between the signed integer norm layer and the natural-number Euclidean-measure layer.

## Optimization candidates

1. **Keep the current proof**
   - `change` plus `rw` is already short and makes the dependencies explicit.

2. **Try a `simpa`-oriented proof**
   - for example, derive the norm equality and normalize with `Int.natAbs_mul`;
   - this may not be shorter than the current proof, and exact elaboration is unverified because no Lean build is run here.

3. **Bundle `goldenEuclideanSize` as a multiplicative map**
   - if downstream code repeatedly uses multiplicativity, a `MonoidHom`-style interface could reduce bespoke lemmas.

4. **Abstract a generic norm-to-`natAbs` Euclidean measure helper**
   - this may be reusable for other quadratic integer rings with an integer-valued multiplicative norm.

The current theorem is already small and transparent, so local proof optimization is low priority.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface used by this theorem is mainly:

- `Int.natAbs_mul`
- definitional equality / `change`
- equality rewriting

Golden-specific declarations such as `goldenNorm_mul`, `goldenEuclideanSize`, and `goldenMul` are upstream in the same development.

The theorem itself should require far less than the whole of `Mathlib`, but the surrounding `GoldenEuclidean.lean` module also uses rational rounding, `field_simp`, `nlinarith`, well-founded measures, and Euclidean-domain typeclasses. Import minimization therefore needs to be measured at module scope. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. Natural comparison candidates are:

- A: current `change` + `rw`
- B: explicit `unfold goldenEuclideanSize` + simplification
- C: a `simpa`-centered proof
- D: bundle `goldenEuclideanSize` as a multiplicative map and use a generic `map_mul`

Useful metrics include proof-term size, visibility of definitional unfolding, reuse of Mathlib APIs, readability in the final Euclidean-domain instance, and generalizability.

The current approach makes the transition from the `ℤ`-valued norm to the `ℕ`-valued measure especially explicit and is therefore strong from an auditability perspective.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source order is:

```lean
theorem goldenEuclideanSize_pos_of_ne_zero ...

theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]

private theorem goldenRemainder_norm_rat_identity ...
```

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0227 `goldenRemainder_norm_rat_identity`**, which is a `private theorem`.

```lean
private theorem goldenRemainder_norm_rat_identity
    (x y : GoldenInt) (hy : y ≠ 0) :
    (goldenNorm (goldenRemainder x y) : ℚ) =
      (goldenNorm y : ℚ) *
        goldenRatNorm
          ((goldenQuotientCoords x y).1 - (goldenQuotient x y).fst,
           (goldenQuotientCoords x y).2 - (goldenQuotient x y).snd) := by
  ...
```

After 0224–0226 establish the basic Euclidean-size API, 0227 factors the remainder norm as

$$
N(r)=N(y)\,Q(\text{quotient rounding error}).
$$

This identity connects directly to the fundamental-cell estimate `|Q|<1` from 0214 and is the central bridge to the strict remainder-size decrease needed for the Euclidean-domain instance.
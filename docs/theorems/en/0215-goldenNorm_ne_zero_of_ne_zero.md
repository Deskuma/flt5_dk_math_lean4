# 0215 — `goldenNorm_ne_zero_of_ne_zero`

## Lean type

```lean
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  intro hn
  have hm : goldenMul y (goldenConj y) = 0 := by
    rw [golden_mul_conj, hn]
    rfl
  rcases mul_eq_zero.mp hm with hy0 | hc0
  · exact hy hy0
  · apply hy
    rw [← goldenConj_invol y, hc0]
    rfl
```

This is a `theorem` asserting that a nonzero golden integer cannot have zero norm.

## Mathematical statement

The statement is

$$
y\neq0\Longrightarrow N(y)\neq0.
$$

By 0176 `golden_mul_conj`, the golden order satisfies

$$
y\overline y=N(y)
$$

as an internal ring identity. If one assumes $N(y)=0$, then

$$
y\overline y=0.
$$

`GoldenInt` has already been registered as a domain by 0155, so zero-product elimination gives

$$
y=0\quad\text{or}\quad\overline y=0.
$$

The first branch contradicts `hy : y ≠ 0`. In the second branch, 0170 `goldenConj_invol` gives

$$
y=\overline{\overline y}=0,
$$

again contradicting `hy`. Therefore $N(y)\neq0$.

## Role in the full proof

In `GoldenEuclidean.lean`, declarations 0209–0214 establish that nearest-integer rounding places the quotient error in a region whose golden norm has absolute value strictly below `1`. The present theorem is the next structural prerequisite for Euclidean division: it certifies that the norm of a nonzero divisor can safely be used as a denominator.

The later definition

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

therefore relies on the fact that `y ≠ 0` implies `goldenNorm y ≠ 0`.

The theorem is also used directly downstream. In `goldenRemainder_norm_rat_identity` the source contains

```lean
have hn : (goldenNorm y : ℚ) ≠ 0 := by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

which supplies the nonzero denominator condition required by `field_simp`. It is also reused in `goldenEuclideanSize_pos_of_ne_zero`, together with `Int.natAbs_pos`, to prove positivity of the Euclidean size.

## Direct dependencies

The direct dependencies are:

- 0176 `golden_mul_conj`
- 0170 `goldenConj_invol`
- `goldenConj`
- `goldenMul`
- `goldenNorm`
- `mul_eq_zero`
- the `NoZeroDivisors` / `IsDomain GoldenInt` structure established by 0153–0155

Conceptually, the proof is

$$
N(y)=0
\Longrightarrow
y\overline y=0
\Longrightarrow
y=0\lor\overline y=0
\Longrightarrow
y=0,
$$

contradicting the hypothesis.

## Proof flow

### 1. Assume the norm vanishes

```lean
intro hn
```

The target `goldenNorm y ≠ 0` is opened as a negation, producing `hn : goldenNorm y = 0`.

### 2. Derive a zero product

```lean
have hm : goldenMul y (goldenConj y) = 0 := by
  rw [golden_mul_conj, hn]
  rfl
```

`golden_mul_conj` rewrites the product to `goldenOfInt (goldenNorm y)`. The hypothesis `hn` turns the norm into `0`, and `goldenOfInt 0 = 0` closes definitionally by `rfl`.

### 3. Split the zero product

```lean
rcases mul_eq_zero.mp hm with hy0 | hc0
```

The domain API yields two branches:

- `hy0 : y = 0`
- `hc0 : goldenConj y = 0`

### 4. Contradict `hy` in both branches

The first branch is immediate:

```lean
exact hy hy0
```

In the conjugate-zero branch, involutivity recovers the original element:

```lean
apply hy
rw [← goldenConj_invol y, hc0]
rfl
```

Thus `goldenConj y = 0` also implies `y = 0`.

## Lean-specific processing

`mul_eq_zero.mp hm` uses the already registered zero-divisor-free algebra structure on `GoldenInt` through typeclass inference. The proof therefore does not expand coordinates or solve the quadratic equation $a^2+ab-b^2=0$ directly.

In the second branch,

```lean
rw [← goldenConj_invol y, hc0]
```

uses involutivity in reverse, replacing `y` by `goldenConj (goldenConj y)`. The inner conjugate is then rewritten to zero using `hc0`, and `goldenConj 0 = 0` closes definitionally.

This is a structural proof built from the ring and conjugation APIs already established upstream; it requires neither `ring` nor `norm_num`.

## Redundancy and duplication

Mathematically, the fact that norm zero implies element zero is almost automatic from `golden_mul_conj` plus the domain structure, so there is room for a more generic abstraction.

The second branch explicitly uses `goldenConj_invol` to recover `y`. If conjugation were bundled as a `RingEquiv`, injectivity could likely replace this explicit involution rewrite.

Nevertheless, keeping this as a named theorem is valuable. The Euclidean quotient code needs exactly the consumer-facing fact that the denominator `goldenNorm y` is nonzero, and repeating the zero-product argument at each use site would obscure that intent.

## Optimization candidates

1. **Bundle conjugation as a `RingEquiv`**
   - injectivity could simplify the conjugate-zero branch.

2. **Introduce a general norm-zero helper**
   - if the relation `x * conj x = algebraMap (N x)` is abstracted, one could package `N x = 0 ↔ x = 0` more generally.

3. **Expose an iff theorem**
   - `goldenNorm y = 0 ↔ y = 0` could improve rewrite usability downstream.

4. **Keep the current theorem as the quotient-facing API**
   - the existing proof is already short and states exactly the denominator-safety property required later.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present theorem directly needs only a relatively small surface:

- zero-product reasoning via `mul_eq_zero`
- equality rewriting
- the `IsDomain` / `NoZeroDivisors` instance on `GoldenInt`
- upstream conjugation and norm theorems

It does not itself use `ring`, `nlinarith`, `norm_num`, or `round`. The surrounding `GoldenEuclidean.lean` module does use those facilities extensively, so the true minimal import set should be evaluated at module scope rather than from 0215 in isolation.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current `golden_mul_conj` + `mul_eq_zero` + involution proof
- B: direct coordinate proof from $a^2+ab-b^2=0$
- C: bundle `goldenConj` as a `RingEquiv` and use injectivity
- D: first prove a general theorem `goldenNorm y = 0 ↔ y = 0`
- E: abstract the argument through a generic norm-like structure on a domain

Useful comparison axes are proof size, coordinate dependence, reuse of Mathlib algebra APIs, mathematical provenance, and downstream quotient ergonomics.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0214 `goldenRat_norm_abs_lt_one`, followed by `goldenQuotientNumerator`. It is later used directly by `goldenEuclideanSize_pos_of_ne_zero` and `goldenRemainder_norm_rat_identity`.

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0216 `goldenQuotientNumerator`**:

```lean
/-- Numerator coordinates of `x * conjugate(y)`. -/
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

Now that 0215 guarantees a nonzero norm for every nonzero divisor, the development begins implementing the rational quotient

$$
\frac{x\overline y}{N(y)}.
$$

Declaration 0216 first names the numerator `x * conjugate(y)` as a concrete `GoldenInt`; the following declarations then expose its coordinates and divide them by `goldenNorm y` to obtain `goldenQuotientCoords`.

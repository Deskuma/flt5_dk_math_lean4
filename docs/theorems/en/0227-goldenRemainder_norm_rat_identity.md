# 0227 — `goldenRemainder_norm_rat_identity`

## Lean type

```lean
private theorem goldenRemainder_norm_rat_identity
    (x y : GoldenInt) (hy : y ≠ 0) :
    (goldenNorm (goldenRemainder x y) : ℚ) =
      (goldenNorm y : ℚ) *
        goldenRatNorm
          ((goldenQuotientCoords x y).1 - (goldenQuotient x y).fst,
           (goldenQuotientCoords x y).2 - (goldenQuotient x y).snd) := by
  have hn : (goldenNorm y : ℚ) ≠ 0 := by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
  have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd - y.snd ^ 2 ≠ 0 := by
    simpa [goldenNorm] using hn
  let A : ℚ := (goldenQuotientCoords x y).1
  let B : ℚ := (goldenQuotientCoords x y).2
  let m : ℤ := (goldenQuotient x y).fst
  let n : ℤ := (goldenQuotient x y).snd
  have hx1 : (x.fst : ℚ) = y.fst * A + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hx2 : (x.snd : ℚ) =
      y.snd * A + y.fst * B + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hr1 : ((goldenRemainder x y).fst : ℚ) =
      y.fst * (A - m) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_fst_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx1]
    ring
  have hr2 : ((goldenRemainder x y).snd : ℚ) =
      y.snd * (A - m) + y.fst * (B - n) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_snd_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx2]
    ring
  dsimp only [goldenNorm, goldenRatNorm]
  push_cast
  change _ = _ *
    ((A - (m : ℚ)) ^ 2 + (A - (m : ℚ)) * (B - (n : ℚ)) -
      (B - (n : ℚ)) ^ 2)
  rw [hr1, hr2]
  ring
```

This is a `private theorem`. It is not exposed as a public API result; instead, it serves as an internal bridge inside `GoldenEuclidean.lean` for proving strict norm decrease of the concrete remainder.

## Mathematical statement

Let the rational coordinates of `x / y` be

$$
(A,B)=\mathrm{goldenQuotientCoords}(x,y),
$$

and let the coordinatewise nearest integers be

$$
m=\operatorname{round}(A),\qquad n=\operatorname{round}(B).
$$

Declaration 0220 `goldenQuotient` chooses this pair $(m,n)$ as the golden-integer quotient, and 0221 `goldenRemainder` defines

$$
r=x-qy.
$$

The present theorem proves the exact factorization

$$
N(r)=N(y)\,Q(A-m,B-n),
$$

where

$$
Q(u,v)=u^2+uv-v^2
$$

is the rational golden norm polynomial from 0210 `goldenRatNorm`.

Thus the size of the remainder splits exactly into the divisor norm and the norm of the quotient rounding error.

This identity allows the fundamental-cell estimate from 0214,

$$
|Q(u,v)|<1,
$$

to be multiplied directly by the divisor norm in order to obtain

$$
|N(r)|<|N(y)|.
$$

The theorem is therefore the central algebraic bridge between nearest-integer rounding and Euclidean norm decrease.

## Role in the full proof

Declarations 0220–0227 form the quotient/remainder construction block for Euclidean division in the golden order.

- 0220 `goldenQuotient` rounds the rational quotient coordinates to the nearest lattice point.
- 0221 `goldenRemainder` defines $r=x-qy$.
- 0222 `goldenQuotient_zero` fixes the total quotient behavior when the divisor is zero.
- 0223 `golden_quotient_mul_add_remainder` proves $yq+r=x$.
- 0224–0226 define the Euclidean size $|N(x)|$ and prove positivity and multiplicativity.
- 0227, the present theorem, factors the remainder norm into the divisor norm times the rounding-error norm.

The immediately following theorem `golden_remainder_size_lt` uses this result directly via

```lean
have hid := goldenRemainder_norm_rat_identity x y hy
```

It combines the nearest-integer bounds on `A-round A` and `B-round B` with 0214 to obtain

$$
|Q(A-m,B-n)|<1,
$$

and then uses the present identity together with `abs_mul` to derive strict contraction.

For this reason, 0227 is one of the most important internal identities in `GoldenEuclidean.lean`. It is not merely a local coordinate calculation; it is the algebraic core connecting the rounding geometry to the Euclidean-domain construction.

## Direct dependencies

The main direct dependencies are:

- 0215 `goldenNorm_ne_zero_of_ne_zero`
- 0217 `goldenQuotientNumerator_fst`
- 0218 `goldenQuotientNumerator_snd`
- 0219 `goldenQuotientCoords`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0210 `goldenRatNorm`
- `goldenNorm`
- `goldenMul`
- `golden_fst_sub`
- `golden_snd_sub`
- `field_simp`
- `exact_mod_cast`
- `push_cast`
- `ring`

Conceptually, the dependency chain is

$$
y\neq0
\Longrightarrow N(y)\neq0
\Longrightarrow
\frac{x\overline y}{N(y)}=(A,B)
\Longrightarrow
r=y\cdot(A-m,B-n)
\Longrightarrow
N(r)=N(y)Q(A-m,B-n).
$$

## Proof flow

### 1. Establish that the denominator `N(y)` is nonzero

```lean
have hn : (goldenNorm y : ℚ) ≠ 0 := by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

The integer nonvanishing theorem from 0215 is transported to `ℚ`.

Then

```lean
have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd - y.snd ^ 2 ≠ 0 := by
  simpa [goldenNorm] using hn
```

rewrites the same fact into the expanded denominator form needed later by `field_simp`.

### 2. Introduce short names for quotient coordinates and rounded integers

```lean
let A : ℚ := (goldenQuotientCoords x y).1
let B : ℚ := (goldenQuotientCoords x y).2
let m : ℤ := (goldenQuotient x y).fst
let n : ℤ := (goldenQuotient x y).snd
```

This cleanly separates the continuous rational coordinates $(A,B)$ from the discrete rounded coordinates $(m,n)$.

### 3. Reconstruct `x` as `y*(A,B)` coordinatewise

The proof establishes

```lean
have hx1 : (x.fst : ℚ) = y.fst * A + y.snd * B := by
  ...
```

and

```lean
have hx2 : (x.snd : ℚ) =
    y.snd * A + y.fst * B + y.snd * B := by
  ...
```

Using 0217 and 0218, the rationalized numerator coordinates are expanded. `field_simp [hn']` clears the common denominator `N(y)`, and `ring` closes the resulting polynomial identities.

These are the coordinate form of the rational quotient identity

$$
x=y(A+B\varphi).
$$

### 4. Express the remainder coordinates through the rounding error

After unfolding 0221's definition $r=x-qy$ and substituting `hx1` and `hx2`, the proof obtains

$$
r_1=y_1(A-m)+y_2(B-n)
$$

and

$$
r_2=y_2(A-m)+y_1(B-n)+y_2(B-n).
$$

These are the statements named `hr1` and `hr2` in Lean.

### 5. Expand both norms and close the final ring identity

Finally `goldenNorm` and `goldenRatNorm` are unfolded, integer casts are pushed through, and the target is changed into

$$
N(r)=N(y)\left((A-m)^2+(A-m)(B-n)-(B-n)^2\right).
$$

After rewriting with `hr1` and `hr2`, the goal is a pure commutative-ring polynomial identity and is closed by `ring`.

## Lean-specific processing

This proof contains a substantial amount of coercion management.

The coordinates of `GoldenInt` live in `ℤ`, whereas quotient coordinates live in `ℚ`. Consequently, the same algebraic expressions cross the integer/rational boundary repeatedly. `exact_mod_cast`, `push_cast`, `Int.cast_sub`, `Int.cast_add`, and `Int.cast_mul` are used to keep those transitions explicit and type-correct.

`field_simp [hn']` removes the denominator `N(y)`, and therefore depends crucially on the nonzero certificate inherited from 0215. Thus 0215 is not merely an abstract domain lemma: here it becomes the concrete denominator certificate required by rational quotient algebra.

The local names `A`, `B`, `m`, and `n` are also important proof-engineering choices. Without them, the long terms involving `goldenQuotientCoords` and `goldenQuotient` would be repeatedly expanded, making the polynomial normalization considerably harder to read.

## Redundancy and duplication

The pairs `hx1` / `hx2` and `hr1` / `hr2` are structurally parallel coordinate proofs, so there is visible duplication.

Mathematically, one would naturally prefer to state a single reconstruction identity

$$
x=y(A+B\varphi)
$$

and then a single remainder factorization

$$
r=y\cdot((A-m)+(B-n)\varphi).
$$

If `GoldenRat` had a richer algebraic structure or a scalar-extension interpretation, these paired coordinate lemmas could potentially be replaced by one structural equality each.

The current implementation deliberately avoids introducing that additional infrastructure. It keeps all dependencies explicit and closes the argument in coordinates, trading some repetition for a shallower abstraction stack.

## Optimization candidates

1. **Bundle rationalized multiplication on `GoldenRat`**
   - define golden multiplication over rational coordinates and express `x = y * quotientCoords` as one equality.

2. **Extract a quotient reconstruction theorem first**
   - package `hx1` and `hx2` into a named result and let 0227 focus only on the rounding error.

3. **Introduce a remainder factorization theorem**
   - prove a structural `r = y * error` statement at rational-coordinate level and derive 0227 from norm multiplicativity.

4. **Keep the current coordinate proof**
   - avoid new scalar-extension infrastructure and preserve an explicit `field_simp + ring` certificate.

5. **Compare against a true `ℚ[φ]` representation**
   - evaluate whether an algebraic extension representation shortens the Euclidean proof enough to justify the extra abstraction.

The current proof is long, but all transformations are explicit and the final obligation is visibly reduced to polynomial algebra.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The Mathlib surface directly involved in this theorem includes at least:

- `exact_mod_cast`
- `field_simp`
- `push_cast`
- `ring`
- rational/integer coercions
- ordinary local definitions and rewriting

The surrounding `GoldenEuclidean.lean` module additionally uses `round`, `abs_sub_round`, `nlinarith`, well-founded measures, and the `EuclideanDomain` typeclass. Import minimization should therefore be measured at module scope rather than theorem scope.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

This theorem is especially suitable for a Comparator challenge. Natural implementations include:

- A: the current explicit coordinate proof
- B: equip `GoldenRat` with multiplication and prove `r=y*error` structurally
- C: lift the argument into a quadratic algebra / `AdjoinRoot` representation and use norm multiplicativity
- D: bundle quotient reconstruction and norm factorization into one reusable abstraction

Useful metrics include proof length, number of coercion operations, reliance on `field_simp`, visibility of the underlying mathematics, generalizability, and the resulting simplicity of `golden_remainder_size_lt`.

Approach A is longer but highly explicit; B and C may be shorter but introduce additional abstraction layers. This is a meaningful design trade-off for the whole `GoldenEuclidean` block.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms that this `private theorem` appears immediately after 0226 `goldenEuclideanSize_mul` and immediately before the public theorem `golden_remainder_size_lt`.

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. Because this theorem is a private internal proof and no exact matching PDF page or section was identified in this pass, no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0228 `golden_remainder_size_lt`**:

```lean
theorem golden_remainder_size_lt (x : GoldenInt) {y : GoldenInt} (hy : y ≠ 0) :
    goldenEuclideanSize (goldenRemainder x y) < goldenEuclideanSize y := by
  ...
```

Now that 0227 provides

$$
N(r)=N(y)Q(\text{rounding error}),
$$

0228 applies the rounding bounds and the 0214 estimate $|Q|<1$ to derive

$$
|N(r)|<|N(y)|
$$

as a strict inequality of natural-valued Euclidean sizes.

This is the actual decrease condition required by the Euclidean algorithm.
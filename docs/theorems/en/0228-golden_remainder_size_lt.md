# 0228 — `golden_remainder_size_lt`

## Lean type

```lean
theorem golden_remainder_size_lt (x : GoldenInt) {y : GoldenInt} (hy : y ≠ 0) :
    goldenEuclideanSize (goldenRemainder x y) < goldenEuclideanSize y := by
  let A := (goldenQuotientCoords x y).1
  let B := (goldenQuotientCoords x y).2
  have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
  have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
  have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
    simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
  have hnpos : 0 < |(goldenNorm y : ℚ)| := abs_pos.mpr (by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy)
  have hid := goldenRemainder_norm_rat_identity x y hy
  have hrat : |(goldenNorm (goldenRemainder x y) : ℚ)| <
      |(goldenNorm y : ℚ)| := by
    rw [hid, abs_mul]
    have := mul_lt_mul_of_pos_left hcell hnpos
    simpa [A, B, goldenQuotient] using this
  have hInt : |goldenNorm (goldenRemainder x y)| < |goldenNorm y| := by
    exact_mod_cast hrat
  change (goldenNorm (goldenRemainder x y)).natAbs <
    (goldenNorm y).natAbs
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hInt
  exact_mod_cast hInt
```

This is a `theorem`. For a nonzero divisor `y`, it proves that the nearest-lattice remainder constructed by 0220 `goldenQuotient` and 0221 `goldenRemainder` is strictly smaller than `y` with respect to 0224 `goldenEuclideanSize`.

## Mathematical statement

The statement is

$$
y\neq0
\Longrightarrow
\operatorname{size}(r)<\operatorname{size}(y),
$$

where

$$
r=x-qy,
\qquad
\operatorname{size}(z)=|N(z)|_{\mathbb N}.
$$

The quotient `q = goldenQuotient x y` is obtained by taking the golden-basis coordinates of the rationalized quotient

$$
\frac{x}{y}
=
\frac{x\overline y}{N(y)}
$$

and rounding both coordinates to the nearest integers. If the exact rational coordinates are

$$
A=(goldenQuotientCoords\ x\ y)_1,
\qquad
B=(goldenQuotientCoords\ x\ y)_2,
$$

then nearest-integer rounding gives

$$
|A-\operatorname{round}(A)|\le\frac12,
\qquad
|B-\operatorname{round}(B)|\le\frac12.
$$

Declaration 0227 `goldenRemainder_norm_rat_identity` factors the norm of the remainder as

$$
N(r)
=
N(y)\,
Q(A-m,B-n),
$$

where

$$
Q(u,v)=u^2+uv-v^2,
\qquad
m=\operatorname{round}(A),
\qquad
n=\operatorname{round}(B).
$$

By 0214 `goldenRat_norm_abs_lt_one`, the rounding cell satisfies

$$
|Q(A-m,B-n)|<1.
$$

Since `y ≠ 0` implies $|N(y)|>0$, multiplication by the positive factor $|N(y)|$ preserves strict inequality, so

$$
|N(r)|
=
|N(y)|\,|Q(A-m,B-n)|
<
|N(y)|.
$$

Converting integer absolute values to `Int.natAbs` yields

$$
goldenEuclideanSize(r)
<
goldenEuclideanSize(y).
$$

## Role in the full proof

This is the **strict-decrease theorem itself** in the construction of the norm-Euclidean structure on `GoldenInt`.

The preceding declarations prepare the ingredients in dependency order:

- 0209 `GoldenRat` — rational golden-basis coordinates.
- 0210 `goldenRatNorm` — the golden norm quadratic form on rational coordinates.
- 0211–0212 — nearest-integer rounding bounds of `1/2` in each coordinate.
- 0213 — the sharp fundamental-cell estimate `5/16`.
- 0214 — conversion of that estimate into the consumer-facing bound `< 1`.
- 0215 — nonzero `y` implies `N(y) ≠ 0`.
- 0216–0219 — construction of the rationalized quotient coordinates.
- 0220 — rounding the rational quotient to a golden integer.
- 0221 — defining the remainder `r = x - qy`.
- 0224 — defining the Euclidean size `natAbs (goldenNorm x)`.
- 0227 — the exact identity `N(r)=N(y)Q(error)`.

Declaration 0228 combines those ingredients and produces the actual decrease condition

$$
size(r)<size(y).
$$

The immediately following `exists_golden_quotient_remainder` packages the quotient and remainder witnesses, and the later `goldenEuclideanDomain` instance installs this theorem directly as

```lean
remainder_lt := golden_remainder_size_lt
```

in the `EuclideanDomain` structure.

Thus 0228 is the central certificate that upgrades the explicit golden order from an integral domain to a Euclidean domain.

## Direct dependencies

The main direct dependencies are:

- 0214 `goldenRat_norm_abs_lt_one`
- 0215 `goldenNorm_ne_zero_of_ne_zero`
- 0219 `goldenQuotientCoords`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0224 `goldenEuclideanSize`
- 0227 `goldenRemainder_norm_rat_identity`
- `goldenRatNorm`
- Mathlib `round`
- Mathlib `abs_sub_round`
- Mathlib `abs_pos`
- Mathlib `abs_mul`
- `mul_lt_mul_of_pos_left`
- `exact_mod_cast`
- `Int.abs_eq_natAbs`

Conceptually,

$$
y\neq0
\Longrightarrow |N(y)|>0,
$$

$$
|error_i|\le\frac12
\Longrightarrow |Q(error)|<1,
$$

and

$$
N(r)=N(y)Q(error)
\Longrightarrow |N(r)|<|N(y)|
\Longrightarrow size(r)<size(y).
$$

## Proof flow

### 1. Name the rational quotient coordinates

```lean
let A := (goldenQuotientCoords x y).1
let B := (goldenQuotientCoords x y).2
```

The local names separate the continuous rational quotient coordinates from the longer projection expressions used in their definition.

### 2. Obtain nearest-integer rounding bounds

```lean
have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
```

Mathlib's `abs_sub_round` places both coordinate errors inside the square fundamental cell.

### 3. Prove that the golden norm of the error is strictly below one

```lean
have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
  simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
```

Declaration 0214 states the quadratic form explicitly, while the present proof wants the bundled `goldenRatNorm` form. `simpa [goldenRatNorm]` bridges those presentations.

### 4. Show that the divisor norm has positive absolute value

```lean
have hnpos : 0 < |(goldenNorm y : ℚ)| := abs_pos.mpr (by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy)
```

The integer nonzero theorem from 0215 is cast to `ℚ`, then `abs_pos.mpr` converts nonzeroness to strict positivity.

This positivity is essential because the proof will multiply the cell inequality by $|N(y)|$.

### 5. Import the exact remainder norm identity

```lean
have hid := goldenRemainder_norm_rat_identity x y hy
```

This supplies

$$
N(r)=N(y)Q(error).
$$

### 6. Prove strict contraction over `ℚ`

```lean
have hrat : |(goldenNorm (goldenRemainder x y) : ℚ)| <
    |(goldenNorm y : ℚ)| := by
  rw [hid, abs_mul]
  have := mul_lt_mul_of_pos_left hcell hnpos
  simpa [A, B, goldenQuotient] using this
```

After rewriting by `hid` and `abs_mul`, the left side becomes

$$
|N(y)|\,|Q(error)|.
$$

`mul_lt_mul_of_pos_left hcell hnpos` turns $|Q(error)|<1$ into

$$
|N(y)|\,|Q(error)|<|N(y)|.
$$

The final `simpa` unfolds the local coordinate names and identifies `round A`, `round B` with the coordinates of `goldenQuotient`.

### 7. Return from rational to integer absolute values

```lean
have hInt : |goldenNorm (goldenRemainder x y)| < |goldenNorm y| := by
  exact_mod_cast hrat
```

The rational inequality is transported back to `ℤ`.

### 8. Convert the integer inequality to the natural Euclidean measure

```lean
change (goldenNorm (goldenRemainder x y)).natAbs <
  (goldenNorm y).natAbs
rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hInt
exact_mod_cast hInt
```

After unfolding the target measure, `Int.abs_eq_natAbs` connects integer absolute value with natural absolute value, and the last cast closes the required natural-number comparison.

## Lean-specific processing

This theorem is notable for its movement through three numeric layers: `ℤ`, `ℚ`, and `ℕ`.

- `exact_mod_cast` moves the nonzero norm and later the strict inequality between integer and rational presentations.
- `abs_pos.mpr` converts nonzeroness into positive absolute value.
- `simpa [A, B, goldenQuotient]` eliminates the local `let` bindings and matches the explicit rounded coordinates with the quotient definition.
- `Int.abs_eq_natAbs` is the bridge from the signed integer norm to the natural Euclidean measure.
- the final `exact_mod_cast` reconciles the remaining integer/natural representation difference.

Another design point is that 0227 is `private`. The long exact algebraic norm identity remains internal, while 0228 exposes only the mathematically meaningful public interface: the remainder measure strictly decreases.

## Redundancy and duplication

The proof contains visible coercion overhead.

The steps

```lean
exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

and

```lean
exact_mod_cast hrat
```

followed by `Int.abs_eq_natAbs` and another cast arise because:

- `goldenNorm` lives in `ℤ`;
- the exact quotient/remainder identity is most convenient over `ℚ`;
- the well-founded Euclidean measure lives in `ℕ`.

Mathematically these several Lean steps express the single inequality

$$
|N(r)|=|N(y)|\,|Q(error)|<|N(y)|.
$$

There is also a small conceptual overlap with 0212 `exists_goldenRat_near_int`: both concern the `1/2` nearest-integer bound. Here, however, the quotient construction has already chosen the canonical witnesses `round A` and `round B`, so directly using `abs_sub_round` is simpler than unpacking an existential theorem.

## Optimization candidates

1. **Provide a `goldenRatNorm`-shaped contraction theorem directly**
   - If 0214 stated `|goldenRatNorm (u,v)| < 1`, the `simpa [goldenRatNorm]` bridge would disappear.

2. **Bundle the rounded quotient error**
   - A definition such as `goldenQuotientError x y` for `(A-round A, B-round B)` could shorten both 0227 and 0228.

3. **Introduce an absolute-norm comparison helper**
   - A reusable helper could hide most `ℚ → ℤ → ℕ` coercion boilerplate.

4. **Expose a comparison lemma for `goldenEuclideanSize`**
   - A suitable equivalence between `goldenEuclideanSize a < goldenEuclideanSize b` and the corresponding absolute norm inequality could simplify the final block.

5. **Keep the current public/private split**
   - The separation between the private exact identity 0227 and the public strict-decrease theorem 0228 is already strong design. Most worthwhile optimization would therefore target representation plumbing rather than the mathematical decomposition.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present theorem directly touches at least:

- `round`
- `abs_sub_round`
- `abs_pos`
- `abs_mul`
- `mul_lt_mul_of_pos_left`
- `exact_mod_cast`
- `Int.abs_eq_natAbs`
- coercions among rationals, integers, and naturals

Its dependencies widen the module-level surface: 0214 uses `linarith` / `norm_num`, while 0227 uses `field_simp`, `push_cast`, and `ring`.

No Lean build is performed in this museum pass, so the exact minimal import set is unverified. Import reduction is therefore recorded only as an optimization candidate.

## Comparator challenge suitability

This theorem is an excellent Comparator challenge for Euclidean-domain proof engineering.

Possible variants include:

- A: the current `ℚ` identity → strict inequality → `ℤ` → `ℕ` cast chain;
- B: introduce absolute-norm comparison helpers that hide the coercion boilerplate;
- C: model `GoldenRat` as a structured quadratic algebra and use generic norm APIs;
- D: bundle quotient error together with its contraction certificate;
- E: formulate the Euclidean relation first in terms of integer absolute norms, then transport it once to a natural well-founded measure.

Useful metrics include proof length, number of casts, tactic dependence, visibility of the mathematical mechanism, ease of connecting to `EuclideanDomain`, and reuse for other quadratic orders.

The comparison between A and B is especially valuable: it tests how much Lean-specific coercion noise can be removed without hiding the explicit mathematics.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source places this theorem immediately after 0227 `goldenRemainder_norm_rat_identity`, followed by

```lean
theorem exists_golden_quotient_remainder ...
```

and then by

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  ...
  remainder_lt := golden_remainder_size_lt
  ...
```

The exact Japanese/English PDF page or section corresponding to this implementation theorem was not identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is **0229 `exists_golden_quotient_remainder`**:

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

Now that 0228 has completed the Euclidean decrease condition, 0229 packages the explicit quotient and remainder into one existential Euclidean-division statement.

The declaration after that is the `goldenEuclideanDomain : EuclideanDomain GoldenInt` instance itself, where 0228 is installed directly as the `remainder_lt` field.
# 0205 — `goldenUnit_neg`

## Lean type

```lean
theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

This is a `theorem` stating that if a golden integer `x` satisfies `GoldenUnit`, then its additive inverse `-x` also satisfies `GoldenUnit`.

## Mathematical statement and meaning of the declaration

The statement is

$$
GoldenUnit(x)\Longrightarrow GoldenUnit(-x).
$$

In any ring, negating a unit again gives a unit: if `y` is an inverse of `x`, then `-y` is an inverse of `-x`, since

$$
(-x)(-y)=xy=1.
$$

The present proof does not construct that inverse witness directly. Instead, it routes through the norm criterion established in declarations 0198–0202.

The golden norm is the quadratic form

$$
N(a+b\varphi)=a^2+ab-b^2,
$$

so

$$
N(-x)=N(x).
$$

By 0202 `goldenNorm_eq_one_or_neg_one_of_unit`, unitness of `x` implies `N(x)=\pm1`. Hence `N(-x)=\pm1`, and 0201 `goldenUnit_of_norm_eq_one_or_neg_one` converts that norm condition back into `GoldenUnit (-x)`.

## Role in the full proof

Declarations 0198–0204 establish the custom unit predicate, the norm `±1` criterion, and concrete unit certificates for `φ` and `1`. Declaration 0205 begins the closure block for `GoldenUnit` under ordinary ring operations.

In source order it is immediately followed by:

- 0206 `goldenUnit_mul`
- 0207 `goldenUnit_pow`

Thus 0205–0207 establish the pattern

$$
\text{unit}\xrightarrow{-}\text{unit},\qquad
\text{unit}\cdot\text{unit}\to\text{unit},\qquad
\text{unit}^n\to\text{unit}.
$$

These closure properties support later manipulations of units together with fifth powers and unit-class representatives. Although 0205 is not itself used in the induction for `goldenUnit_pow`, it completes the expected elementary closure surface of the custom unit API.

## Direct dependencies

The current proof directly depends on:

- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- 0202 `goldenNorm_eq_one_or_neg_one_of_unit`
- 0164 `goldenNorm`
- the `Neg GoldenInt` instance and its coordinate simp rules
- `simp`

Conceptually, the dependency chain is

$$
GoldenUnit(x)
\Longrightarrow N(x)=\pm1
\Longrightarrow N(-x)=N(x)=\pm1
\Longrightarrow GoldenUnit(-x).
$$

The equality `N(-x)=N(x)` is not imported through a named theorem; it is proved locally inside the rewrite.

## Proof flow

The proof has three steps.

### 1. Move the unit goal to the norm criterion

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
```

This changes the goal

```lean
GoldenUnit (-x)
```

into

```lean
goldenNorm (-x) = 1 ∨ goldenNorm (-x) = -1.
```

### 2. Rewrite norm invariance under negation

```lean
rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
```

The inline equality proves

$$
N(-x)=N(x),
$$

reducing the target to

```lean
goldenNorm x = 1 ∨ goldenNorm x = -1.
```

### 3. Project the unit hypothesis to norm `±1`

```lean
exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

Declaration 0202 closes the remaining goal directly.

## Lean-specific processing

The distinctive Lean feature is the inline theorem used as a rewrite rule:

```lean
rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
```

The `show ... by ...` expression constructs exactly the equality needed by `rw` without introducing a separate named lemma. This keeps norm invariance under negation local to 0205.

`simp [goldenNorm]` uses the existing projection simp rules for negation, such as `(-x).fst = -x.fst` and `(-x).snd = -x.snd`, together with integer sign simplification. Since the norm is quadratic, all signs cancel.

The surrounding use of 0201 and 0202 also shows that those two declarations are already functioning as the two directions of one bidirectional unit criterion, even though no explicit iff theorem has yet been packaged.

## Redundancy and duplication

The mathematical content is standard for units in a ring. Once `GoldenUnit` is connected to Mathlib's `IsUnit`, a dedicated golden-specific proof of closure under negation may become unnecessary.

Indeed, a later module contains a bridge of the form

```lean
theorem goldenUnit_iff_isUnit {x : GoldenInt} : GoldenUnit x ↔ IsUnit x := by
  ...
```

so a future refactor could delegate this closure fact to the generic `IsUnit` API.

The equality `N(-x)=N(x)` is also proved inline. If the same fact appears repeatedly, a reusable theorem such as

```lean
@[simp] theorem goldenNorm_neg (x : GoldenInt) :
    goldenNorm (-x) = goldenNorm x := by
  simp [goldenNorm]
```

would remove duplicated local calculations.

Finally, 0201 and 0202 together already encode

$$
GoldenUnit(x)\iff N(x)=\pm1.
$$

Publishing that equivalence explicitly could shorten this and several later unit arguments.

## Optimization candidates

1. **Construct the inverse witness directly**
   - destruct `hx`, then use `-y` as the inverse of `-x`;
   - avoids the round trip through the norm criterion.

2. **Publish `goldenNorm_neg` as a simp theorem**
   - turns the local quadratic-form calculation into reusable API.

3. **Package the unit criterion as an iff theorem**
   - expose `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` for rewriting and simp.

4. **Integrate `GoldenUnit` with `IsUnit`**
   - generic Mathlib unit-closure theorems could replace custom proofs.

5. **Keep the current proof**
   - it is already short and clearly demonstrates the practical value of the norm criterion developed immediately beforehand.

The largest optimization opportunity is therefore structural API consolidation rather than local proof compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is small, mainly:

- `simp`
- equality rewriting
- elementary simp rules for negation in a ring

The unit-criterion results and the golden norm are local upstream declarations.

The theorem alone should require much less than all of `Mathlib`, but the surrounding `GoldenDivisibility.lean` module also uses integer divisibility, `Int.eq_one_or_neg_one_of_mul_eq_one`, `norm_num`, and ring arithmetic. Import minimization should therefore be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: the current proof through the norm criterion
- B: direct transformation of an inverse witness `y` into `-y`
- C: `goldenNorm_neg` plus an explicit unit-criterion iff
- D: the `GoldenUnit ↔ IsUnit` bridge plus generic Mathlib unit API
- E: a more abstract design bundling conjugation and norm

Useful comparison axes are proof size, direct dependency depth, reuse of standard Mathlib APIs, visibility of mathematical provenance, dependence on the coordinate layer, and refactor robustness.

The contrast between A and B is especially clean: A treats norm `±1` as the central unit interface, while B works directly with the existential inverse witness.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source directly confirms the sequence

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]

theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx

theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  ...
```

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified directly in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0206 `goldenUnit_mul`**:

```lean
theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [goldenNorm_mul]
  rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
    rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
    simp [hx', hy']
```

Where 0205 proves closure under negation, 0206 proves closure under multiplication by reducing the two unit hypotheses to the four sign combinations of norm `±1`. Declaration 0207 `goldenUnit_pow` then uses 0204 and 0206 to complete closure under natural powers.
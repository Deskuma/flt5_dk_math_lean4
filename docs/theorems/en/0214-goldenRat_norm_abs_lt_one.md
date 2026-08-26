# 0214 — `goldenRat_norm_abs_lt_one`

## Lean type

```lean
theorem goldenRat_norm_abs_lt_one
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| < 1 := by
  have h := goldenRat_norm_abs_le_five_sixteen hu hv
  norm_num at h ⊢
  linarith
```

This is a `theorem` proving that on the square fundamental cell produced by nearest-integer rounding,

$$
|u|\le\frac12,\qquad |v|\le\frac12,
$$

the golden norm quadratic form

$$
Q(u,v)=u^2+uv-v^2
$$

has absolute value strictly less than `1`.

## Mathematical statement

Declaration 0213 `goldenRat_norm_abs_le_five_sixteen` already proves the sharp uniform estimate

$$
|Q(u,v)|\le\frac5{16}
$$

under the same assumptions.

The present theorem performs no new quadratic-form estimate. It simply combines the previous bound with

$$
\frac5{16}<1
$$

to obtain

$$
|Q(u,v)|<1.
$$

Mathematically, it is the one-line transitivity step

$$
|Q(u,v)|\le\frac5{16}<1.
$$

The threshold `1`, however, is exactly the quantity required by the Euclidean-division argument. The remainder norm is later expressed as the divisor norm multiplied by the norm of the rounding error; strict inequality below `1` then forces a strict decrease in absolute norm.

## Role in the full proof

Inside `GoldenEuclidean.lean`, 0214 is the **boundary theorem from a quantitative estimate to Euclidean contraction**.

The upstream sequence is:

1. 0209 `GoldenRat` introduces rational quotient coordinates.
2. 0210 `goldenRatNorm` extends the golden norm quadratic form to `ℚ²`.
3. 0211–0212 round each coordinate to a nearest integer and place the error inside `[-1/2,1/2]^2`.
4. 0213 proves the sharp cell bound `5/16`.
5. **0214 converts `5/16 < 1` into the strict contraction statement needed downstream.**

The later theorem `golden_remainder_size_lt` uses 0214 directly:

```lean
have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
  simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
```

Then `goldenRemainder_norm_rat_identity` gives the factorization

$$
N(r)=N(y)\,Q(\text{rounding error}),
$$

and `|Q|<1` yields

$$
|N(r)|<|N(y)|.
$$

Thus 0213 supplies the sharp geometric estimate, while 0214 exposes the consumer-facing strict inequality required by the Euclidean-domain construction.

## Direct dependencies

The direct dependency surface is very small:

- 0213 `goldenRat_norm_abs_le_five_sixteen`
- `norm_num`
- `linarith`
- the linear ordered field structure of `ℚ`

The statement itself does not mention `goldenRatNorm` by name. It repeats the same polynomial used in 0213:

$$
u^2+uv-v^2.
$$

Conceptually the dependency chain is simply

$$
\texttt{goldenRat\_norm\_abs\_le\_five\_sixteen}
\Longrightarrow
\frac5{16}\text{ bound}
\Longrightarrow
<1.
$$

## Proof flow

### 1. Obtain the sharp bound from 0213

```lean
have h := goldenRat_norm_abs_le_five_sixteen hu hv
```

This gives

$$
|u^2+uv-v^2|\le\frac5{16}.
$$

### 2. Normalize the rational constants

```lean
norm_num at h ⊢
```

`norm_num` normalizes rational constants such as `5/16`, `1/2`, and `1`, preparing both the hypothesis and the goal for a simple order argument.

The hard nonlinear estimate has already been completed in 0213, so no new `nlinarith` call is required here.

### 3. Close the strict inequality by linear arithmetic

```lean
linarith
```

From `h : |Q| ≤ 5/16` together with `5/16 < 1`, `linarith` derives

$$
|Q|<1.
$$

## Lean-specific processing

Unlike 0213, this theorem contains no absolute-value expansion, completion of squares, `sq_nonneg`, or nonlinear arithmetic.

The local theorem result is stored with

```lean
have h := ...
```

and `norm_num at h ⊢` simultaneously normalizes both the hypothesis and the goal. The remaining relation is linear, so `linarith` is sufficient.

The proof architecture is therefore deliberately layered as

```text
hard nonlinear estimate (0213)
→ numeric normalization
→ linear strictness step (0214)
```

This is useful from a maintenance perspective: downstream proofs only depend on the `<1` interface and do not need to know how the sharp constant `5/16` was obtained.

## Redundancy and duplication

Logically, 0214 is an immediate corollary of 0213 and the numerical fact `5/16 < 1`. Downstream code could inline the two-step argument rather than naming a separate theorem.

However, the dedicated theorem is useful API redundancy:

- Euclidean division needs exactly `|Q|<1`, not the sharp constant itself.
- downstream proofs do not need to know the value `5/16`.
- the sharp estimate could later be replaced by any bound `c<1` without changing the consumer-facing theorem.
- `golden_remainder_size_lt` becomes much easier to read mathematically.

Thus 0213 and 0214 are close in logical content but serve distinct roles: **sharp estimate** versus **Euclidean contraction interface**.

There is also an API-level duplication with 0210 `goldenRatNorm`: the quadratic polynomial is repeated directly in the statement instead of using the named function. This keeps the connection to 0213 syntactically simple but pushes the bridge to the named norm API into later `simpa [goldenRatNorm]` calls.

## Optimization candidates

1. **State the theorem with `goldenRatNorm`**

```lean
|goldenRatNorm (u, v)| < 1
```

This would make the link to 0210 explicit.

2. **Use `lt_of_le_of_lt` instead of `linarith`**

Conceptually the theorem could be written as

```lean
exact lt_of_le_of_lt
  (goldenRat_norm_abs_le_five_sixteen hu hv)
  (by norm_num)
```

which may remove the solver dependency. Exact elaboration is unverified here because this museum pass does not run Lean builds.

3. **Avoid introducing a generic contraction helper**

A helper for turning `|Q| ≤ c` and `c < 1` into `|Q| < 1` would add abstraction without meaningful reuse.

4. **Keep the current two-layer API deliberately**

Separating sharp mathematics from the downstream contraction interface is arguably a strength of the present design rather than a defect.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct features used by this theorem are mainly:

- `ℚ`
- ordered-field inequalities
- `norm_num`
- `linarith`

Unlike 0213, this theorem does not directly require `abs_le`, `sq_nonneg`, or `nlinarith`. The surrounding `GoldenEuclidean.lean` module, however, also uses rounding, `field_simp`, `ring`, casts, `EuclideanDomain`, and well-founded measures, so module-level import minimization is broader than the local surface of 0214.

No Lean build is performed in this museum pass, so the exact minimal import modules remain unverified and are recorded only as optimization candidates.

## Comparator challenge suitability

Yes. The theorem is small enough that proof-style differences are easy to measure.

Possible variants include:

- A: current `have` + `norm_num` + `linarith`
- B: `lt_of_le_of_lt` + `norm_num`
- C: `nlinarith [goldenRat_norm_abs_le_five_sixteen hu hv]`
- D: an API whose statement uses `goldenRatNorm`
- E: prove `<1` directly from the cell hypotheses without passing through 0213

Useful comparison axes are proof-term size, solver dependence, visibility of the sharp constant, clarity of the downstream interface, and robustness under future changes to the sharp bound.

The contrast between A and B is especially clean: it compares delegating the final order step to an arithmetic solver with spelling out order transitivity in the proof term.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, 0214 appears immediately after 0213 and is followed by

```lean
/-- A nonzero golden integer has nonzero norm. -/
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  ...
```

The later theorem `golden_remainder_size_lt` directly consumes 0214 to show that the nearest-lattice rounding error has norm below `1`.

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0215 `goldenNorm_ne_zero_of_ne_zero`**:

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

By 0214, the rounding-error side of the strict contraction argument is complete. Declaration 0215 proves that a nonzero divisor has nonzero norm, making division by `goldenNorm y` safe in the rational quotient-coordinate construction that follows.

# 0213 — `goldenRat_norm_abs_le_five_sixteen`

## Lean type

```lean
/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| ≤ (5 : ℚ) / 16 := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  rw [abs_le]
  constructor
  · have hs := sq_nonneg (u + v / 2)
    nlinarith
  · have hs := sq_nonneg (v - u / 2)
    nlinarith
```

This is a `theorem` proving that the quadratic form appearing in rational golden coordinates,

$$
Q(u,v)=u^2+uv-v^2,
$$

is uniformly bounded on the square fundamental cell produced by nearest-integer rounding:

$$
|u|\le\frac12,\qquad |v|\le\frac12
$$

implies

$$
|Q(u,v)|\le\frac{5}{16}.
$$

## Mathematical statement

Declaration 0210 `goldenRatNorm` introduces the golden norm form on rational coordinates,

$$
Q(u,v)=u^2+uv-v^2.
$$

The present theorem evaluates this form on the rounding-error cell supplied by 0212 `exists_goldenRat_near_int`:

$$
(u,v)\in[-1/2,1/2]^2.
$$

It proves the uniform estimate

$$
|u^2+uv-v^2|\le\frac5{16}.
$$

The constant is not merely convenient; it is sharp. For example,

$$
Q\left(\frac12,\frac14\right)
=\frac14+\frac18-\frac1{16}
=\frac5{16},
$$

while

$$
Q\left(-\frac14,\frac12\right)
=\frac1{16}-\frac18-\frac14
=-\frac5{16}.
$$

Thus the source comment “sharp uniform constant” has the natural interpretation

$$
\sup_{|u|,|v|\le1/2}|u^2+uv-v^2|=\frac5{16}.
$$

## Role in the full proof

The purpose of `GoldenEuclidean.lean` is to make `GoldenInt` a norm-Euclidean domain.

The relevant chain is:

1. 0209 `GoldenRat` introduces rational quotient coordinates.
2. 0210 `goldenRatNorm` introduces the rational golden norm form.
3. 0211–0212 round each quotient coordinate to the nearest integer, placing the error in `[-1/2,1/2]^2`.
4. **0213, the present theorem**, bounds the norm on that cell by `5/16`.
5. 0214 `goldenRat_norm_abs_lt_one` converts `5/16 < 1` into a strict contraction.
6. `goldenRemainder_norm_rat_identity` expresses the remainder norm as divisor norm times the rational error norm.
7. `golden_remainder_size_lt` concludes

$$
|N(r)|<|N(y)|.
$$

Thus 0213 is the quantitative core that turns nearest-lattice rounding into a strict Euclidean decrease.

## Direct dependencies

The main Mathlib ingredients directly used by the proof are:

- `abs_le.mp`
- `sq_nonneg`
- `nlinarith`
- the ordered-field structure of `ℚ`
- absolute value, squaring, and division

Structurally, it is also tied to:

- the quadratic form defined by 0210 `goldenRatNorm`;
- the hypothesis shape produced by 0212 `exists_goldenRat_near_int`.

The Lean statement does not mention `goldenRatNorm` by name; it spells out the polynomial explicitly. Likewise, 0212 is not invoked inside this theorem. Instead, the two coordinate bounds are accepted directly as hypotheses `hu` and `hv`, making 0213 a local cell-estimate lemma.

## Proof flow

### 1. Convert absolute-value bounds into two-sided inequalities

```lean
have hu' := abs_le.mp hu
have hv' := abs_le.mp hv
```

This yields

$$
-\frac12\le u\le\frac12,
\qquad
-\frac12\le v\le\frac12.
$$

### 2. Bound the coordinate squares by `1/4`

```lean
have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
```

From the two-sided coordinate bounds, `nlinarith` derives

$$
u^2\le\frac14,\qquad v^2\le\frac14.
$$

### 3. Split the final absolute-value inequality

```lean
rw [abs_le]
constructor
```

The goal

$$
|Q(u,v)|\le\frac5{16}
$$

becomes the pair

$$
-\frac5{16}\le Q(u,v)
$$

and

$$
Q(u,v)\le\frac5{16}.
$$

### 4. Derive the lower bound from a nonnegative square

```lean
have hs := sq_nonneg (u + v / 2)
nlinarith
```

The certificate

$$
\left(u+\frac v2\right)^2\ge0
$$

expands to

$$
u^2+uv+\frac{v^2}{4}\ge0.
$$

Combining this with `v² ≤ 1/4` gives

$$
u^2+uv-v^2\ge-\frac5{16}.
$$

### 5. Derive the upper bound from the complementary square

```lean
have hs := sq_nonneg (v - u / 2)
nlinarith
```

Now use

$$
\left(v-\frac u2\right)^2\ge0,
$$

or

$$
v^2-uv+\frac{u^2}{4}\ge0.
$$

Together with `u² ≤ 1/4`, this yields

$$
u^2+uv-v^2\le\frac5{16}.
$$

These two completion-of-squares certificates are exactly what produce the sharp constant `5/16`.

## Lean-specific processing

`abs_le.mp hu` transforms the proposition `|u| ≤ 1/2` into a conjunction representing the two-sided interval bound. The local facts `hu'` and `hv'` remain conjunctions, and `nlinarith` is able to use their components when deriving the square estimates.

Later, `rw [abs_le]` performs the converse kind of transformation on the goal, replacing an absolute-value inequality by two ordered inequalities.

The facts

```lean
sq_nonneg (u + v / 2)
```

and

```lean
sq_nonneg (v - u / 2)
```

are supplied as explicit nonlinear certificates. The proof does not manually expand them with `ring`; instead `nlinarith` reads the polynomial constraints and combines them with `huSq` and `hvSq`.

This makes the proof a clean example of the style:

> provide the mathematically decisive nonnegative squares explicitly, then delegate the remaining polynomial bookkeeping to the nonlinear arithmetic solver.

## Redundancy and duplication

The main API-level duplication is that 0210 has already defined

```lean
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

but the present theorem restates the polynomial directly in its conclusion instead of writing `goldenRatNorm (u,v)`.

The explicit polynomial may make the arithmetic proof simpler, but it means the statement must remain synchronized with the named norm definition if the representation ever changes.

There is also symmetry between the two square bounds `huSq` and `hvSq`. A helper lemma of the shape

```lean
|x| ≤ 1/2 → x^2 ≤ 1/4
```

could remove that small duplication, although introducing another public lemma may cost more API surface than the two current lines justify.

## Optimization candidates

1. **State the result through `goldenRatNorm`**

```lean
|goldenRatNorm (u, v)| ≤ (5 : ℚ) / 16
```

This would make the dependency on 0210 explicit at the theorem surface.

2. **Name the completion-of-squares bounds**
   - expose the upper and lower estimates as separate lemmas;
   - this improves mathematical transparency but lengthens the local API.

3. **Introduce a square-cell predicate**
   - package `|u|≤1/2 ∧ |v|≤1/2` under a named geometric predicate;
   - this could clarify the 0212 → 0213 → 0214 interface.

4. **Formalize sharpness separately**
   - a small certificate at `(1/2,1/4)` would formally justify the source comment that `5/16` is sharp.

5. **Avoid over-generalizing the quadratic form**
   - the current form admits an exceptionally short completion-of-squares proof, so a generic quadratic-form abstraction may add more burden than value.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The main features needed by this theorem in isolation are:

- `ℚ`
- absolute value and `abs_le`
- ordered ring / field arithmetic
- `sq_nonneg`
- `nlinarith`

The theorem itself should therefore need substantially less than all of `Mathlib`. However, the complete `GoldenEuclidean.lean` module later uses rounding, `field_simp`, `ring`, coercions, `EuclideanDomain`, and well-founded measures, so module-level import minimization has a broader target.

Because this museum pass does not run a Lean build, the exact minimal import modules remain unverified and are recorded only as optimization candidates.

## Comparator challenge suitability

This theorem is very suitable for a Comparator challenge because both the mathematics and the target bound are compact.

Possible implementations are:

- A: current `sq_nonneg` + `nlinarith`
- B: explicit completion-of-squares identities via `ring`, followed by `linarith`
- C: direct extremum analysis on the square boundary
- D: a theorem stated with `goldenRatNorm` plus a dedicated cell predicate
- E: rescale to `U=2u`, `V=2v` and prove an equivalent integer-coefficient bound on `[-1,1]^2`

Useful metrics are proof-term size, mathematical readability, solver dependence, transparency of the constant `5/16`, generalizability, and robustness under changes to the norm representation.

The A-versus-B comparison is especially instructive for deciding how much of a completion-of-squares argument should be exposed explicitly in Lean and how much should be delegated to arithmetic automation.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0212 and immediately before 0214 `goldenRat_norm_abs_lt_one`.

```lean
/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen ...
```

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0214 `goldenRat_norm_abs_lt_one`**:

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

Declaration 0213 provides the sharp quantitative estimate `5/16`. Declaration 0214 then uses only

$$
\frac5{16}<1
$$

to convert it into the qualitative strict-contraction form required downstream by `golden_remainder_size_lt`.
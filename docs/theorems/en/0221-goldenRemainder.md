# 0221 — `goldenRemainder`

## Lean type

```lean
/-- The residual after nearest-lattice normalization. -/
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

This is a `def`, not a theorem. Using the golden-integer quotient selected by 0220 `goldenQuotient`, it defines the remainder in the standard Euclidean form

$$
r=x-qy.
$$

## Mathematical statement and meaning of the declaration

Let

$$
q=\operatorname{goldenQuotient}(x,y).
$$

Then the present definition is exactly

$$
r=x-qy.
$$

The quotient `q` is obtained by taking the rational quotient coordinates from 0219 and rounding each coordinate to the nearest integer. Thus `goldenRemainder` is not merely an arbitrary difference: it is the **error left after normalizing the exact rational quotient to the golden-integer lattice**.

If

$$
\frac{x}{y}=A+B\varphi,
$$

then conceptually

$$
q=\operatorname{round}(A)+\operatorname{round}(B)\varphi
$$

and

$$
r=x-qy.
$$

Downstream, the relative quotient error is expressed through

$$
A-\operatorname{round}(A),\qquad B-\operatorname{round}(B),
$$

and the contraction estimate from 0214 is applied to those two coordinates.

## Role in the full proof

The norm-Euclidean construction in `GoldenEuclidean.lean` proceeds as follows.

1. Declarations 0216–0218 compute the integral coordinates of `x * conjugate(y)`.
2. 0219 `goldenQuotientCoords` divides those coordinates by `N(y)` to obtain the exact rational quotient.
3. 0220 `goldenQuotient` rounds both coordinates to the nearest integers.
4. **0221 `goldenRemainder` defines `r = x - qy`.**
5. `golden_quotient_mul_add_remainder` proves the Euclidean identity

$$
yq+r=x.
$$

6. The private theorem `goldenRemainder_norm_rat_identity` factors the remainder norm into the divisor norm times the norm of the rounding error.
7. `golden_remainder_size_lt` proves

$$
|N(r)|<|N(y)|.
$$

8. Finally, `goldenEuclideanDomain` installs this declaration directly as the `remainder` field of `EuclideanDomain GoldenInt`.

The source later contains

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
  ...
```

so this is not merely a helper difference function. It is the concrete remainder algorithm of the completed Euclidean-domain structure.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0220 `goldenQuotient`
- 0124 `goldenMul`
- the `Sub GoldenInt` instance

Because this is a definition, there is no proof script.

Its mathematical background includes:

- 0219 `goldenQuotientCoords`
- 0213 `goldenRat_norm_abs_le_five_sixteen`
- 0214 `goldenRat_norm_abs_lt_one`

Conceptually,

$$
q=\operatorname{goldenQuotient}(x,y)
\longrightarrow
r=x-qy
\longrightarrow
N(r)=N(y)\,Q(\text{rounding error})
\longrightarrow
|N(r)|<|N(y)|.
$$

## Construction flow

The definition is a single line:

```lean
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

1. Compute the discrete quotient `q = goldenQuotient x y`.
2. Compute the multiple `qy` using `goldenMul`.
3. Subtract it from `x` using the `GoldenInt` subtraction structure.
4. Return the resulting `GoldenInt` as the remainder.

The definition itself contains no norm inequality. It deliberately separates the **construction** of the remainder from the later **proof** that the remainder is Euclidean-small.

## Lean-specific processing

### 1. Raw multiplication and standard subtraction are mixed

The multiplication is written explicitly as `goldenMul`, while subtraction uses the standard notation `x - ...`.

This reflects the development's dual API: explicit coordinate operations coexist with Mathlib's standard algebra notation. In the next identity theorem, the source uses

```lean
simp [goldenRemainder, golden_mul_eq]
ring
```

to bridge the raw multiplication back to standard `*` notation.

### 2. The remainder is a total function

There is no assumption `y ≠ 0`, so `goldenRemainder x 0` is also defined.

This matches the design of the `EuclideanDomain` remainder field, which is a total operation. Nonzeroness of the divisor is required only by the later strict-decrease theorem.

### 3. Projection simp lemmas are used directly downstream

In `goldenRemainder_norm_rat_identity`, the source expands the first coordinate through a simp set containing

```lean
simp only [goldenRemainder, goldenMul, golden_fst_sub, ...]
```

and similarly expands the second coordinate with `golden_snd_sub`.

Thus the projection API developed much earlier in the golden-order layer becomes an active component of the Euclidean proof here.

## Redundancy and duplication

Mathematically, `r = x - qy` is completely standard, so one could avoid a named `goldenRemainder` definition and repeat the expression wherever needed.

A dedicated definition nevertheless has substantial API value:

- it can be installed directly in the Euclidean-domain instance;
- long norm proofs do not need to repeat the quotient expression;
- the boundary between quotient selection and remainder construction remains explicit;
- downstream theorem statements can remain stable if the quotient algorithm changes.

There is also mild API duplication in the mixture of raw `goldenMul` and standard multiplication. A version defined entirely with standard notation is a viable alternative.

## Optimization candidates

1. **Use standard multiplication notation throughout**

```lean
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenQuotient x y * y
```

This may reduce later uses of `golden_mul_eq`.

2. **Bundle quotient and remainder together**

A structure such as `GoldenDivisionResult` could carry `q`, `r`, and an identity certificate. This may reduce recomputation downstream, at the cost of a heavier API.

3. **Make the zero-divisor branch explicit**

One could define `if y = 0 then x else ...`. The current design is simpler because the quotient is already total and specification theorems handle the special case separately.

4. **Generalize the generic remainder layer**

The equation `r = x - qy` is not golden-specific. A more general quadratic-order Euclidean framework could isolate the golden-specific work to quotient selection and norm contraction.

5. **Promote the norm identity if reuse grows**

The private theorem `goldenRemainder_norm_rat_identity` is close to the mathematical core of the Euclidean proof. If later developments need it, exposing it as public API may be worthwhile.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The definition itself directly needs mainly:

- `GoldenInt`
- subtraction / `Sub`
- `goldenMul`
- `goldenQuotient`

It uses no tactic and no analytic theorem directly.

The full `GoldenEuclidean.lean` module, however, uses a much broader surface including `round`, `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, `measure`, and the `EuclideanDomain` hierarchy.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current remainder definition with raw `goldenMul`
- B: use standard `*` notation only
- C: bundle quotient, remainder, and the division identity
- D: use an explicit zero-divisor branch in the total division API
- E: specialize a generic quadratic-order Euclidean division framework

Useful comparison axes include:

- proof size of `golden_quotient_mul_add_remainder`
- expansion size in the norm identity proof
- simp / rewrite burden
- naturalness of integration with `EuclideanDomain`
- auditability of the explicit coordinate API
- generalizability

The A-versus-B comparison is especially small and clear: it directly measures whether keeping the raw multiplication API visible helps or hurts the downstream Euclidean proofs.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source confirms the sequence

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩

def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y

theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ...
```

Later, `goldenRemainder_norm_rat_identity` and `golden_remainder_size_lt` unfold this definition directly, and the final `goldenEuclideanDomain` instance installs it as its `remainder` field.

The branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0222 `goldenQuotient_zero`**:

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

Now that 0220–0221 provide total quotient and remainder functions, 0222 establishes the special-case law that division by zero yields quotient zero. This theorem is installed directly as the `quotient_zero` field of the final `EuclideanDomain` instance.

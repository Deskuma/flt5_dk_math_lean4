# 0182 — `goldenNorm_sqrtFive`

## Lean type

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

This is a `theorem`. It states that the golden norm of `goldenSqrtFive : GoldenInt := ⟨-1, 2⟩`, introduced in 0177, is `-5`.

## Mathematical statement and meaning of the declaration

Read a coordinate pair `⟨a,b⟩ : GoldenInt` as

$$
a+b\varphi.
$$

The golden norm was defined in 0164 by

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

and 0177 defines

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩.
```

Substituting these coordinates gives

$$
N(2\varphi-1)=(-1)^2+(-1)\cdot2-2^2=1-2-4=-5.
$$

Thus the theorem represents

$$
N(\sqrt5)=-5.
$$

Here `goldenSqrtFive` is not a square-root function on the reals; it is the explicit golden-integer element $2\varphi-1$.

## Role in the overall proof

Declaration 0181 `goldenSqrtFive_sq` establishes

$$
(2\varphi-1)^2=5.
$$

The present theorem adds that the same ramified element has norm `-5`. Together, these facts identify both its square relation and its norm size.

Immediately afterward the source contains

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

followed by `goldenNorm_tau : goldenNorm goldenTau = 5`. Therefore 0182 supplies the signed norm side of the norm-five ramification package.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0164 `goldenNorm`
- 0177 `goldenSqrtFive`
- Mathlib's `norm_num` tactic for concrete integer normalization

The theorem is mathematically closely related to 0181 `goldenSqrtFive_sq`, but the Lean proof does not use 0181. Instead it unfolds `goldenNorm` and `goldenSqrtFive` directly.

## Proof / construction flow

The proof is only

```lean
by
  norm_num [goldenNorm, goldenSqrtFive]
```

After unfolding the two definitions, the goal is essentially the closed integer calculation

```text
(-1 : ℤ)^2 + (-1) * 2 - 2^2 = -5
```

and `norm_num` normalizes the powers, products, additions, and subtraction.

## Lean-specific processing

`norm_num [goldenNorm, goldenSqrtFive]` unfolds both definitions and then solves the resulting concrete integer equality using numeric normalization.

Declaration 0181 uses `by decide` because its target is a closed equality of concrete `GoldenInt` values. Declaration 0182 instead reduces to an equality in `ℤ`, for which `norm_num` is the natural proof tool. Both are closed computations, but the tactic reflects the target type.

## Redundancy and duplication

Mathematically one could derive this theorem from the square relation in 0181 together with more structural norm identities. The current source instead evaluates the explicit coordinates directly because that proof is shorter.

There is also a repeated proof pattern across 0167 `goldenNorm_phi`, 0169 `goldenNorm_ofInt`, 0182, and the later `goldenNorm_tau`: each evaluates `goldenNorm` on a distinguished concrete element and closes with numerical normalization. This is better viewed as a family of closed certificates than as serious mathematical duplication.

## Optimization candidates

1. Keep `norm_num [goldenNorm, goldenSqrtFive]` as a direct regression certificate.
2. Derive the result structurally from 0181 together with `golden_mul_conj` and conjugation facts.
3. Bundle `goldenNorm` as a multiplicative map and obtain the result as a specialization of a general theorem.
4. Group the square, conjugation, and norm properties of `goldenSqrtFive` in a dedicated namespace or structure.
5. Abstract a norm theorem for the discriminant element of a general quadratic order and specialize it to discriminant `5`.

The current implementation is less general, but it is very small and directly detects changes to the coordinate definitions.

## Required Mathlib imports and import optimization

The theorem directly needs the existing `GoldenInt`, `goldenNorm`, and `goldenSqrtFive` definitions together with `norm_num`. The standalone artifact imports all of `Mathlib`, but this theorem alone is unlikely to require the whole library.

A reduced import set would likely consist of the integer arithmetic and `norm_num` support required by the upstream `GoldenOrder` definitions. Because this museum pass does not run Lean builds, the exact minimal import set remains unverified and import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementations to compare are:

- concrete coordinates + `norm_num`
- derivation from the square relation in 0181
- a structural proof through `golden_mul_conj`
- specialization of a bundled multiplicative norm
- specialization of a generic quadratic-order / discriminant theorem

Comparison criteria include proof-term size, mathematical explanatory power, robustness under definition changes, downstream reuse, required imports, and generalizability.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated source contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In the source, this theorem appears immediately after 0181 `goldenSqrtFive_sq` and immediately before 0183 `goldenTau_eq_phi_mul_sqrtFive`.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. However, the exact PDF page or section corresponding to this small theorem was not identified directly, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

Declarations 0178 and 0177 define `goldenTau = 2+φ` and `goldenSqrtFive = 2φ-1`. Declaration 0183 makes explicit that

$$
2+\varphi=\varphi(2\varphi-1),
$$

linking `tau` and the ramified square-root element through the unit `φ` and preparing the later associate / norm-five arithmetic.
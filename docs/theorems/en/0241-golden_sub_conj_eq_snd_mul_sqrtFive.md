# 0241 — `golden_sub_conj_eq_snd_mul_sqrtFive`

## Lean type

```lean
/-- Subtracting the conjugate isolates the square-root-of-five direction. -/
theorem golden_sub_conj_eq_snd_mul_sqrtFive (x : GoldenInt) :
    x - goldenConj x = goldenMul (goldenOfInt x.snd) sqrtFiveElement := by
  apply GoldenInt.ext
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
    ring
```

This is a `theorem` stating that the difference between a golden integer `x` and its conjugate is entirely carried by the second coordinate `x.snd` times the distinguished square-root-of-five element.

## Mathematical statement

Write

$$
x=a+b\varphi.
$$

Golden conjugation sends this to

$$
\overline{x}=(a+b)-b\varphi.
$$

Therefore

$$
x-\overline{x}
=(a+b\varphi)-((a+b)-b\varphi)
=-b+2b\varphi.
$$

Using the element introduced in 0177,

$$
\sqrt5=2\varphi-1,
$$

represented by `sqrtFiveElement = goldenSqrtFive = ⟨-1,2⟩`, we obtain

$$
b\sqrt5=b(2\varphi-1)=-b+2b\varphi.
$$

Hence

$$
x-\overline{x}=b\sqrt5.
$$

The Lean statement expresses this in the raw golden API as

```lean
goldenMul (goldenOfInt x.snd) sqrtFiveElement.
```

## Role in the full proof

By 0240, the desired algebraic output from a ramifier-stripped packet has been isolated as the contract

$$
\beta=\varepsilon\gamma^5.
$$

To obtain that factorization, the development first needs to prove that `beta` and `goldenConj beta` are relatively prime. `SignedGoldenConjugateCoprime.lean` is the module that establishes this fact, and the present theorem is its first coordinate identity.

If a common divisor `d` divides both `beta` and `conj beta`, then 0191 `goldenDivides_sub` gives

$$
d\mid \beta-\overline\beta.
$$

The present theorem exposes that difference as

$$
\beta-\overline\beta=\beta_{\mathrm{snd}}\sqrt5.
$$

The next declaration, 0242, therefore turns its norm into

$$
N(\beta-\overline\beta)=-5\,\beta_{\mathrm{snd}}^2.
$$

Using the stripped-packet coordinate formula

$$
\beta_{\mathrm{snd}}=-5^7a^{10},
$$

the difference norm becomes

$$
-5^{15}a^{20}.
$$

At the same time `N(beta)=b^5`. Thus the norm of any common divisor must divide both `b^5` and `5^15 a^20`. The power-split coprimality then forces its absolute norm to be `1`, which converts the divisor into a golden unit. In this sense 0241 is the first factorization step in the conjugate-coprimality argument.

## Direct dependencies

The statement and proof directly use the following declarations:

- `GoldenInt`
- 0163 `goldenConj`
- 0162 `goldenOfInt`
- 0177 `goldenSqrtFive`
- 0179 `sqrtFiveElement`
- 0124 `goldenMul`
- `GoldenInt.ext`

Rather than composing higher-level lemmas, the proof unfolds these concrete definitions and verifies the identity coordinatewise.

Conceptually, the dependency is

$$
\text{conjugation formula}
+\sqrt5=2\varphi-1
\Longrightarrow
x-\overline{x}=x_{\mathrm{snd}}\sqrt5.
$$

## Proof flow

The proof first reduces equality of `GoldenInt` values to equality of their two coordinates:

```lean
apply GoldenInt.ext
```

For the first coordinate,

```lean
simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
```

unfolds all relevant definitions and normalizes both sides to `-x.snd`.

For the second coordinate, the same unfolding leaves an elementary integer polynomial identity, which is closed by

```lean
ring
```

and mathematically says that both sides have second coordinate `2 * x.snd`.

## Lean-specific processing

`GoldenInt.ext` is the key reduction principle: equality of the explicit coordinate structure is reduced to its `fst` and `snd` fields. In this model, it is often shorter to expose the concrete coordinates and delegate the remaining arithmetic to `simp` and `ring` than to build a more abstract theorem chain.

The simplifier unfolds `goldenSqrtFive` rather than explicitly naming `sqrtFiveElement` because `sqrtFiveElement` is an `abbrev`; it transparently reduces to `goldenSqrtFive`.

The statement also mixes standard subtraction on the left with raw `goldenMul` on the right. This reflects the current API layering. Declarations 0158 `golden_sub_eq` and 0159 `golden_mul_eq` ensure that raw operations and standard ring notation remain interoperable.

## Redundancy and duplication

At the coordinate level, the theorem is the elementary identity

$$
x-\overline{x}=b(2\varphi-1).
$$

A generic quadratic-order conjugation API could potentially derive this theorem automatically, so the explicit coordinate proof is mathematically specialized.

Nevertheless, the named theorem is valuable. The downstream argument does not merely need the coordinates of a difference; it needs the fact that the entire difference factors through the **square-root-of-five direction**. This exact factorization is what enables 0242 to use `goldenNorm_mul` and `goldenNorm_sqrtFive` directly.

There is also a mild API duplication between `sqrtFiveElement` and `goldenSqrtFive`. The public statement uses the shorter alias, while the proof unfolds the concrete internal definition. This makes visible the intended separation between public naming and implementation-level coordinates.

## Optimization candidates

1. **Keep the current coordinate proof**
   - shallow dependencies and easy proof auditing.

2. **Use standard ring notation throughout**
   - a statement closer to

```lean
x - goldenConj x = (x.snd : GoldenInt) * sqrtFiveElement
```

   could integrate more naturally with generic algebra rewriting, provided the integer-cast API is made convenient.

3. **Bundle conjugation as a `RingEquiv`**
   - involution, additive compatibility, multiplicativity, negation, subtraction, and power compatibility are already established upstream.

4. **Generalize to quadratic orders**
   - one could prove a generic theorem that `x - conj x` lies in the anti-invariant basis direction and specialize it to the golden order.

5. **Treat 0241 and 0242 as a factor/norm API pair**
   - they are naturally consumed together and could be documented or packaged as one downstream interface.

The current proof is already very small, so local proof compression is not a high-priority optimization.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The theorem itself directly needs only a relatively small surface:

- structure extensionality;
- `simp`;
- integer polynomial normalization through `ring`;
- project-local definitions for `GoldenInt`, conjugation, multiplication, integer embedding, and the square-root-of-five element.

The theorem in isolation likely requires much less than all of `Mathlib`. However, the full `SignedGoldenConjugateCoprime.lean` module also uses divisibility, norms, coprimality, `natAbs`, and integer/natural casts, so import minimization should be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful contestants include:

- A: current `ext + simp + ring` coordinate proof;
- B: a proof normalized through `golden_sub_eq` / `golden_mul_eq` and standard notation;
- C: an abstract proof after bundling `goldenConj` as a `RingEquiv`;
- D: specialization of a generic quadratic-order conjugation theorem;
- E: an explicit algebraic rewrite from `sqrtFiveElement = 2*phi - 1`.

Useful metrics are proof size, direct dependency depth, visibility of the mathematical factorization, dependence on raw coordinate APIs, interoperability with Mathlib's generic algebra layer, and generalizability.

Approach A maximizes transparency of the concrete model; C and D maximize algebraic reuse. This makes the theorem a clean Comparator challenge for the museum.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In the source, 0240 `SignedGoldenFifthPowerUpToUnitCore` closes `SignedGoldenRamifierStripped.lean`. The next generated module is `SignedGoldenConjugateCoprime.lean`, and the present theorem is its first declaration.

The module header explicitly explains the intended argument: a common divisor of `beta` and `conj beta` divides both `N(beta)=b^5` and the norm of their difference `-5^15*a^20`; coprimality of these integer masses then forces the common divisor to have norm `±1` and hence to be a golden unit.

The exact Japanese or English PDF page corresponding to this theorem was not directly identified in this pass, so no PDF page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0242 `goldenNorm_sub_conj`**:

```lean
/-- The norm of the conjugate difference is `-5` times the square coordinate. -/
theorem goldenNorm_sub_conj (x : GoldenInt) :
    goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2 := by
  rw [golden_sub_conj_eq_snd_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_sqrtFive]
  simp [goldenNorm, goldenOfInt]
  ring
```

Declaration 0241 factors

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5.
$$

Declaration 0242 applies norm multiplicativity and `N(sqrtFive)=-5` to obtain

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2.
$$

This is the next bridge between the explicit five-adic mass stored in the stripped packet and the norm of a common divisor.

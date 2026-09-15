# 0385 `lift_relPrime_conj`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this theorem proves that the quadratic re-entry element `goldenZeroSectorLift p.base` and its conjugate `goldenConj (goldenZeroSectorLift p.base)` are `GoldenRelPrime`.

## Lean code

```lean
/-- The re-entry element and its conjugate have no nonunit common divisor. -/
theorem lift_relPrime_conj (p : GoldenZeroSectorDescentPacket) :
    GoldenRelPrime (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) := by
  intro z hzAlpha hzConj
  have hzDiff : GoldenDivides z
      (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenDivides_sub hzAlpha hzConj
  have hzNormAlpha : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base) :=
    goldenNorm_dvd_of_goldenDivides hzAlpha
  have hzNormDiff : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenNorm_dvd_of_goldenDivides hzDiff
  have hzD : (goldenNorm z).natAbs ∣ p.D ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [goldenZeroSectorLift_norm, p.H_eq] using hzNormAlpha
  have hzS : (goldenNorm z).natAbs ∣
      5 * p.base.snd.natAbs ^ 4 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm z ∣ (5 : ℤ) * p.base.snd ^ 4 := by
      apply Int.dvd_neg.mp
      convert hzNormDiff using 1
      rw [goldenNorm_sub_conj, goldenZeroSectorLift_snd]
      ring
    have habspow : abs p.base.snd ^ 4 = p.base.snd ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    simpa [Int.natCast_natAbs, habspow] using hpos
  have hD5 : Nat.Coprime (p.D ^ 5) 5 :=
    Nat.Coprime.pow_left 5
      ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
        p.five_not_dvd_D).symm
  have hDS : Nat.Coprime (p.D ^ 5) (p.base.snd.natAbs ^ 4) :=
    (Nat.Coprime.pow_left 5 p.coprime_D_s).pow_right 4
  have hcop : Nat.Coprime (p.D ^ 5)
      (5 * p.base.snd.natAbs ^ 4) := hD5.mul_right hDS
  have hone : (goldenNorm z).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hzD hzS
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega
```

## Lean type

Expanding the namespace, the conceptual type is

```lean
GoldenZeroSectorDescentPacket.lift_relPrime_conj :
  (p : GoldenZeroSectorDescentPacket) →
    GoldenRelPrime
      (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base))
```

From the proof shape `intro z hzAlpha hzConj`, `GoldenRelPrime alpha beta` is a relative-primality predicate requiring every golden integer `z` dividing both `alpha` and `beta` to be a unit.

## Mathematical statement

Write `p.base = (r,s)` and set

$$
\alpha = T(r,s)=\operatorname{goldenZeroSectorLift}(r,s).
$$

The theorem establishes the analogue of

$$
\gcd_{\mathbb Z[\varphi]}(\alpha,\overline\alpha)=1.
$$

Here “1” does not mean that an integer gcd object is literally constructed. It means that every common divisor in the golden integer ring is a unit.

Assume `z` divides both `alpha` and `conj alpha`. Norm divisibility gives

$$
|N(z)| \mid |N(\alpha)|.
$$

Using the packet invariants prepared in 0380--0384 and

$$
N(\alpha)=H(r,s)=D^5,
$$

we obtain

$$
|N(z)|\mid D^5.
$$

Since `z` divides both `alpha` and `conj alpha`, it also divides their difference

$$
\alpha-\overline\alpha.
$$

The second coordinate of the quadratic lift is `s^2`, and `goldenNorm_sub_conj` turns the norm of the difference, up to sign, into

$$
5s^4.
$$

Hence

$$
|N(z)|\mid 5|s|^4.
$$

By 0382 `five_not_dvd_D` and 0384 `coprime_D_s`,

$$
\gcd(D^5,5|s|^4)=1.
$$

Therefore the natural number `|N(z)|`, which divides both coprime numbers, must satisfy

$$
|N(z)|=1.
$$

Thus

$$
N(z)=\pm1,
$$

so `z` is a unit in the golden integer ring.

## Role in the full proof

This theorem is an important ring-theoretic bridge in the zero-sector descent.

Up through 0382--0384, the preparation is largely in ordinary natural-number arithmetic:

$$
5\nmid D,
\qquad
\gcd(D,|s|)=1.
$$

The present theorem lifts that information to the golden integer statement

$$
\operatorname{GoldenRelPrime}(T(r,s),\overline{T(r,s)}).
$$

This relative primality is a direct input to the later `exists_lift_eq_fifthPower`, where `goldenCoprimeFactorOfFifthPower` is applied. Since 0375 `goldenZeroSectorLift_mul_conj` has already supplied a fifth-power product of the form

$$
T(r,s)\overline{T(r,s)}=D^5,
$$

the relative-prime property proved here allows the proof to proceed to a factorization

$$
T(r,s)=\varepsilon\gamma^5.
$$

Thus 0385 is the boundary theorem connecting arithmetic coprimality preparation to the golden-ring fifth-power factorization machinery.

## Direct dependencies

The main project declarations used directly are:

- `GoldenZeroSectorDescentPacket`
- `GoldenRelPrime`
- `GoldenDivides`
- `goldenZeroSectorLift`
- `goldenConj`
- `goldenDivides_sub`
- `goldenNorm`
- `goldenNorm_dvd_of_goldenDivides`
- `goldenZeroSectorLift_norm`
- `GoldenZeroSectorDescentPacket.H_eq`
- `goldenNorm_sub_conj`
- `goldenZeroSectorLift_snd`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `GoldenZeroSectorDescentPacket.coprime_D_s`
- `goldenUnit_of_norm_eq_one_or_neg_one`

The main visible Mathlib APIs are:

- `Int.dvd_natCast.mp`
- `Int.dvd_neg.mp`
- `Int.natCast_natAbs`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.pow_right`
- `Nat.Coprime.mul_right`
- `Nat.eq_one_of_dvd_coprimes`
- `abs_pow`
- `abs_of_nonneg`
- `norm_num`
- `positivity`
- `ring`
- `omega`

## Proof / construction flow

1. Unfold the intended use of `GoldenRelPrime` by introducing a common divisor `z` and the two divisibility assumptions.

   ```lean
   intro z hzAlpha hzConj
   ```

2. A common divisor also divides the difference.

   ```lean
   have hzDiff := goldenDivides_sub hzAlpha hzConj
   ```

3. Map `GoldenDivides` to integer divisibility of norms.

   ```lean
   have hzNormAlpha := goldenNorm_dvd_of_goldenDivides hzAlpha
   have hzNormDiff := goldenNorm_dvd_of_goldenDivides hzDiff
   ```

4. Use `N(alpha)=H(r,s)=D^5` to construct

   ```lean
   hzD : (goldenNorm z).natAbs ∣ p.D ^ 5
   ```

5. Compute the norm of `alpha - conj alpha` and obtain

   ```lean
   hzS : (goldenNorm z).natAbs ∣ 5 * p.base.snd.natAbs ^ 4
   ```

6. From 0382 build

   ```lean
   hD5 : Nat.Coprime (p.D ^ 5) 5
   ```

7. From 0384 build

   ```lean
   hDS : Nat.Coprime (p.D ^ 5) (p.base.snd.natAbs ^ 4)
   ```

8. Combine them using `mul_right`:

   ```lean
   hcop : Nat.Coprime (p.D ^ 5)
     (5 * p.base.snd.natAbs ^ 4)
   ```

9. Since `|N(z)|` divides both coprime numbers, conclude

   ```lean
   have hone : (goldenNorm z).natAbs = 1 :=
     Nat.eq_one_of_dvd_coprimes hcop hzD hzS
   ```

10. Use `omega` to pass from `natAbs = 1` to the norm being `±1`, and close with `goldenUnit_of_norm_eq_one_or_neg_one`.

## Lean-specific processing

### Direct predicate-style proof of `GoldenRelPrime`

The proof starts with

```lean
intro z hzAlpha hzConj
```

so it does not construct a gcd object. It proves the predicate by showing that an arbitrary common divisor is a unit.

### Descending from `GoldenDivides` to integer norm divisibility

`goldenNorm_dvd_of_goldenDivides` turns divisibility in the golden integer ring into divisibility in `ℤ`. This is the main type boundary from abstract ring arithmetic to ordinary arithmetic.

### `Int.dvd_natCast.mp`

Norm divisibility lives over integers, while the final coprimality argument is expressed with `Nat.Coprime`. The proof therefore passes through `natAbs` and natural-number casts to obtain natural divisibility statements.

### `convert ... using 1` and `ring`

When extracting `5*s^4` from the norm of the conjugate difference, the expressions are not definitionally identical, so the proof uses

```lean
convert hzNormDiff using 1
rw [goldenNorm_sub_conj, goldenZeroSectorLift_snd]
ring
```

to normalize the algebraic identity.

### Absolute values and an even power

```lean
have habspow : abs p.base.snd ^ 4 = p.base.snd ^ 4 := by
  rw [← abs_pow]
  exact abs_of_nonneg (by positivity)
```

makes explicit that `s^4 ≥ 0`, so the absolute value can be removed.

### Power transport of coprimality

`Nat.Coprime.pow_left`, `.pow_right`, and `.mul_right` lift

$$
\gcd(D,|s|)=1
$$

and

$$
5\nmid D
$$

to the exact form

$$
\gcd(D^5,5|s|^4)=1
$$

needed by the common-divisor argument.

## Redundancy and duplication

The proof is long, but mathematically it has one line of argument: the norm of a common divisor divides two coprime natural numbers, so its absolute norm is 1. Most local `have`s exist to make representation changes explicit.

The main possible duplication is around `hzD` and `hzS`, where `Int.dvd_natCast.mp` is used to move norm divisibility to natural-number `natAbs` divisibility. If this pattern occurs repeatedly, a helper such as

```lean
lemma natAbs_goldenNorm_dvd_of_goldenDivides ...
```

could be justified.

Likewise, `hD5`, `hDS`, and `hcop` could be packaged as packet-level lemmas if reused later. If they are local to this argument, the present local `have` structure keeps the public API smaller.

## Optimization candidates

1. **Factor the Nat form of norm divisibility into a helper**

   This is useful if the chain `GoldenDivides → norm divisibility → natAbs divisibility` repeats elsewhere.

2. **Consider a dedicated norm-of-lift-minus-conjugate lemma**

   The current proof combines

   ```lean
   goldenNorm_sub_conj
   goldenZeroSectorLift_snd
   ring
   ```

   A dedicated zero-sector lemma equivalent to

   ```lean
   goldenNorm_lift_sub_conj :
     goldenNorm (T x - conj (T x)) = -(5 * x.snd ^ 4)
   ```

   would shorten this theorem. If the identity is used only here, however, keeping it local avoids unnecessary API growth.

3. **Keep the existing final unit conversion**

   Using `omega` plus `goldenUnit_of_norm_eq_one_or_neg_one` is cleaner than manually splitting the cases `N(z)=1` and `N(z)=-1`.

4. **Preserve the 0382/0384 packet APIs**

   The theorem correctly reuses `five_not_dvd_D` and `coprime_D_s` instead of reproving their arithmetic content locally.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The visible Mathlib requirements of this theorem are integer and natural divisibility/coprimality, prime APIs, absolute values, powers, and the tactics `ring`, `norm_num`, `positivity`, and `omega`.

A narrower import set is likely possible, but this run does not perform a Lean build, so the exact minimal Mathlib module set has not been verified. Therefore no specific minimal import list is asserted.

On the project side, the theorem requires the golden divisibility APIs, norm/conjugation APIs, the packet and quadratic lift from `SignedGoldenZeroSectorDescent`, and the preceding 0382/0384 results. In the standalone artifact these appear through the ordered source modules listed in the manifest header.

## Comparator challenge suitability

**Highly suitable.**

0385 is not a one-line API application. It crosses several representation layers, making it a strong medium-sized Comparator challenge.

Useful evaluation points include whether a model can:

- read the `GoldenRelPrime` goal as a common-divisor-to-unit problem,
- notice that a common divisor also divides the difference,
- descend from `GoldenDivides` to norm divisibility,
- obtain divisibility by `D^5` from `H_eq`,
- normalize the conjugate-difference norm to `5*s^4`,
- lift `five_not_dvd_D` and `coprime_D_s` to power coprimality,
- select `Nat.eq_one_of_dvd_coprimes`,
- and close the argument by converting norm `±1` to a unit.

The route

$$
\text{golden ring}
\to \text{integer norm}
\to \text{natural coprimality}
\to \text{golden unit}
$$

makes it particularly useful as an API-selection benchmark rather than merely a tactic benchmark.

A smaller challenge could provide `hzD`, `hzS`, and `hcop` as assumptions and test only the final `Nat.eq_one_of_dvd_coprimes` and unit conversion. The full version better measures the design of the actual theorem.

## Next declaration to read

The next declaration is `five_dvd_norm_of_nonzero_goldenUnitSector`, also a `theorem`.

```lean
theorem five_dvd_norm_of_nonzero_goldenUnitSector
    {alpha gamma : GoldenInt} {i : Fin 5}
    (hi : i ≠ 0)
    (hAlpha : alpha =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5))
    (hFive : (5 : ℤ) ∣ alpha.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

The source temporarily leaves the `GoldenZeroSectorDescentPacket` namespace before this packet-independent theorem.

After 0385 establishes relative primality of the re-entry element and its conjugate, the later `exists_lift_eq_fifthPower` can use coprime fifth-power factorization to reach a unit-sector expression of the form

$$
T(r,s)=\varphi^i\theta^5.
$$

The next theorem proves that if the sector is nonzero (`i ≠ 0`) and the second coordinate is divisible by 5, then

$$
5\mid N(\theta).
$$

This prepares the exclusion of every nonzero unit sector by contradiction with the packet's five-adic cleanliness.
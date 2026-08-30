# 0281 — `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split`

## Declaration kind

This is a **`theorem`**.

For a zero-sector fifth-power base `gamma : GoldenInt`, it completely separates the factor `5^6` occurring in the natural absolute value of the second coordinate and proves that the remaining second-coordinate factor and the quartic factor are both tenth powers.

## Lean type

```lean
/--
The coprime zero-sector product splits exactly: all six factors of five lie in
the second coordinate, and the remaining coprime factors are tenth powers.
-/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ∃ c d : ℕ,
      gamma.snd.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = d ^ 10 := by
  let H := (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
  have hprod : gamma.snd.natAbs * H =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    simpa [H] using p.zeroSector_natAbs_product_eq hbeta
  have h5H : ¬ 5 ∣ H := by
    intro h
    apply p.zeroSector_five_not_dvd_sndFactor hbeta
    apply Int.natCast_dvd.mpr
    simpa [H] using h
  have hcop5H : Nat.Coprime (5 ^ 6) H :=
    (Nat.Coprime.pow_left 6
      ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5H))
  have h5dvdProduct : 5 ^ 6 ∣ gamma.snd.natAbs * H := by
    rw [hprod]
    exact dvd_mul_right (5 ^ 6) _
  have h5dvdS : 5 ^ 6 ∣ gamma.snd.natAbs :=
    hcop5H.dvd_of_dvd_mul_right h5dvdProduct
  rcases h5dvdS with ⟨t, ht⟩
  have htProduct : t * H = p.exceptional.powerSplit.a ^ 10 := by
    rw [ht] at hprod
    rw [mul_assoc] at hprod
    exact Nat.mul_left_cancel (by positivity) hprod
  have htDvdS : t ∣ gamma.snd.natAbs := by
    rw [ht]
    exact dvd_mul_left t (5 ^ 6)
  have hcopTH : Nat.Coprime t H :=
    (p.zeroSector_coprime_s_sndFactor hbeta).of_dvd_left htDvdS
  have hunit : IsUnit (gcd t H) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopTH
  obtain ⟨c, hc⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit htProduct
  have hunit' : IsUnit (gcd H t) := by
    simpa [gcd_comm] using hunit
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using htProduct)
  exact ⟨c, d, by simpa [hc] using ht, hd⟩
```

Write `gamma = (r,s)` and let `H` denote the natural absolute value of

```lean
goldenFifthSndFactor r s.
```

Then the conclusion is

$$
|s|=5^6c^{10},
\qquad
H=d^{10}.
$$

## Mathematical meaning

The preceding zero-sector results have already established

$$
|s|H=5^6a^{10}.
$$

They also prove

$$
5\nmid H,
\qquad
\gcd(|s|,H)=1.
$$

From `5 ∤ H`, one gets

$$
\gcd(5^6,H)=1.
$$

Yet `5^6` divides the product `|s|H`. Coprimality therefore forces all six factors of five into the `|s|` side:

$$
5^6\mid |s|.
$$

Hence there is some `t : ℕ` such that

$$
|s|=5^6t.
$$

Substituting this into the product equation and cancelling the positive factor `5^6` gives

$$
tH=a^{10}.
$$

Moreover, `t | |s|` together with `gcd(|s|,H)=1` implies

$$
\gcd(t,H)=1.
$$

The product of two coprime natural numbers is thus a tenth power. Since no prime factor can be shared between the two factors, every prime exponent occurring in either factor must itself be divisible by ten. Consequently,

$$
t=c^{10},
\qquad
H=d^{10},
$$

and therefore

$$
|s|=5^6c^{10},
\qquad
H=d^{10}.
$$

Thus this theorem is stronger than a mere divisibility statement: it determines the prime-factor ownership in the zero-sector product exactly.

## Role in the overall proof

Declarations 0275 through 0280 progressively prepare the second-coordinate equation. Starting from

$$
sH(r,s)=-5^6a^{10},
$$

0278 passes to natural absolute values and obtains

$$
|s||H|=5^6a^{10}.
$$

Declaration 0277 supplies `5 ∤ H`, while 0279 and 0280 establish the primitive and coprimality conditions. The present theorem 0281 combines these ingredients into the normal form required directly by the subsequent inversion layer:

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}.
$$

This theorem is the final declaration of the generated source `SignedGoldenZeroSector.lean`. The next generated source, `SignedGoldenZeroSectorInversion.lean`, changes coordinates by introducing

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5.
$$

Thus 0281 lies exactly at the **boundary between zero-sector arithmetic and inversion geometry**.

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq` (0278)

```lean
gamma.snd.natAbs *
    (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
  5 ^ 6 * p.exceptional.powerSplit.a ^ 10
```

This provides the product equation on which the theorem is based.

### `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor` (0277)

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

The proof transports this statement through `Int.natCast_dvd` to obtain `5 ∤ H` for the natural absolute value.

### `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor` (0280)

```lean
Nat.Coprime gamma.snd.natAbs
  (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
```

This gives the coprimality of `|s|` and `H`; since `t | |s|`, it descends to `gcd(t,H)=1`.

### `Nat.Coprime.dvd_of_dvd_mul_right`

From `gcd(5^6,H)=1` and `5^6 | |s|H`, this extracts `5^6 | |s|`.

### `exists_eq_pow_of_mul_eq_pow`

This is the generic GCDMonoid lemma saying, in the required direction, that if a product is a power and the relevant gcd is a unit, then one factor is itself a power of the same exponent. The theorem invokes it twice, reversing the two factors for the second use.

## Proof / construction flow

### 1. Abbreviate the quartic factor by `H`

```lean
let H := (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
```

This local abbreviation keeps the subsequent natural-number factorization readable.

### 2. Rewrite the product equation using `H`

```lean
have hprod : gamma.snd.natAbs * H =
    5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  simpa [H] using p.zeroSector_natAbs_product_eq hbeta
```

### 3. Transport `5 ∤ H` from the integer theorem 0277

```lean
have h5H : ¬ 5 ∣ H := by
  intro h
  apply p.zeroSector_five_not_dvd_sndFactor hbeta
  apply Int.natCast_dvd.mpr
  simpa [H] using h
```

This is the type boundary between factorization in `ℕ` via `natAbs` and the quartic polynomial defined over `ℤ`.

### 4. Build coprimality of `5^6` and `H`

```lean
have hcop5H : Nat.Coprime (5 ^ 6) H :=
  (Nat.Coprime.pow_left 6
    ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5H))
```

The proof first obtains coprimality of the prime `5` with `H`, then raises the left factor to the sixth power.

### 5. Force `5^6` into the `|s|` factor

```lean
have h5dvdS : 5 ^ 6 ∣ gamma.snd.natAbs :=
  hcop5H.dvd_of_dvd_mul_right h5dvdProduct
rcases h5dvdS with ⟨t, ht⟩
```

Here `ht` represents `|s| = 5^6 * t`.

### 6. Cancel `5^6` and obtain `tH=a^10`

```lean
have htProduct : t * H = p.exceptional.powerSplit.a ^ 10 := by
  rw [ht] at hprod
  rw [mul_assoc] at hprod
  exact Nat.mul_left_cancel (by positivity) hprod
```

The positivity of `5^6` is discharged by `positivity` before natural-number left cancellation.

### 7. Inherit coprimality for `t` and `H`

```lean
have htDvdS : t ∣ gamma.snd.natAbs := by
  rw [ht]
  exact dvd_mul_left t (5 ^ 6)
have hcopTH : Nat.Coprime t H :=
  (p.zeroSector_coprime_s_sndFactor hbeta).of_dvd_left htDvdS
```

The coprimality from 0280 descends from `|s|` to its divisor `t`.

### 8. Convert to the generic GCDMonoid API

```lean
have hunit : IsUnit (gcd t H) := by
  simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopTH
```

Mathlib's `exists_eq_pow_of_mul_eq_pow` is formulated generically in terms of the gcd being a unit rather than directly in terms of `Nat.Coprime`, so this conversion is required.

### 9. Extract both tenth powers

```lean
obtain ⟨c, hc⟩ :=
  exists_eq_pow_of_mul_eq_pow hunit htProduct
```

gives `t = c^10`. The proof then reverses the gcd and product,

```lean
obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
  (by simpa [mul_comm] using htProduct)
```

and obtains `H = d^10`.

### 10. Assemble the final normal form

```lean
exact ⟨c, d, by simpa [hc] using ht, hd⟩
```

## Lean-specific processing

The distinctive feature of this proof is not difficult polynomial algebra but the **conversion between library interfaces**.

`Int.natCast_dvd` connects non-divisibility over `ℤ` with factorization over the `natAbs : ℕ` representation. `Nat.Coprime.pow_left` lifts coprimality from `5` to `5^6`, and `Nat.Coprime.dvd_of_dvd_mul_right` decides which coprime factor owns the entire prime-power contribution.

The conversion from `Nat.Coprime` to

```lean
IsUnit (gcd t H)
```

is particularly Lean-specific. It adapts a natural-number statement to Mathlib's generic GCDMonoid theorem. `gcd_eq_nat_gcd`, `Nat.isUnit_iff`, `gcd_comm`, and `mul_comm` are mathematically routine representation changes, but they are needed to match the generic theorem's exact input shape.

## Redundancy and duplication

The clearest duplication is the two symmetric calls to `exists_eq_pow_of_mul_eq_pow`:

```lean
have hunit : IsUnit (gcd t H) := ...
obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow hunit htProduct
have hunit' : IsUnit (gcd H t) := by
  simpa [gcd_comm] using hunit
obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
  (by simpa [mul_comm] using htProduct)
```

Mathematically this is one symmetric fact: if two coprime factors have an `n`-th-power product, then both factors are `n`-th powers. The current Mathlib API returns the needed existence one side at a time, so the proof explicitly swaps the factors.

By contrast, the local abbreviation `H` and the explicit step moving `5^6` wholly into `|s|` expose the factor-ownership structure clearly and are probably better kept than compressed away.

## Optimization candidates

### 1. Symmetric coprime-product power-split helper

A natural-number helper of the form

```lean
Nat.Coprime x y → x * y = z ^ n →
  ∃ a b, x = a ^ n ∧ y = b ^ n
```

would hide the conversion to `IsUnit (gcd ...)`, the use of `gcd_comm`, and the duplicate calls to the generic theorem.

### 2. Prime-power ownership helper

The step from `Nat.Coprime (5^6) H` and `5^6 | s*H` to `5^6 | s` is a reusable prime-power ownership pattern. If the same shape appears elsewhere in the development, a generic helper could make the intended valuation structure more explicit.

### 3. Localize the `ℤ`/`ℕ` boundary

A `natAbs` version of `zeroSector_five_not_dvd_sndFactor` would remove the `Int.natCast_dvd` conversion from this theorem. That would only be worthwhile if the natural-number form is reused elsewhere, since otherwise it merely increases the API surface.

## Required Mathlib imports and import optimization

The repository's canonical standalone file `Flt5DkMath/FLT5StandAlone.lean` actually uses

```lean
import Mathlib
```

so **`Mathlib` is the import verified directly from the repository**.

The proof itself uses Mathlib facilities for natural-number primality, coprimality and divisibility, GCDMonoid `gcd` and `exists_eq_pow_of_mul_eq_pow`, integer cast/divisibility lemmas, and tactics such as `norm_num` and `positivity`.

A narrower import set is very likely possible. However, no Lean build or import bisection was performed in this run, so no specific smaller module list can be asserted as the verified minimum. The import-optimization candidate is to replace the umbrella `Mathlib` import with the individual modules supplying those APIs and then validate that change with a separate build.

## Comparator challenge suitability

**Suitable; medium to moderately high difficulty.**

A particularly clean challenge can remove the packet-specific setup and expose the following natural-number core:

```lean
hprod : s * H = 5 ^ 6 * a ^ 10
h5H   : ¬ 5 ∣ H
hcop  : Nat.Coprime s H
⊢ ∃ c d, s = 5 ^ 6 * c ^ 10 ∧ H = d ^ 10
```

This tests theorem/API selection rather than only `ring` or `omega`:

- coprime ownership of a prime power,
- inheritance of coprimality by divisors,
- conversion between `Nat.Coprime` and the generic GCDMonoid API,
- splitting a coprime product that is an exact power.

For a stronger Comparator exercise, one version can allow `exists_eq_pow_of_mul_eq_pow`, while a second version can require reconstructing the result from prime-exponent reasoning.

## Relation to the PDFs

The repository tree on the target branch confirms the presence of the Japanese PDF

```text
docs/pdf/FLT5-main-ja-v0-r1.pdf
```

and the English PDF

```text
docs/pdf/FLT5-main-en-v0-r1.pdf.
```

However, in this run the binary PDF contents could not be obtained in an analyzable form. Therefore the exact page number, section correspondence, and any verbatim alignment of 0281 with the PDF text are **unverified** and are not guessed here. The technical content and Lean code in this explanation are grounded primarily in the branch's canonical `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is **0282 `zeroSectorX`**, whose kind is `def`:

```lean
/-- The diagonal coordinate `X = 2*r+s`. -/
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

Once the tenth-power split is completed in 0281, the generated source `SignedGoldenZeroSector.lean` ends. The immediately following `SignedGoldenZeroSectorInversion.lean` begins by introducing the diagonal coordinate

$$
X=2r+s.
$$

The subsequent declarations construct

$$
U=X^2+5s^2,
\qquad
W=4d^5,
\qquad
A=U-W,
\qquad
B=U+W,
$$

and transform the quartic factor into an inversion/factorization form. Thus 0282 is the first declaration in the transition from the factorization arithmetic completed by 0281 to the next coordinate-based algebraic layer.

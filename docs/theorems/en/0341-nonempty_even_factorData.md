# 0341 — `nonempty_even_factorData`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem nonempty_even_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  let Q2 : ℕ := 5 ^ 5 * 2 ^ 7 * k ^ 8
  have hQ : zeroSectorQ p.source.c = 2 * Q2 := by
    unfold zeroSectorQ Q2
    rw [hk]
    ring
  have hQ2Even : Even Q2 := by
    rw [even_iff_two_dvd]
    dsimp [Q2]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (by norm_num : 2 ∣ 2 ^ 7) (5 ^ 5)) _
  obtain ⟨A1, B1, hA8, hB8, hparity⟩ := p.even_factor_eighths hc
  rcases hparity with ⟨hAodd, hBeven⟩ | ⟨hAeven, hBodd⟩
  · rcases even_iff_two_dvd.mp hBeven with ⟨B2, hB2⟩
    have hcop : Nat.Coprime A1 B2 := by
      apply coprime_of_odd_of_no_common_odd_prime hAodd
      intro q hq hq2 hqA1 hqB2
      apply p.no_common_odd_prime q hq hq2
      · rw [hA8]
        exact dvd_mul_of_dvd_right hqA1 8
      · rw [hB8, hB2]
        exact Nat.dvd_mul_left_of_dvd
          (Nat.dvd_mul_left_of_dvd hqB2 2) 8
    have hred : A1 * B2 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A1 * B2) = p.source.A0 * p.source.B0 := by
          rw [hA8, hB8, hB2]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hB2, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have heOdd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A1 * B2 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have hfEven : Even f := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact (heOdd.not_two_dvd_nat h2e).elim
      · exact even_iff_two_dvd.mpr h2f
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hB8, hB2, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenLeftLow e f hePos hfPos hef hefd heOdd hfEven
      (by rw [hA8, he]) (by rw [hB8, hB2, hf]; ring)
      hownership hdiff⟩
  · rcases even_iff_two_dvd.mp hAeven with ⟨A2, hA2⟩
    have hcop : Nat.Coprime A2 B1 := by
      have hcop' : Nat.Coprime B1 A2 := by
        apply coprime_of_odd_of_no_common_odd_prime hBodd
        intro q hq hq2 hqB1 hqA2
        apply p.no_common_odd_prime q hq hq2
        · rw [hA8, hA2]
          exact Nat.dvd_mul_left_of_dvd
            (Nat.dvd_mul_left_of_dvd hqA2 2) 8
        · rw [hB8]
          exact dvd_mul_of_dvd_right hqB1 8
      exact hcop'.symm
    have hred : A2 * B1 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A2 * B1) = p.source.A0 * p.source.B0 := by
          rw [hA8, hA2, hB8]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, hA2, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have hfOdd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A2 * B1 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have heEven : Even e := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact even_iff_two_dvd.mpr h2e
      · exact (hfOdd.not_two_dvd_nat h2f).elim
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hA2, hB8, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenRightLow e f hePos hfPos hef hefd heEven hfOdd
      (by rw [hA8, hA2, he]; ring) (by rw [hB8, hf])
      hownership hdiff⟩
```

## Lean type

The theorem has type

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
Nonempty (GoldenZeroSectorFactorData p)
```

`GoldenZeroSectorFactorData p` is a dependent inductive type indexed by `p`. The theorem proves that whenever `p.source.c` is even, that type is inhabited. It returns `Nonempty` rather than a bare datum because the following layer only needs existence before selecting one witness with `Classical.choice`.

## Mathematical statement

In the even branch, theorem 0340 gives

$$
p.source.A0 = 8A_1,
\qquad
p.source.B0 = 8B_1,
$$

with $A_1$ and $B_1$ of opposite parity.

Since $c$ is even, write $c=2k$. The proof defines

$$
Q_2 := 5^5 2^7 k^8
$$

and rewrites

$$
\operatorname{zeroSectorQ}(c)=2Q_2.
$$

The quantity $Q_2$ is itself even.

Two cases remain.

### 1. $A_1$ odd and $B_1$ even

Write $B_1=2B_2$. The proof establishes

$$
\gcd(A_1,B_2)=1
$$

and, from the factor-product identity,

$$
A_1B_2=Q_2^5.
$$

Applying `fifth_power_factor_split` gives

$$
A_1=e^5,
\qquad
B_2=f^5.
$$

Hence

$$
A_0=8e^5,
\qquad
B_0=16f^5.
$$

The root $e$ is odd. Since $ef=Q_2$ is even, primality of 2 together with the oddness of $e$ forces $f$ to be even. The factor-difference identity then becomes

$$
e^5+d^5=2f^5.
$$

These data build `GoldenZeroSectorFactorData.evenLeftLow`.

### 2. $A_1$ even and $B_1$ odd

Write $A_1=2A_2`. Symmetrically,

$$
\gcd(A_2,B_1)=1,
\qquad
A_2B_1=Q_2^5,
$$

so

$$
A_2=e^5,
\qquad
B_1=f^5.
$$

Therefore

$$
A_0=16e^5,
\qquad
B_0=8f^5,
$$

with $e$ even and $f$ odd, and the difference equation becomes

$$
2e^5+d^5=f^5.
$$

These data build `GoldenZeroSectorFactorData.evenRightLow`.

## Role in the full proof

This theorem is the main constructor for the even branch between zero-sector inversion and the exact factor packet.

Theorem 0339 extracts a common factor $2^3$ from $A_0,B_0`; theorem 0340 then proves that the quotients have opposite parity. The present theorem uses that parity information to remove **one additional factor of 2 from the even quotient**. That extra factor produces the asymmetric coefficient patterns

$$
(8,16)
\quad\text{or}\quad
(16,8),
$$

which are exactly the two dependent constructors `evenLeftLow` and `evenRightLow`.

Thus 0341 upgrades the coarse statement “the source is in the even branch” into a complete proof-carrying factor certificate suitable for the later descent.

## Direct dependencies

The principal direct dependencies are:

- `GoldenZeroSectorInversionPacket.even_factor_eighths`
- `GoldenZeroSectorInversionPacket.no_common_odd_prime`
- `GoldenZeroSectorInversionPacket.factor_product`
- `GoldenZeroSectorInversionPacket.factor_difference`
- `GoldenZeroSectorInversionPacket.A0_pos`
- `GoldenZeroSectorInversionPacket.B0_pos`
- `GoldenZeroSectorInversionPacket.coprime_Q_d`
- `GoldenZeroSectorFactorData.evenLeftLow`
- `GoldenZeroSectorFactorData.evenRightLow`
- `zeroSectorQ`
- `coprime_of_odd_of_no_common_odd_prime`
- `fifth_power_factor_split`
- `even_iff_two_dvd`
- `Nat.Prime.dvd_mul`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `dvd_pow_self`

The mathematical center is `fifth_power_factor_split`: if two coprime factors multiply to a fifth power, each factor is itself a fifth power.

## Proof flow

The proof proceeds as follows.

1. Extract $c=2k$ from `hc : Even c`.
2. Define $Q_2=5^5 2^7 k^8`; prove `zeroSectorQ c = 2 * Q2` and that $Q_2$ is even.
3. Invoke theorem 0340 to obtain $A_0=8A_1`, $B_0=8B_1`, and opposite parity.
4. Split on the two parity orientations.
5. Divide the even quotient by 2, introducing `B2` or `A2`.
6. Use `no_common_odd_prime` to prove coprimality of the reduced pair.
7. Normalize the factor-product identity with the common coefficient 128 and cancel it to derive a fifth-power product.
8. Apply `fifth_power_factor_split` to obtain fifth-power roots $e,f$.
9. Recover positivity of $e,f$ from `A0_pos` and `B0_pos`.
10. Descend coprimality from $e^5,f^5$ to `Nat.Coprime e f`.
11. Descend oddness from the odd fifth power to the corresponding root with `Nat.odd_pow_iff`.
12. Use injectivity of fifth powers to prove $ef=Q_2$.
13. Since $Q_2$ is even, use primality of 2 to force the remaining root to be even.
14. Recover the ownership equation `2 * (e * f) = zeroSectorQ c`.
15. Rewrite `factor_difference` and let `omega` derive the branch-specific fifth-power equation.
16. Pull `Nat.Coprime (e*f) d` back from `coprime_Q_d`.
17. Construct `.evenLeftLow` or `.evenRightLow`.

## Lean-specific processing

### Existence packaged as `Nonempty`

The target

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

packages the constructed dependent datum with `⟨...⟩`. This is precisely the interface needed by the following `nonempty_factorData` theorem and then by `Classical.choice`.

### Local definition `Q2`

`Q2` is introduced with `let`, and `hQ` uses

```lean
unfold zeroSectorQ Q2
```

before `ring` closes the polynomial identity.

### Explicit divisibility witnesses

`even_iff_two_dvd.mp` converts parity into divisibility and exposes quotient witnesses `B2` or `A2` directly.

### Cancellation of 128

The reduced product is proved by

```lean
apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
```

because $8\cdot16=128$ is the common normalization coefficient in both orientations.

### Injectivity of fifth powers

Instead of manipulating `e * f = Q2` directly, the proof applies

```lean
Nat.pow_left_injective (by decide : 5 ≠ 0)
```

and compares fifth powers using `hred` and `mul_pow`.

### Descending parity through a power

From `A1=e^5` and `Odd A1`, the proof obtains `Odd e` through

```lean
Nat.odd_pow_iff
```

and symmetrically obtains `Odd f` in the other branch.

### Division of labor between `ring` and `omega`

`ring` handles polynomial and coefficient normalization. `omega` is used only after rewriting the nonlinear fifth powers into atomic terms in a linear natural-number equality; it is not expanding the fifth powers themselves.

## Redundancy and duplication

The two parity branches are strongly symmetric. The following blocks are nearly duplicated:

- coprimality of the reduced pair,
- construction of `hred`,
- positivity of `e,f`,
- recovery of root-level coprimality,
- proof of `ef = Q2`,
- determination of the even root,
- construction of ownership,
- recovery of `coprime_ef_d`.

The differences are the ordering of `A1/B2` versus `A2/B1`, the location of the odd root, and the final constructor. Fully deduplicating the proof would therefore require an explicit abstraction for branch orientation.

## Optimization candidates

The clearest optimization would be a common reduced-even-factor lemma parameterized by the orientation. Given an odd factor, an even factor written as twice a reduced factor, the product relation, and the source embeddings, such a lemma could return

$$
O=e^5,
\qquad
E_2=f^5,
\qquad
\gcd(e,f)=1,
\qquad
ef=Q_2.
$$

Then the body of 0341 would mainly handle orientation, parity of the remaining root, and the final difference equation.

The repeated `hePos` / `hfPos` arguments may also be abstractable into a general lemma saying that a positive positive-coefficient multiple of a fifth power has a positive root.

On the other hand, the current duplication keeps the left/right mathematical symmetry explicit, which is useful in a theorem-museum setting.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The Mathlib facilities visibly used by this theorem include at least:

- `Even`, `Odd`, `even_iff_two_dvd`
- `Nat.Coprime`
- `Nat.Prime.dvd_mul`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `Nat.eq_zero_of_not_pos`
- `Nat.mul_left_cancel`
- `dvd_pow_self`
- `norm_num`
- `ring`
- `omega`

The original per-module import list is not determined from this generated standalone excerpt, and no Lean build is performed in this task. Therefore the **minimal import set is not confirmed**. Replacing `import Mathlib` with narrower imports is a plausible optimization, but it should be validated separately by an import audit and Lean build.

## Comparator challenge suitability

**Yes; it is particularly suitable as an intermediate-to-advanced challenge.**

Two useful challenge cuts are possible:

1. Given `even_factor_eighths` and the product relation, prove that the appropriate reduced product is a fifth power.
2. Give `fifth_power_factor_split` as an available lemma and require the solver to recover parity, ownership, the difference equation, and finally construct `.evenLeftLow` or `.evenRightLow`.

The second version exercises dependent constructors, divisibility, coprimality, parity, `omega`, `ring`, and power injectivity in one realistic proof-refactoring task.

## Next declaration to read

The next declaration is **0342 `nonempty_factorData`**, again a **`private theorem`**.

```lean
private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc
```

With both odd and even exact-factor constructors now available, 0342 simply routes on `Nat.even_or_odd p.source.c` and removes the parity hypothesis altogether, yielding unconditional inhabitation of `GoldenZeroSectorFactorData p`.
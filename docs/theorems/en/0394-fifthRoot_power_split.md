# 0394 `GoldenZeroSectorDescentPacket.fifthRoot_power_split`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma splits the second coordinate of the fifth root `gamma : GoldenInt` and its quartic factor back into fifth powers, recovering the recursive shape required by the zero-sector descent.

## Lean code

```lean
theorem fifthRoot_power_split
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ∃ u v : ℕ,
      0 < u ∧ 0 < v ∧
      gamma.snd = 5 * (u : ℤ) ^ 5 ∧
      goldenFifthSndFactor gamma.fst gamma.snd = (v : ℤ) ^ 5 := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hAbs := congrArg Int.natAbs hEq
  have hNatEq :
      p.base.snd.natAbs ^ 2 =
        5 * gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    simpa [Int.natAbs_pow, Int.natAbs_mul] using hAbs
  have hProduct :
      gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        5 * (p.t ^ 2) ^ 5 := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    calc
      5 * (gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) =
          p.base.snd.natAbs ^ 2 := by
        rw [hNatEq]
        ring
      _ = (5 * p.t ^ 5) ^ 2 := by rw [p.snd_natAbs_eq]
      _ = 5 * (5 * (p.t ^ 2) ^ 5) := by ring
  have hFiveNotH :
      ¬ 5 ∣ (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    intro h
    exact p.fifthRoot_five_not_dvd_H gamma hnorm
      (Int.natCast_dvd.mpr h)
  have hFiveN : 5 ∣ gamma.snd.natAbs := by
    have hFiveProduct : 5 ∣
        gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
      rw [hProduct]
      exact dvd_mul_right 5 _
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp hFiveProduct with h | h
    · exact h
    · exact (hFiveNotH h).elim
  rcases hFiveN with ⟨n0, hn0⟩
  have hn0Eq :
      n0 * (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        (p.t ^ 2) ^ 5 := by
    rw [hn0] at hProduct
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    simpa [mul_assoc] using hProduct
  have hrootCoprime := p.fifthRoot_coprime_coords gamma hroot hnorm
  have hcopNH := coprime_natAbs_goldenFifthSndFactor_of_coprime
    gamma.fst gamma.snd hrootCoprime
  have hn0Dvd : n0 ∣ gamma.snd.natAbs := by
    rw [hn0]
    exact dvd_mul_left n0 5
  have hcopN0H : Nat.Coprime n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs :=
    hcopNH.of_dvd_left hn0Dvd
  have hunit : IsUnit (gcd n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopN0H
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hn0Eq
  have hunit' : IsUnit (gcd
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs n0) := by
    simpa [gcd_comm] using hunit
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using hn0Eq)
  have huPos : 0 < u := by
    by_contra hu0
    have huZero : u = 0 := Nat.eq_zero_of_not_pos hu0
    have hnZero : gamma.snd.natAbs = 0 := by simp [hn0, hu, huZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hn)) hnZero
  have hvPos : 0 < v := by
    by_contra hv0
    have hvZero : v = 0 := Nat.eq_zero_of_not_pos hv0
    have hHZero :
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = 0 := by
      simp [hv, hvZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hH)) hHZero
  refine ⟨u, v, huPos, hvPos, ?_, ?_⟩
  · have hcast : (gamma.snd.natAbs : ℤ) = 5 * (u : ℤ) ^ 5 := by
      exact_mod_cast (by rw [hn0, hu])
    rw [Int.ofNat_natAbs_of_nonneg hn.le] at hcast
    exact hcast
  · have hcast :
        ((goldenFifthSndFactor gamma.fst gamma.snd).natAbs : ℤ) =
          (v : ℤ) ^ 5 := by exact_mod_cast hv
    rw [Int.ofNat_natAbs_of_nonneg hH.le] at hcast
    exact hcast
```

## Lean type

Conceptually, the theorem has the following type.

```lean
GoldenZeroSectorDescentPacket.fifthRoot_power_split :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  goldenNorm gamma = (p.D : ℤ) →
  ∃ u v : ℕ,
    0 < u ∧ 0 < v ∧
    gamma.snd = 5 * (u : ℤ) ^ 5 ∧
    goldenFifthSndFactor gamma.fst gamma.snd = (v : ℤ) ^ 5
```

The inputs are the descent packet `p`, the fifth root `gamma`, the fifth-power identity `hroot`, and the norm identification `hnorm`. The output is a pair of positive natural numbers `u,v` together with the exact power splitting

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})=v^5.
$$

## Mathematical statement

Write

$$
b=\gamma_{\mathrm{snd}},
\qquad
H=H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}),
\qquad
s=p.base.snd.
$$

From 0388,

$$
s^2=5bH.
$$

The packet also stores

$$
|s|=5t^5.
$$

Taking absolute values therefore gives

$$
|s|^2=5|b||H|
$$

and

$$
|s|^2=(5t^5)^2=25t^{10}.
$$

After cancelling one factor of 5,

$$
|b||H|=5(t^2)^5.
$$

By 0392, $5\nmid H$, so the prime 5 must belong to the $|b|$ factor. Hence

$$
|b|=5n_0
$$

for some $n_0$, and

$$
n_0|H|=(t^2)^5.
$$

From the coordinate primitivity proved in 0391, the existing lemma `coprime_natAbs_goldenFifthSndFactor_of_coprime` yields

$$
\gcd(|b|,|H|)=1.
$$

Since $n_0\mid |b|$, it follows that

$$
\gcd(n_0,|H|)=1.
$$

A product of two coprime factors is a fifth power only if both factors are fifth powers, so

$$
n_0=u^5,
\qquad
|H|=v^5.
$$

Finally, positivity from 0389 and 0390 removes the absolute values and gives

$$
b=5u^5,
\qquad
H=v^5.
$$

## Role in the full proof

Whereas 0393 `fifthRoot_measure_lt` supplies the **strict decrease**, 0394 supplies the **preservation of the recursive shape**.

After 0387 extracts a fifth root `gamma` from the quadratic lift of the source packet, 0388–0392 recover the sign, coprimality, and 5-adic conditions needed for `gamma` to serve as the base of the next zero-sector packet. The present theorem then turns the product identity back into the exact power form required by packet construction:

$$
5u^5\cdot v^5.
$$

Thus the two ingredients needed for infinite descent,

$$
\text{the same structural invariants},
\qquad
\text{a strictly smaller measure},
$$

are divided cleanly between 0394 and 0393 respectively.

## Direct dependencies

The main direct dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenNorm`
- `goldenFifthSndFactor`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`
- `GoldenZeroSectorDescentPacket.snd_natAbs_eq`
- `coprime_natAbs_goldenFifthSndFactor_of_coprime`
- `exists_eq_pow_of_mul_eq_pow`
- `Int.natAbs_pow`
- `Int.natAbs_mul`
- `Int.natCast_dvd`
- `Int.ofNat_natAbs_of_nonneg`
- `Nat.Prime.dvd_mul`
- `Nat.Coprime.of_dvd_left`
- `Nat.mul_left_cancel`
- `gcd_eq_nat_gcd`

In particular, `exists_eq_pow_of_mul_eq_pow` is the abstract engine that converts a coprime product equal to a fifth power into a fifth power for each factor.

## Proof / construction flow

1. Obtain $b>0$ and $H>0$ from 0390 and 0389.
2. Apply `Int.natAbs` to the integer identity from 0388 and obtain the natural-number identity `hNatEq`.
3. Use the packet field `snd_natAbs_eq` to derive
   $$
   |b||H|=5(t^2)^5,
   $$
   recorded as `hProduct`.
4. Transfer 0392 through `Int.natCast_dvd` to get $5\nmid |H|$.
5. Use primality of 5 and `hProduct` to force $5\mid |b|`, and write $|b|=5n_0$.
6. Cancel 5 to obtain
   $$
   n_0|H|=(t^2)^5.
   $$
7. Use 0391 to obtain coprimality with the quartic factor and shrink its left argument from $|b|$ to $n_0$.
8. Convert the gcd to a unit condition and apply `exists_eq_pow_of_mul_eq_pow` in both orders, obtaining $n_0=u^5$ and $|H|=v^5$.
9. If either `u` or `v` were zero, then $|b|=0$ or $|H|=0$; contradict the already established positivity to prove $u,v>0$.
10. Use `exact_mod_cast` and `Int.ofNat_natAbs_of_nonneg` to return from natural-number equalities to the signed integer equalities.

## Lean-specific processing

This proof crosses the `ℤ` / `ℕ` boundary several times. The original algebraic equation lives over integers, while prime-factor splitting and `exists_eq_pow_of_mul_eq_pow` are handled naturally over naturals. The proof therefore first applies `congrArg Int.natAbs` to transport the equation into `ℕ`.

`simpa [Int.natAbs_pow, Int.natAbs_mul]` normalizes absolute values of powers and products. `Int.natCast_dvd.mpr` transports a natural divisibility statement into integers. At the end, `exact_mod_cast` transports the fifth-power equalities back to integers, and `Int.ofNat_natAbs_of_nonneg` removes `natAbs` using positivity.

The conversion from `Nat.Coprime` to `IsUnit (gcd ...)` occurs because `exists_eq_pow_of_mul_eq_pow` is exposed through a gcd-unit hypothesis rather than directly through `Nat.Coprime`.

## Redundancy and duplication

The first half of the proof passes through both `hNatEq` and `hProduct`, performing two stages of normalization of essentially the same product identity. Similar “integer product equation to `natAbs` power product” conversions occur elsewhere in the zero-sector development and could be extracted into a helper lemma.

Likewise, `hunit` and `hunit'` differ only by the order of the gcd arguments. A symmetric or coprime-oriented wrapper around `exists_eq_pow_of_mul_eq_pow` could recover both roots from one coprimality fact without explicitly constructing the second unit proof.

The proofs of `huPos` and `hvPos` are also instances of the generic fact that if a positive integer is a fifth power, then its fifth root is positive.

## Optimization candidates

A useful abstraction would have the shape

```lean
Nat.Coprime a b →
a * b = c ^ 5 →
∃ u v, a = u ^ 5 ∧ b = v ^ 5
```

which would hide `gcd`, `IsUnit`, and `gcd_comm` from this theorem.

An even stronger refactoring could isolate the packet-independent zero-sector arithmetic core:

```lean
|s| = 5 * t ^ 5 →
s ^ 2 = 5 * b * H →
0 < b → 0 < H → ¬ 5 ∣ H →
...
```

This would improve both reuse and Comparator suitability, while leaving 0394 as the orchestration theorem that connects the arithmetic core to the packet API.

## Required Mathlib imports and import optimization

The checked standalone source uses

```lean
import Mathlib
```

for the entire generated file.

The Mathlib facilities used directly here include natural/integer divisibility and coprimality, gcd and `IsUnit`, `natAbs`, casts, and tactics such as `norm_num`, `ring`, and `simp`.

Because this run does not perform a Lean build, the exact minimal replacement for `import Mathlib` is **not verified**. A safe import-minimization pass should first isolate the arithmetic core and then test narrower imports around natural-number gcd/divisibility, integer divisibility/casts, and the tactics actually used.

## Comparator challenge suitability

**Yes, and it is a strong candidate.**

Using the whole theorem directly would retain many DkMath-specific packet dependencies. For Comparator, the arithmetic core is cleaner: from

$$
xy=5z^5,
\qquad
\gcd(x,y)=1,
\qquad
5\nmid y,
$$

derive

$$
x=5u^5,
\qquad
y=v^5.
$$

That formulation isolates ownership of the prime 5, coprime power splitting, and natural-number arithmetic, making alternative Lean proof strategies easy to compare.

## Next declaration to read

Next is **0395 `GoldenZeroSectorStrictDescent`**, whose declaration kind is `structure`.

```lean
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

Immediately after 0393 establishes strict decrease and 0394 recovers the recursive power shape, this structure packages the result into one proof object containing the next packet, fifth-power re-entry, and strict measure decrease. From this point onward the descent can be treated as an iterable certified step rather than merely as a collection of separate lemmas.
# 0338 — `nonempty_odd_factorData`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem nonempty_odd_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  obtain ⟨A1, B1, hA, hAodd, hB, hBodd⟩ := p.odd_factor_halves hc
  have hcop : Nat.Coprime A1 B1 := by
    apply coprime_of_odd_of_no_common_odd_prime hAodd
    intro q hq hq2 hqA1 hqB1
    apply p.no_common_odd_prime q hq hq2
    · rw [hA]
      exact dvd_mul_of_dvd_right hqA1 2
    · rw [hB]
      exact dvd_mul_of_dvd_right hqB1 2
  have hred : A1 * B1 = zeroSectorQ p.source.c ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
    calc
      4 * (A1 * B1) = p.source.A0 * p.source.B0 := by
        rw [hA, hB]
        ring
      _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
  have hePos : 0 < e := by
    by_contra he0
    have : e = 0 := Nat.eq_zero_of_not_pos he0
    have hpos := p.A0_pos
    rw [hA, he, this] at hpos
    norm_num at hpos
  have hfPos : 0 < f := by
    by_contra hf0
    have : f = 0 := Nat.eq_zero_of_not_pos hf0
    have hpos := p.B0_pos
    rw [hB, hf, this] at hpos
    norm_num at hpos
  have hef : Nat.Coprime e f := by
    have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
      simpa [he, hf] using hcop
    exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
      (dvd_pow_self f (by decide))
  have heodd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
  have hfodd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
  have hownership : e * f = zeroSectorQ p.source.c := by
    apply Nat.pow_left_injective (by decide : 5 ≠ 0)
    calc
      (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
      _ = A1 * B1 := by rw [← he, ← hf]
      _ = zeroSectorQ p.source.c ^ 5 := hred
  have hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5 := by
    have hfactorDifference := p.factor_difference
    rw [hA, hB, he, hf] at hfactorDifference
    omega
  exact ⟨.odd e f hePos hfPos hef (hownership ▸ p.coprime_Q_d)
    heodd hfodd (by rw [hA, he]) (by rw [hB, hf]) hownership hdiff⟩
```

Because it is `private`, the theorem name is not exposed as an ordinary public API outside the current source file. Its purpose is to act as an internal construction lemma for the later factor-packet machinery.

## Lean type

Its type is

```lean
(p : GoldenZeroSectorInversionPacket) →
Odd p.source.c →
Nonempty (GoldenZeroSectorFactorData p)
```

Thus, for a zero-sector inversion packet `p`, if the tenth-power base `c` is odd, the dependent inductive type defined in 0334,

```lean
GoldenZeroSectorFactorData p
```

has at least one inhabitant.

The inhabitant constructed at the end is the `.odd ...` constructor. It is not merely an existential pair: it carries proofs of positivity, coprimality, parity, exact fifth-power factorization, ownership, and the branch-specific difference equation.

## Mathematical meaning

The hypothesis is

$$
\operatorname{Odd}(c).
$$

The previously established odd-branch two-adic reduction gives

$$
A_0=2A_1,
\qquad
B_0=2B_1,
$$

with both $A_1$ and $B_1$ odd.

Using the exclusion of a common odd prime factor, the theorem proves

$$
\gcd(A_1,B_1)=1.
$$

The product identity

$$
A_0B_0=4Q^5,
\qquad
Q=5^5c^8
$$

then reduces to

$$
A_1B_1=Q^5.
$$

Since the two factors are coprime and their product is a fifth power, `fifth_power_factor_split` produces

$$
A_1=e^5,
\qquad
B_1=f^5.
$$

From these witnesses the proof recovers

$$
e>0,
\qquad
f>0,
$$

$$
\gcd(e,f)=1,
$$

$$
\operatorname{Odd}(e),
\qquad
\operatorname{Odd}(f),
$$

and

$$
ef=Q.
$$

Finally, the original factor-difference identity yields

$$
e^5+4d^5=f^5,
$$

which supplies the last branch-specific field required by `GoldenZeroSectorFactorData.odd`.

## Role in the FLT5 proof

0334 `GoldenZeroSectorFactorData` only defined the type of exact factor certificates for the three branches. It did not establish that the type is inhabited for a given inversion packet.

This theorem is the **existence constructor for the odd-`c` branch**.

Its structural flow is

```text
GoldenZeroSectorInversionPacket
        │
        ├─ c is odd
        │
        ▼
A0 = 2*A1, B0 = 2*B1
        │
        ▼
Coprime A1 B1
        │
        ▼
A1*B1 = Q^5
        │
        ▼
A1 = e^5, B1 = f^5
        │
        ▼
GoldenZeroSectorFactorData.odd
```

0337 `GoldenZeroSectorFactorPacket` requires

```lean
factors : GoldenZeroSectorFactorData inversion
```

so this `Nonempty` theorem is an internal component used to supply that second field in the odd branch.

## Direct dependencies

### `GoldenZeroSectorInversionPacket.odd_factor_halves`

From

```lean
hc : Odd p.source.c
```

it provides the half-factor decomposition corresponding to

```lean
∃ A1 B1,
  p.source.A0 = 2 * A1 ∧ Odd A1 ∧
  p.source.B0 = 2 * B1 ∧ Odd B1
```

and is the starting point of the construction.

### `coprime_of_odd_of_no_common_odd_prime`

It upgrades oddness plus exclusion of common odd prime divisors to

```lean
Nat.Coprime A1 B1
```

for the reduced factors.

### `GoldenZeroSectorInversionPacket.no_common_odd_prime`

The theorem explained in 0328 forbids a common odd prime divisor of `A0` and `B0`.

Here, divisibility assumptions `q ∣ A1` and `q ∣ B1` are lifted through

$$
A_0=2A_1,
\qquad
B_0=2B_1
$$

to divisibility of both original inversion factors, contradicting `no_common_odd_prime`.

### `GoldenZeroSectorInversionPacket.factor_product`

This supplies

$$
A_0B_0=4Q^5.
$$

### `fifth_power_factor_split`

This existing lemma splits a coprime product that is a fifth power into individual fifth powers.

Applied to

```lean
hcop : Nat.Coprime A1 B1
hred : A1 * B1 = zeroSectorQ p.source.c ^ 5
```

it yields witnesses corresponding to

```lean
A1 = e ^ 5
B1 = f ^ 5
```

### `A0_pos`, `B0_pos`

These positivity facts rule out `e = 0` and `f = 0` after the fifth-power representations have been obtained.

### `GoldenZeroSectorInversionPacket.coprime_Q_d`

The theorem from 0330 gives

$$
\gcd(Q,d)=1.
$$

After rewriting by `hownership : e*f=Q`, it supplies

```lean
Nat.Coprime (e * f) p.source.d
```

for the `.odd` constructor.

### `GoldenZeroSectorInversionPacket.factor_difference`

The original difference identity for `A0` and `B0` becomes

$$
e^5+4d^5=f^5
$$

after rewriting the exact fifth-power forms.

## Proof flow

### 1. Extract odd half-factors

```lean
obtain ⟨A1, B1, hA, hAodd, hB, hBodd⟩ := p.odd_factor_halves hc
```

removes one factor of two from each inversion factor.

### 2. Prove `A1` and `B1` coprime

Assume an odd prime $q$ divides both reduced factors. The equalities `A0=2*A1` and `B0=2*B1` then show that $q$ divides both `A0` and `B0`, contradicting `p.no_common_odd_prime`.

This yields

```lean
hcop : Nat.Coprime A1 B1
```

### 3. Reduce the product to a pure fifth power

The proof uses `Nat.mul_left_cancel` to cancel the common factor 4 and derives

$$
A_1B_1=Q^5.
$$

### 4. Split the coprime fifth power

```lean
obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
```

produces the fifth-power bases `e` and `f`.

### 5. Recover positivity

If $e=0$, then $A_0=2e^5=0$, contradicting `p.A0_pos`. The same argument proves $f>0$ from `p.B0_pos`.

### 6. Recover base-level coprimality and oddness

The proof first obtains `Coprime (e^5) (f^5)` and then descends through `dvd_pow_self` to `Coprime e f`.

It also uses `Nat.odd_pow_iff` to turn oddness of the fifth powers back into oddness of their bases.

### 7. Establish ownership `e*f=Q`

The equality of fifth powers is shown first, then

```lean
Nat.pow_left_injective (by decide : 5 ≠ 0)
```

is used to infer

$$
(ef)^5=Q^5
\Longrightarrow
ef=Q.
$$

### 8. Derive the branch-specific difference equation

The proof rewrites `p.factor_difference` by the exact forms of `A0` and `B0`, after which `omega` closes

$$
e^5+4d^5=f^5.
$$

### 9. Construct the `.odd` certificate

All witnesses and proofs are finally packed into

```lean
GoldenZeroSectorFactorData.odd
```

and wrapped in `Nonempty`.

## Lean-specific processing

### `Nonempty`

The conclusion is

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

rather than directly exposing a named factor datum. This allows the implementation to prove inhabitation while keeping the branch-construction detail behind an existence-oriented interface.

### `private theorem`

The declaration can be used by later code in the same file, but it is not intended as a stable external API. This marks the construction as an implementation detail of the factorization stage.

### `obtain` with nested witnesses

The return shape of `fifth_power_factor_split` is destructured at once by

```lean
obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := ...
```

which keeps the witness extraction compact.

### Equality transport

```lean
hownership ▸ p.coprime_Q_d
```

uses the equality `e*f=Q` to transport

```lean
Nat.Coprime Q d
```

into

```lean
Nat.Coprime (e*f) d
```

without a separate rewrite block.

### `by decide`

Finite decidable side conditions, such as the nonzeroness of exponent 5 and hypotheses needed by `dvd_pow_self`, are discharged computationally.

### `omega`, `ring`, `norm_num`

The proof uses domain lemmas for the mathematical structure and delegates coefficient normalization, natural-number linear arithmetic, and zero contradictions to tactics.

## Redundancy and duplication

The proofs of `hePos` and `hfPos` are almost perfectly symmetric. The same is true of the oddness recovery for `e` and `f`, and of the final rewrites producing the `A_eq` and `B_eq` fields.

The amount of duplication is nevertheless modest because this is a single internal branch constructor.

The derivation of `Nat.Coprime e f` first constructs coprimality at the fifth-power level and then descends to the bases with `of_dvd_left` and `of_dvd_right`. If Mathlib provides an exactly matching equivalence for coprimality of equal positive powers, that part might be shortened; the repository evidence inspected here does not establish a better exact lemma name.

## Optimization candidates

### Local helper for the symmetric positivity arguments

The zero-exclusion arguments for `e` and `f` could be factored into a small local helper. Since the helper would only be used twice inside a private theorem, the gain is mainly cosmetic.

### Stronger fifth-power-split certificate

A stronger version of `fifth_power_factor_split` could return additional derived properties such as base coprimality, positivity, or parity along with the witnesses. That would shorten this theorem.

On the other hand, keeping `fifth_power_factor_split` mathematically minimal and deriving branch-specific properties here improves its general reusability.

### Reusable ownership lemma

The fifth-power injectivity step proving `e*f=Q` is already concise. If the same pattern recurs in the even branches, a local helper for fifth-power ownership could reduce repetition across branch constructors.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

for the whole generated file.

Mathlib functionality used directly in this theorem includes at least:

- `Nat.Coprime`
- divisibility lemmas such as `dvd_mul_of_dvd_right` and `dvd_pow_self`
- `Nat.eq_zero_of_not_pos`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `mul_pow`
- `omega`
- `ring`
- `norm_num`
- standard elaboration and rewriting facilities such as `simpa`, `rw`, and `obtain`

The main domain-specific dependencies are preceding local declarations from the zero-sector factorization development; in the original module split this material belongs around `SignedGoldenZeroSectorFactorization.lean`.

`import Mathlib` is likely broader than necessary for this theorem alone. Because no Lean build is performed in this task, a concrete minimal import list is not claimed as verified.

## Comparator challenge suitability

**Very suitable, with medium-to-high difficulty.**

The theorem requires a solver to reconstruct several logically distinct stages in the correct order:

1. obtain the odd half-factorization,
2. derive coprimality from common-prime exclusion,
3. cancel the coefficient in the product identity,
4. split a coprime fifth power,
5. recover positivity, parity, and base-level coprimality,
6. prove ownership by fifth-power injectivity,
7. obtain the branch difference equation,
8. assemble the dependent `.odd` constructor.

A strong challenge would provide the theorem statement and major existing lemmas while leaving the `.odd` certificate construction to the solver.

The comparator should emphasize successful type checking of an inhabitant of `GoldenZeroSectorFactorData p`, rather than requiring syntactic identity of the final proof term.

## Next declaration to read

The next declaration is

```lean
/-- In the even-`c` branch, both inversion factors contain at least three
factors of two. -/
theorem GoldenZeroSectorInversionPacket.eight_dvd_factors
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0 := by
```

Its kind is **`theorem`**.

Where the present theorem constructs the factor certificate for the odd-`c` branch, the next theorem opens the even-`c` branch by proving the two-adic lower bounds

$$
8\mid A_0,
\qquad
8\mid B_0.
$$

The proof then proceeds through `even_factor_eighths` to `nonempty_even_factorData`, which constructs the even-branch counterpart of the exact factor certificate built here.
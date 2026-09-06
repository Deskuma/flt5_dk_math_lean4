# 0328 — `GoldenZeroSectorInversionPacket.no_common_odd_prime`

## Declaration kind

This declaration is a **`theorem`**.

It is a public theorem attached to `GoldenZeroSectorInversionPacket`. It proves that the positive natural inversion factors `A0` and `B0` have **no common odd prime divisor**.

## Lean type

```lean
/-- The positive inversion factors have no common odd prime divisor. -/
theorem GoldenZeroSectorInversionPacket.no_common_odd_prime
    (p : GoldenZeroSectorInversionPacket)
    (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hqA : q ∣ p.source.A0) (hqB : q ∣ p.source.B0) : False := by
  have hqDiff : q ∣ 8 * p.source.d ^ 5 := by
    have hqAZ : (q : ℤ) ∣ p.source.A0 := Int.natCast_dvd.mpr hqA
    have hqBZ : (q : ℤ) ∣ p.source.B0 := Int.natCast_dvd.mpr hqB
    have hqDiffZ : (q : ℤ) ∣
        (p.source.B0 : ℤ) - (p.source.A0 : ℤ) :=
      dvd_sub hqBZ hqAZ
    have hdiffZ : (p.source.B0 : ℤ) - (p.source.A0 : ℤ) =
        8 * (p.source.d : ℤ) ^ 5 := by
      have hcast : (p.source.B0 : ℤ) =
          (p.source.A0 : ℤ) + 8 * (p.source.d : ℤ) ^ 5 := by
        exact_mod_cast p.factor_difference
      linarith
    rw [hdiffZ] at hqDiffZ
    exact Int.natCast_dvd.mp hqDiffZ
  have hqd : q ∣ p.source.d := by
    rcases hq.dvd_mul.mp hqDiff with hq8 | hqd5
    · have hq2pow : q ∣ 2 ^ 3 := by simpa using hq8
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqd5
  have hqMass : q ∣ zeroSectorQ p.source.c := by
    have hqProduct : q ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
      rw [← p.factor_product]
      exact dvd_mul_of_dvd_left hqA _
    rcases hq.dvd_mul.mp hqProduct with hq4 | hqQ5
    · have hq2pow : q ∣ 2 ^ 2 := by simpa using hq4
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqQ5
  unfold zeroSectorQ at hqMass
  rcases hq.dvd_mul.mp hqMass with hq5pow | hqcpow
  · have hq5 : q ∣ 5 := hq.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
    exact p.five_not_dvd_d (hqeq ▸ hqd)
  · have hqc : q ∣ p.source.c := hq.dvd_of_dvd_pow hqcpow
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqc hqd) p.coprime_c_d
```

## Mathematical statement

Assume that a prime $q$ satisfies

$$
q\mid A_0,
\qquad
q\mid B_0,
$$

and additionally $q\neq2$. The theorem shows that these assumptions lead to a contradiction. Hence the natural factors $A_0,B_0$ have no common **odd prime divisor**.

The conclusion is deliberately not `Nat.Coprime A0 B0` itself, because the prime $2$ genuinely occurs in both factors. Downstream, the two-adic factors are removed first; this theorem is then combined with 0326 `coprime_of_odd_of_no_common_odd_prime` to prove coprimality of the remaining odd parts.

## Role in the whole proof

The zero-sector inversion packet already carries the two natural-number identities

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5,
$$

where

$$
Q=5^5c^8.
$$

This theorem applies the same common prime $q$ to the product and the difference information.

1. From $q\mid A_0$ and $q\mid B_0$, the difference yields $q\mid8d^5$.
2. Since $q$ is an odd prime, $q\nmid8$, so $q\mid d$.
3. From $q\mid A_0$ and the product identity, $q\mid4Q^5$.
4. Since $q$ is odd, $q\nmid4$, so $q\mid Q$.
5. Since $Q=5^5c^8$, either $q\mid5$ or $q\mid c$.
6. In the first branch, primality gives $q=5$, contradicting the already known `five_not_dvd_d` together with $q\mid d$.
7. In the second branch, $q\mid c$ and $q\mid d$ contradict `coprime_c_d`.

Therefore no common odd prime can exist.

This result is a direct input to the later theorem `GoldenZeroSectorInversionPacket.odd_factor_halves`. After that theorem writes

$$
A_0=2A_1,
\qquad
B_0=2B_1,
$$

`no_common_odd_prime` is used to establish that the odd factors $A_1,B_1$ are coprime.

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

Defined at 0324 and constructed from a candidate at 0325. The fields used directly here are:

- `p.factor_difference`
- `p.factor_product`
- `p.five_not_dvd_d`
- `p.coprime_c_d`
- `p.source.A0`, `p.source.B0`, `p.source.c`, `p.source.d`

### `zeroSectorQ`

The mass term unfolded near the end of the proof. Its factorization

$$
Q=5^5c^8
$$

is decisive for the final prime split.

### Main Mathlib lemmas

- `Int.natCast_dvd.mpr`, `Int.natCast_dvd.mp`
- `dvd_sub`
- `Nat.Prime.dvd_mul`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_prime`
- `Nat.not_coprime_of_dvd_of_dvd`
- `dvd_mul_of_dvd_left`

The tactics `norm_num`, `simpa`, `linarith`, and `exact_mod_cast` support numeric normalization and type conversion.

## Proof flow

### 1. Turn the common divisor into a divisor of the difference

The proof first casts `hqA` and `hqB` to integer divisibility:

```lean
have hqAZ : (q : ℤ) ∣ p.source.A0 := Int.natCast_dvd.mpr hqA
have hqBZ : (q : ℤ) ∣ p.source.B0 := Int.natCast_dvd.mpr hqB
```

Because ordinary subtraction is available over `ℤ`, the common divisor divides the difference:

```lean
have hqDiffZ : (q : ℤ) ∣
    (p.source.B0 : ℤ) - (p.source.A0 : ℤ) :=
  dvd_sub hqBZ hqAZ
```

The packet field `p.factor_difference` is the subtraction-free natural identity

$$
B_0=A_0+8d^5.
$$

Using `exact_mod_cast` and `linarith`, the proof reconstructs the integer difference equation

$$
B_0-A_0=8d^5.
$$

Then `Int.natCast_dvd.mp` transports divisibility back to `ℕ`, giving

$$
q\mid8d^5.
$$

### 2. Use `q ≠ 2` to extract `q ∣ d`

`hq.dvd_mul.mp hqDiff` splits into

$$
q\mid8
\quad\text{or}\quad
q\mid d^5.
$$

If $q\mid8=2^3$, then `dvd_of_dvd_pow` gives $q\mid2`, and `Nat.dvd_prime` forces $q=2$, contradicting `hq2`.

Thus only $q\mid d^5$ remains, and another application of `dvd_of_dvd_pow` gives

$$
q\mid d.
$$

### 3. Extract `q ∣ Q` from the product identity

From `hqA : q ∣ A0` and

$$
A_0B_0=4Q^5,
$$

the proof obtains

$$
q\mid4Q^5.
$$

Again `hq.dvd_mul.mp` gives

$$
q\mid4
\quad\text{or}\quad
q\mid Q^5.
$$

The first branch collapses exactly as before because $4=2^2$ and $q\neq2$. The second gives

$$
q\mid Q.
$$

### 4. Expand `Q = 5^5 c^8` and close both branches

After `unfold zeroSectorQ at hqMass`, primality gives

$$
q\mid5^5
\quad\text{or}\quad
q\mid c^8.
$$

In the first branch, $q\mid5$, hence $q=5$. Together with the already proved $q\mid d$, this yields $5\mid d$, contradicting `p.five_not_dvd_d`.

In the second branch, $q\mid c`. Together with $q\mid d$ and `hq.one_lt`, this gives a nontrivial common divisor of `c` and `d`, contradicting `p.coprime_c_d`.

All branches are therefore impossible.

## Lean-specific processing

### The `ℕ → ℤ → ℕ` round trip

Only the opening difference argument moves natural-number divisibility into integer divisibility and back. This avoids truncated natural subtraction when using `B0 - A0`.

### `hq.dvd_of_dvd_pow`

The mathematical phrase “a prime dividing a power divides the base” appears explicitly several times in Lean. It is used for powers of $2$, $d^5$, $Q^5$, $5^5$, and $c^8$.

### `Nat.dvd_prime`

From facts such as $q\mid2$ or $q\mid5$, Lean first obtains the divisor alternatives for the prime target. The impossible `q = 1` branch is removed with `hq.ne_one`, leaving `q = 2` or `q = 5`.

### `exact (hq2 this).elim`

This is the standard contradiction idiom: `this : q = 2` contradicts `hq2 : q ≠ 2`, producing `False`, whose eliminator closes the current goal.

## Redundancy and duplication

The clearest duplication is the argument “if prime $q$ divides a positive power of $2$, then $q=2$.” It is performed once for `8` and once for `4`:

```lean
have hq2pow : q ∣ 2 ^ k := ...
have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
have : q = 2 := ...
exact (hq2 this).elim
```

This could be factored into a local helper.

The repeated uses of `dvd_of_dvd_pow` are also structurally similar, although keeping them explicit is reasonably readable because the bases differ in each branch.

## Optimization candidates

### 1. Possibly remove the integer cast in the difference step

`p.factor_difference` already has the subtraction-free natural form

$$
B_0=A_0+8d^5.
$$

It should therefore be possible, using `Nat.dvd_add_left` or a related divisibility lemma, to derive $q\mid8d^5$ directly from `q ∣ A0` and `q ∣ B0` inside `ℕ`.

If that elaborates cleanly, the proof could remove:

- `Int.natCast_dvd`
- `dvd_sub`
- `exact_mod_cast`
- `linarith`

from this part and remain entirely in `ℕ`.

This is an optimization candidate rather than a confirmed replacement; the exact orientation and elaboration of the relevant Mathlib divisibility lemma should be checked in Lean before changing the source.

### 2. Factor the power-of-two exclusion into a local helper

A local lemma saying that a prime `q ≠ 2` cannot divide any positive power `2 ^ k` would shorten both the `8` and `4` branches. If it is not reused elsewhere, however, the current explicit proof has the advantage of locality.

### 3. Shorten `q ∣ 5 → q = 5`

If the pinned Mathlib version provides a more direct prime-divisor equality lemma, the current `Nat.dvd_prime ... resolve_left hq.ne_one` sequence could be shortened. The exact API should be verified before adopting such a refactor.

## Required Mathlib import

The standalone source uses

```lean
import Mathlib
```

The functionality needed by this theorem is mainly:

- `Nat.Prime` and prime divisibility lemmas
- `Nat.Coprime`
- `Int.natCast_dvd`
- divisibility algebra
- `norm_num`
- `linarith`
- `exact_mod_cast`

### Import optimization candidate

For the standalone artifact, `import Mathlib` is reasonable. If this theorem were isolated into a minimal module, the imports could probably be narrowed to number-theoretic prime/divisibility modules plus the required tactic imports. The exact minimal set is not confirmed here because no Lean build is being run in this task.

## Comparator challenge suitability

**Suitable.**

It tests several useful proof-engineering skills:

- prime splitting with `Nat.Prime.dvd_mul`
- extracting a base divisor from a divisor of a power
- divisibility across `ℕ` / `ℤ` casts
- contradictions from `Nat.Coprime`
- combining packet invariants into a new local exclusion theorem

For a standalone Comparator challenge, it would be cleaner to expose only the mathematical hypotheses

$$
AB=4Q^5,
\quad
B=A+8d^5,
\quad
Q=5^5c^8,
\quad
\gcd(c,d)=1,
\quad
5\nmid d,
$$

and ask the solver to prove that no odd prime divides both $A$ and $B$.

A harder variant could explicitly forbid integer casts and require a proof entirely in `ℕ`.

## Next declaration to read

The next declaration is

```lean
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
```

In the branch where `c` is odd, it uses the oddness of $Q$ together with

$$
A_0B_0=4Q^5
$$

and

$$
B_0=A_0+8d^5
$$

to show that each factor contains **exactly one factor of two**. It produces

$$
A_0=2A_1,
\qquad
B_0=2B_1,
$$

with both $A_1$ and $B_1$ odd.

Afterward, `no_common_odd_prime` and 0326 `coprime_of_odd_of_no_common_odd_prime` combine to construct `Nat.Coprime A1 B1`. Thus 0328 is the central odd-prime exclusion step that makes the subsequent fifth-power factor splitting possible.

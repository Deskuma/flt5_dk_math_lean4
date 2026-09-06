# 0326 — `coprime_of_odd_of_no_common_odd_prime`

## Declaration kind

This is a **`private theorem`**.

It is a local helper placed at the beginning of `SignedGoldenZeroSectorFactorization.lean`, not an API intended to be exported outside the module.

## Lean type

```lean
/-- An odd factor cannot share any prime with a second factor once common odd
prime divisors have been excluded. -/
private theorem coprime_of_odd_of_no_common_odd_prime
    {m n : ℕ} (hm : Odd m)
    (hodd : ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) :
    Nat.Coprime m n := by
  apply Nat.coprime_of_dvd
  intro q hq hqm hqn
  by_cases hq2 : q = 2
  · subst q
    have hmEven : Even m := even_iff_two_dvd.mpr hqm
    exact (Nat.not_even_iff_odd.mpr hm) hmEven
  · exact hodd q hq hq2 hqm hqn
```

Equivalently, for implicit arguments `m n : ℕ`, its type is

```lean
Odd m →
(∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) →
Nat.Coprime m n
```

## Mathematical statement

There are two assumptions.

1. `m` is odd.
2. No prime `q` other than `2` divides both `m` and `n`.

Then

$$
\gcd(m,n)=1,
$$

that is, `Nat.Coprime m n`.

The argument is elementary. Assume there is a common prime divisor `q`. If `q=2`, then `2 ∣ m`, so `m` is even, contradicting `Odd m`. If `q≠2`, the second hypothesis `hodd` directly excludes `q` as a common divisor. Hence no common prime divisor can exist.

## Role in the full FLT5 proof

This theorem is the first local tool used after entering the factorization phase following zero-sector inversion.

The preceding inversion packet supplies positive natural factors `A0`, `B0` together with identities such as

$$
A_0B_0=4Q^5,
$$

and

$$
B_0=A_0+8d^5.
$$

The factorization phase must remove powers of two from these factors, prove that the remaining factors are pairwise coprime, and then split the fifth-power product into independent fifth-power components.

This theorem is a generic helper for that conversion. It combines

- oddness of one factor, and
- exclusion of every common odd prime divisor,

into the standard Mathlib conclusion `Nat.Coprime`.

It therefore acts as a bridge from local prime-divisor exclusion to full coprimality.

## Direct dependencies

### `Odd m`

The standard predicate expressing that `m` is odd.

### `Nat.Prime q`

The standard natural-number primality predicate.

### `Nat.Coprime m n`

The natural-number coprimality conclusion.

### `Nat.coprime_of_dvd`

The Mathlib theorem providing the proof skeleton. It reduces coprimality to excluding an arbitrary common prime divisor `q`.

### `even_iff_two_dvd`

Relates `2 ∣ m` to `Even m`.

### `Nat.not_even_iff_odd`

Used to obtain `¬ Even m` from `Odd m`.

### `hodd`

The theorem hypothesis that directly eliminates a common prime divisor in the branch `q ≠ 2`.

## Proof flow

1. Apply `Nat.coprime_of_dvd`, converting the goal into exclusion of arbitrary common prime divisors.
2. Introduce a prime `q` and hypotheses `q ∣ m`, `q ∣ n`.
3. Split with `by_cases hq2 : q = 2`.
4. In the branch `q=2`, use `subst q` to replace `q` by `2` everywhere.
5. From `hqm : 2 ∣ m`, derive `Even m` via `even_iff_two_dvd.mpr hqm`.
6. From `hm : Odd m`, derive `¬ Even m` via `Nat.not_even_iff_odd.mpr hm`, yielding a contradiction.
7. In the branch `q≠2`, close immediately with `hodd q hq hq2 hqm hqn`.

Thus the proof closes by the exhaustive split between the unique even prime `2` and all other primes.

## Lean-specific processing

### `private theorem`

Although the declaration lives inside the namespace, `private` means it is intended only as an implementation helper for this factorization module rather than part of the ordinary exported API.

### `apply Nat.coprime_of_dvd`

This changes the target `Nat.Coprime m n` into a prime-divisor exclusion problem. It is the main step aligning the mathematical argument with Mathlib's available API.

### `by_cases hq2 : q = 2`

The prime `q` is split into the exceptional even prime `2` and the case `q ≠ 2`. This matches the interface of `hodd`, which is deliberately stated only for primes different from `2`.

### `subst q`

In the `q=2` branch, this replaces `q` completely by `2`, allowing `hqm` to be used directly as `2 ∣ m`.

### `.mpr`

Both `even_iff_two_dvd.mpr` and `Nat.not_even_iff_odd.mpr` apply the reverse direction of an equivalence. The proof is built from explicit proof terms rather than heavier automation.

## Redundancy and duplication

There is little redundancy in the proof itself.

The `q=2` branch might be shortened if an available Mathlib lemma directly expresses that an odd natural number is not divisible by `2`, for example in a shape resembling

```lean
exact hm.not_two_dvd_nat hqm
```

However, the exact lemma name and applicability were **not confirmed** in this run because no Lean build was performed.

The hypothesis `hodd` is written in explicit curried form:

```lean
∀ q, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False
```

An alternative presentation could be

```lean
∀ q, Nat.Prime q → q ≠ 2 → ¬ (q ∣ m ∧ q ∣ n)
```

but the current form may be more convenient for direct application from downstream proofs.

## Optimization candidates

The most natural local optimization is to replace the explicit conversion

```lean
2 ∣ m → Even m → contradiction with Odd m
```

by a direct oddness/divisibility lemma if one is available and stable in Mathlib.

A second design choice is to retain this declaration as `private`. Although the mathematical fact is general, in this development it serves as local glue for the factorization machinery, so there is no evident need to enlarge the public namespace.

If structurally identical proofs occur in several other modules, promoting a shared helper could be worthwhile. That repository-wide duplication question is **not confirmed** here because a complete search for equivalent lemmas was not performed.

## Required Mathlib imports and possible import optimization

The canonical standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The theorem directly relies on APIs involving

- `Nat.Coprime`,
- `Nat.Prime`,
- `Odd` and `Even`,
- `Nat.coprime_of_dvd`,
- `even_iff_two_dvd`,
- `Nat.not_even_iff_odd`.

A substantially smaller import than all of `Mathlib` is therefore likely possible in principle. The exact minimal import set is **not confirmed**, because no Lean build or import-minimization experiment was performed.

## Suitability for a Comparator challenge

It is **well suited** to a Comparator challenge.

The theorem is small and self-contained, and several Lean proof styles can express the same mathematics cleanly. Useful variants include:

1. the current `Nat.coprime_of_dvd` plus `by_cases q = 2` proof;
2. a proof through `Nat.coprime_iff_gcd_eq_one` and exclusion of prime divisors of the gcd;
3. a direct prime-divisor characterization of `Nat.Coprime`;
4. a shortened `q=2` branch using a direct oddness/non-divisibility lemma.

Useful evaluation criteria are proof length, dependency count, readability, robustness against Mathlib API changes, and elaboration simplicity.

## Next declaration to read

The next declaration in the same factorization module is the private theorem

```lean
private theorem exists_eq_two_mul_odd_of_two_dvd_not_four_dvd
    {n : ℕ} (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    ∃ m : ℕ, n = 2 * m ∧ Odd m := by
  rcases h2 with ⟨m, hm⟩
  refine ⟨m, hm, Nat.not_even_iff_odd.mp ?_⟩
  rw [even_iff_two_dvd]
  intro h2m
  rcases h2m with ⟨k, hk⟩
  apply h4
  refine ⟨k, ?_⟩
  omega
```

It extracts

$$
n=2m,\qquad m\text{ odd}
$$

from

$$
2\mid n,\qquad 4\nmid n.
$$

In other words, it normalizes a factor of exact two-adic depth one into `2 × odd`. In museum dependency order, the natural next entry is **0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`**.

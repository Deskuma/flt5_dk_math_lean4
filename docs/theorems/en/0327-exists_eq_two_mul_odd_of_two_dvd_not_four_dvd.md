# 0327 — `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`

## Declaration kind

This is a **`private theorem`**.

It is a local helper used only inside `SignedGoldenZeroSectorFactorization.lean`; it is not part of the public API.

## Lean type

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

As a type, this is

```lean
{n : ℕ} → 2 ∣ n → ¬ 4 ∣ n → ∃ m : ℕ, n = 2 * m ∧ Odd m
```

## Mathematical statement

If a natural number `n` satisfies

$$
2 \mid n,
$$

and

$$
4 \nmid n,
$$

then there exists a natural number `m` such that

$$
n = 2m
$$

and `m` is odd.

In 2-adic language, when the exponent of 2 in `n` is exactly one, removing that unique factor of 2 leaves an odd quotient.

## Role in the FLT5 proof

The preceding 0326 theorem turns “odd factor plus no common odd prime” into coprimality. The present theorem supplies the 2-adic normalization needed before that step.

The zero-sector inversion packet provides

$$
A_0 B_0 = 4Q^5
$$

and

$$
B_0 = A_0 + 8d^5.
$$

The following theorem `GoldenZeroSectorInversionPacket.odd_factor_halves` first proves that both `A0` and `B0` are divisible by 2 but not by 4, then applies the present theorem to each factor to obtain

$$
A_0 = 2A_1, \qquad B_0 = 2B_1
$$

with

$$
A_1, B_1 \text{ odd}.
$$

Thus this theorem is a local normalization lemma converting the information “the 2-adic exponent is exactly one” into the explicit `2 × odd` form required by downstream factorization.

## Direct dependencies

### `Nat.not_even_iff_odd`

This gives `¬ Even m ↔ Odd m`. The proof uses `.mp` to reduce the construction of `Odd m` to proving `¬ Even m`.

### `even_iff_two_dvd`

This gives `Even m ↔ 2 ∣ m`. The rewrite `rw [even_iff_two_dvd]` turns the parity statement into concrete divisibility by 2.

### `omega`

At the end it closes the arithmetic consequence of

```lean
hm : n = 2 * m
hk : m = 2 * k
```

namely

```lean
n = 4 * k
```

which produces the contradiction with `h4`.

### Assumptions `h2`, `h4`

`h2 : 2 ∣ n` produces the quotient `m`, while `h4 : ¬ 4 ∣ n` rules out the possibility that this quotient is even.

## Proof flow

1. Destructure `h2 : 2 ∣ n` and obtain a witness `m` with `n = 2 * m`.
2. Choose this same `m` as the witness of the existential conclusion.
3. Reduce the remaining goal `Odd m` to `¬ Even m` using `Nat.not_even_iff_odd.mp`.
4. Rewrite `Even m` as `2 ∣ m` using `even_iff_two_dvd`.
5. Assume `2 ∣ m` and extract a witness `k` with `m = 2 * k`.
6. Then `n = 2m = 4k`, hence `4 ∣ n`.
7. This contradicts `h4 : ¬ 4 ∣ n`.
8. Therefore `m` is not even, hence it is odd.

Mathematically the proof is the direct chain

$$
2 \mid n,\quad 4 \nmid n
\Longrightarrow v_2(n)=1
\Longrightarrow n=2m,\quad 2\nmid m
\Longrightarrow m\text{ odd}.
$$

## Lean-specific processing

### `rcases h2 with ⟨m, hm⟩`

Lean divisibility `a ∣ b` is represented by an existential witness, so the quotient `m` and its multiplication equality can be extracted directly from `h2`.

### `refine ⟨m, hm, ...⟩`

The existential witness, factorization identity, and oddness proof are assembled in one constructor expression. For a proposition this small, this is clearer than splitting the construction into several tactics.

### `Nat.not_even_iff_odd.mp`

Rather than constructing `Odd m` directly, the proof establishes that `m` is not even and then transports that fact through a standard equivalence. This fits the hypothesis `¬ 4 ∣ n` naturally.

### `rw [even_iff_two_dvd]`

The abstract parity predicate is reduced to divisibility, making it possible to destructure the assumption again with `rcases`.

### `omega`

Only the final linear arithmetic identity is delegated to automation. The number-theoretic reasoning has already been completed before this step.

## Redundancy and duplication

The proof is already short and has little obvious redundancy.

The final block

```lean
rcases h2m with ⟨k, hk⟩
apply h4
refine ⟨k, ?_⟩
omega
```

could possibly be replaced by a purely divisibility-based proof using multiplication/divisibility lemmas. That might remove the dependency on `omega`. The exact shortest Mathlib lemma combination is **unverified** here because no Lean build was run.

The statement itself is also general enough that Mathlib may already contain an equivalent parity or 2-adic lemma. A complete API search was not performed in this run, so that possibility is **unverified**.

## Optimization candidates

The first candidate is to replace this theorem by a thin wrapper around an existing Mathlib lemma about exact divisibility by 2, if such a lemma exists.

The second candidate is to eliminate `omega` and prove

$$
2 \mid m \Longrightarrow 4 \mid 2m = n
$$

using divisibility lemmas only. This could reduce tactic dependencies and make the proof term more explicitly number-theoretic.

That said, the present proof is already very readable and is entirely reasonable as a private local helper; shortening it at the cost of readability would bring little benefit.

## Required Mathlib imports and import optimization

The checked canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main APIs directly needed by this theorem are:

- natural-number divisibility `∣`
- `Odd`, `Even`
- `Nat.not_even_iff_odd`
- `even_iff_two_dvd`
- `omega`

A narrower import set than all of `Mathlib` is therefore likely possible. The exact minimal import set is **unverified**, since no Lean build or import-minimization pass was run.

## Comparator challenge suitability

**Highly suitable.**

The statement is small and self-contained, and several proof styles can be compared cleanly:

1. The current `Even` / `Odd` bridge plus `omega`.
2. A divisibility-only proof that avoids `omega`.
3. A proof via 2-adic valuation, deriving the result from `v₂(n)=1`.
4. A wrapper around a direct Mathlib lemma, if one exists.

Useful comparison axes are proof length, tactic dependencies, readability, stability against Mathlib API changes, and clarity of the underlying number-theoretic meaning.

## Next declaration to read

The next declaration is

```lean
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 2 * A1 ∧ Odd A1 ∧
      p.source.B0 = 2 * B1 ∧ Odd B1 := by
  ...
```

It applies the present private theorem to both `A0` and `B0`, producing the odd half-factors

$$
A_0 = 2A_1,\qquad B_0 = 2B_1.
$$

In museum dependency order, the natural next entry is **0328 `GoldenZeroSectorInversionPacket.odd_factor_halves`**.

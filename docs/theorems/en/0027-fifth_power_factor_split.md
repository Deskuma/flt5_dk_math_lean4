# 0027 — `fifth_power_factor_split`

## Declaration

```lean
theorem fifth_power_factor_split
    {g n x : ℕ} (hcop : Nat.Coprime g n) (hbody : g * n = x ^ 5) :
    (∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5) := by
  have hunit : IsUnit (GCDMonoid.gcd g n) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd n g) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)
```

## Lean type

The theorem takes natural numbers `g` and `n` that are coprime and whose product is the fifth power of a natural number `x`, and returns that each factor is itself a fifth power.

```lean
Nat.Coprime g n →
  g * n = x ^ 5 →
  ((∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5))
```

## Mathematical statement

The assumptions are

$$
\gcd(g,n)=1,
\qquad
 gn=x^5.
$$

Coprime factors share no prime divisor. Every prime exponent in the product `gn` is a multiple of $5$, because the product is a fifth power, and each such exponent belongs entirely to either `g` or `n`. Hence every prime exponent in each factor is itself a multiple of $5$. Therefore there exist $a,b\in\mathbb N$ such that

$$
g=a^5,
\qquad
n=b^5.
$$

## Role in the complete proof

In Branch B, the previous article establishes

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1.
$$

The fifth-power equation and the difference factorization also give

$$
(z-y)GN5(z-y,y)=x^5.
$$

This theorem is the general engine that consumes those two facts and separates the gap and `GN5` into individual perfect fifth powers.

The theorem knows nothing about the FLT5-specific polynomial. It uses only the general `GCDMonoid` structure of a coprime product that is a power, so it sits at the boundary between the Reduction layer and the later Branch B normal form.

## Direct dependencies

1. `Nat.Coprime`
   - Expresses that the natural numbers `g` and `n` have gcd `1`.
2. `GCDMonoid.gcd`
   - The general gcd API required by the Mathlib power-splitting theorem.
3. `gcd_eq_nat_gcd`
   - Bridges the general gcd and `Nat.gcd`.
4. `Nat.isUnit_iff`
   - Connects being a unit in `ℕ` with being equal to `1`.
5. `exists_eq_pow_of_mul_eq_pow`
   - A Mathlib lemma stating that if the gcd is a unit and a product is a power, then one factor is a power with the same exponent.
6. `gcd_comm`, `mul_comm`
   - Reverse the factor order so that the same general lemma can be applied to the second factor.

## Proof flow

1. Convert `hcop : Nat.Coprime g n` into the statement that the general gcd is a unit.

```lean
have hunit : IsUnit (GCDMonoid.gcd g n) := by
  simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
```

2. Split the conjunction in the conclusion with `constructor`.
3. Apply `exists_eq_pow_of_mul_eq_pow hunit hbody` directly to obtain `g=a^5`.
4. Reverse the gcd order and build `hunit' : IsUnit (gcd n g)`.
5. Reverse the product to `n*g=x^5`, then apply the same Mathlib lemma again to obtain `n=b^5`.

## Lean-specific processing

### Conversion from `Nat.Coprime` to `IsUnit gcd`

The central Mathlib lemma does not consume `Nat.Coprime g n` directly. It requires `IsUnit (GCDMonoid.gcd g n)`. The proof therefore normalizes three representations at once:

```lean
simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
```

### Reusing a one-sided lemma on both factors

`exists_eq_pow_of_mul_eq_pow` returns a conclusion about the left factor of a product. To apply it to the right factor, the proof explicitly reverses both the gcd and product with `gcd_comm` and `mul_comm`. The mathematical statement is symmetric, but the Lean API requires this explicit transport.

### Inference of the exponent `5`

The exponent is not supplied explicitly to the lemma. Lean infers it from the right side `x ^ 5` in `hbody` and from the targets `g = a ^ 5` and `n = b ^ 5`.

## Redundancy and duplication

The same Mathlib lemma is applied twice, once to each factor, and the second branch separately normalizes the gcd and product order. This is logical duplication, but the proof remains short and transparent.

It would be possible to inline `hunit'` inside the second application, but the current named intermediate localizes possible type-conversion failures and improves readability.

## Optimization candidates

1. If Mathlib provides a two-sided version of `exists_eq_pow_of_mul_eq_pow`, or a theorem returning the conjunction directly, the two applications may be combined. This has not been verified.
2. `hunit'` could be inlined as `by simpa [gcd_comm] using hunit`, though this would have no meaningful performance effect.
3. DkMath could introduce a general `coprime_power_factor_split` for an arbitrary exponent `k`, and make this theorem the specialization `k=5`. This is an unverified but reusable design proposal.
4. The current theorem name accurately advertises the fifth-power specialization and is clear in the FLT5 reading path.

## Required Mathlib imports and import optimization

The standalone source is checked under `import Mathlib`, so the minimal import set is not established.

The proof directly needs natural-number gcd and coprimality, `GCDMonoid`, units, powers, `exists_eq_pow_of_mul_eq_pow`, and commutativity lemmas. After checking the imports of the individual source module, it may be possible to reduce the dependency to focused gcd and natural-number modules such as a `Mathlib.Algebra.GCDMonoid` module. The exact module names and sufficiency are unverified because no Lean build was run.

## Comparator challenge suitability

This theorem is highly suitable. It exposes both the mathematical content and the Lean API conversion layer.

### Suggested challenge

```lean
{g n x : ℕ}
(hcop : Nat.Coprime g n)
(hbody : g * n = x ^ 5)
⊢ (∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5)
```

Possible solutions to compare:

1. The current reuse of `exists_eq_pow_of_mul_eq_pow`.
2. A proof expanding prime exponents or `padicValNat`.
3. A proof that first derives a symmetric helper theorem.
4. A proof that generalizes the exponent and then specializes to `5`.

Evaluation criteria include proof length, generality, use of Mathlib APIs, visibility of type conversions, build cost, and resilience to Mathlib changes.

## Verified facts and interpretation

The declaration type, proof body, used lemmas, and the fact that `branchB_fifth_power_factor_split` follows immediately afterward were verified in the repository Lean code. The prime-exponent explanation is the standard mathematical interpretation. The minimal imports, existence of a two-sided Mathlib theorem, and arbitrary-exponent generalization are unverified proposals.

## Next theorem to read

```lean
DkMath.FLT.Five.branchB_fifth_power_factor_split
```

It combines `CounterexamplePack`, the Branch B condition, the difference-of-fifth-powers factorization, and the general splitting theorem from this article to obtain the concrete exact elementary normal form

$$
z-y=a^5,
\qquad
GN5(z-y,y)=b^5.
$$
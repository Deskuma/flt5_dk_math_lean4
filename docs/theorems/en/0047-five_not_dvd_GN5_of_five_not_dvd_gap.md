# 0047 — `five_not_dvd_GN5_of_five_not_dvd_gap`

## 1. Declaration

```lean
theorem five_not_dvd_GN5_of_five_not_dvd_gap
    {g y : ℕ} (h5g : ¬ 5 ∣ g) :
    ¬ 5 ∣ GN5 g y := by
  intro h5GN
  have hdecomp := GN5_eq_g_pow_four_add_five_mul g y
  have h5tail :
      5 ∣ 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 + 2 * g * y ^ 3 + y ^ 4) :=
    dvd_mul_of_dvd_left (dvd_refl 5) _
  rw [hdecomp] at h5GN
  have h5g4 : 5 ∣ g ^ 4 := (Nat.dvd_add_left h5tail).mp h5GN
  exact h5g ((by decide : Nat.Prime 5).dvd_of_dvd_pow h5g4)
```

Its fully qualified name is `DkMath.FLT.Five.five_not_dvd_GN5_of_five_not_dvd_gap`.

## 2. Lean Type

```lean
{g y : ℕ} → (¬ 5 ∣ g) → ¬ 5 ∣ GN5 g y
```

The variables `g` and `y` are implicit. The only explicit hypothesis, `h5g`, says that the gap `g` is not divisible by 5. The conclusion is the negative proposition that the residual factor `GN5 g y` is not divisible by 5 either.

## 3. Mathematical Statement

The five-adic decomposition from Article 0009 is

$$
GN5(g,y)=g^4+5\bigl(g^3y+2g^2y^2+2gy^3+y^4\bigr).
$$

Hence

$$
GN5(g,y)\equiv g^4\pmod 5.
$$

If $5\mid GN5(g,y)$, then the second term on the right is trivially divisible by 5, so $5\mid g^4$. Since 5 is prime, this implies $5\mid g$, contradicting $5\nmid g$. Therefore

$$
5\nmid g \Longrightarrow 5\nmid GN5(g,y).
$$

## 4. Role in the Overall Proof

This lemma supplies one side of the fact that, in Branch B, where the gap is not divisible by 5, neither factor of the fifth-power body

$$
Body5(g,y)=g\,GN5(g,y)
$$

contains a factor 5.

In the immediately following theorem `five_not_dvd_x_of_branchB`, one first obtains `Body5 (z-y) y = x^5` from the Fermat equation. If $5\mid x$, then $5\mid Body5(z-y,y)$. Primality of 5 splits divisibility of the product into the gap side or the `GN5` side. The gap side is excluded by the Branch B hypothesis, and the `GN5` side is excluded by this lemma. Thus this result is a five-adic entry guard before the signed Branch A routing begins.

## 5. Direct Dependencies

1. `GN5`

   The definition of the fifth cyclotomic factor in gap coordinates.

2. `GN5_eq_g_pow_four_add_five_mul`

   The lemma from Article 0009 rewriting `GN5` in the form $g^4+5K$.

3. `dvd_mul_of_dvd_left`

   The generic divisibility lemma constructing $5\mid5K$ from $5\mid5$.

4. `Nat.dvd_add_left`

   A lemma transporting divisibility across an addition when one summand is already known to be divisible. Here it extracts $5\mid g^4$ from $5\mid5K$ and $5\mid(g^4+5K)$.

5. `Nat.Prime.dvd_of_dvd_pow`

   The lemma saying that if a prime divides a power, then it divides the base. It is used together with `(by decide : Nat.Prime 5)`.

## 6. Proof Flow

1. Because the conclusion is a negation, introduce the contrary hypothesis $5\mid GN5(g,y)$ with `intro h5GN`.
2. Store `GN5_eq_g_pow_four_add_five_mul g y` as `hdecomp`.
3. Construct `h5tail`, proving that the residual term $5K$ is divisible by 5.
4. Rewrite `h5GN` with `rw [hdecomp] at h5GN`, turning it into $5\mid(g^4+5K)$.
5. Use `Nat.dvd_add_left` to derive $5\mid g^4$.
6. Use primality of 5 to derive $5\mid g`, apply `h5g`, and close the contradiction.

## 7. Lean-Specific Processing

### 7.1 Negation as a Function

`¬ 5 ∣ GN5 g y` is definitionally `(5 ∣ GN5 g y) → False`, so the proof begins with `intro h5GN`. At the end, `h5g` is applied to the derived proof of `5 ∣ g` to obtain `False`.

### 7.2 Type Inference in `have hdecomp := ...`

The type of `hdecomp` is omitted and inferred from the theorem application. The equality is used as a local rewrite rule rather than as the final target.

### 7.3 The `_` Placeholder

```lean
dvd_mul_of_dvd_left (dvd_refl 5) _
```

uses `_` to let the elaborator infer the entire right multiplier. Since the polynomial is long, this avoids spelling out the same expression twice.

### 7.4 Normalizing a Hypothesis with `rw ... at`

The rewrite is performed only inside `h5GN`, not in the goal. This places the divisibility hypothesis directly into an additive form suitable for the next divisibility lemma.

### 7.5 Concrete Primality via `by decide`

`Nat.Prime 5` is a decidable closed proposition, so Lean synthesizes its proof with `by decide`. This implementation is specialized to the exceptional prime 5 rather than parameterized by an arbitrary prime.

## 8. Redundant or Repeated Parts

The proof is short and contains almost no mathematical duplication. There are only small local redundancies:

- `hdecomp` is named and then used exactly once for rewriting.
- The long residual polynomial appears both in the decomposition theorem and in the type of `h5tail`.
- `(by decide : Nat.Prime 5)` may recur in later five-adic lemmas.

These are reasonable tradeoffs for readability. The current proof makes every divisibility step explicit and easy to audit.

## 9. Optimization Candidates

### 9.1 Rewrite Directly with the Decomposition Theorem

It may be possible to omit `hdecomp` and write

```lean
rw [GN5_eq_g_pow_four_add_five_mul] at h5GN
```

directly. However, the explicit local name is more robust for argument inference and easier to inspect.

### 9.2 A Congruence or Remainder Proof

One could first prove `GN5 g y % 5 = g ^ 4 % 5` and then reason with remainders. The present proof stays entirely inside the divisibility API, which matches the vocabulary of the following `dvd_mul` argument.

### 9.3 A Generic Prime Lemma

A general result of the following shape could be extracted:

```lean
Nat.Prime p → n = a ^ k + p * t → ¬ p ∣ a → ¬ p ∣ n
```

But the important prime here is specifically 5, matching the cyclotomic exponent, so this abstraction may add more code than value.

### 9.4 A Local Name for the Residual Polynomial

Introducing `let K := ...` would shorten the displayed expression, but would likely require additional `simp [K]` or `dsimp [K]` steps and would not necessarily shorten the Lean proof.

## 10. Required Mathlib Imports and Import Optimization

The generated standalone source uses `import Mathlib`, so the declaration is confirmed to be available in the current artifact.

The theorem directly needs roughly the following facilities:

- natural-number divisibility and additive divisibility lemmas,
- `Nat.Prime.dvd_of_dvd_pow`,
- `decide` for proving `Nat.Prime 5`,
- the upstream definitions and theorem `GN5` and `GN5_eq_g_pow_four_add_five_mul`.

The exact import line of the split source file `SignedBranchA.lean` could not be retrieved directly from this repository artifact, so no minimal import claim is made. As an explicit inference, importing the upstream Branch A or GN5 module likely brings the necessary Mathlib components transitively. Any import optimization should be checked against the split module in the original `dkmath` repository using `lake env lean` or an import-audit tool. No Lean build was run for this article.

## 11. Comparator Challenge Suitability

 **Suitable.** 

A useful challenge is to provide only the declaration and the five-adic decomposition, then ask for a proof using the divisibility API:

```lean
theorem challenge
    {g y : ℕ} (h5g : ¬ 5 ∣ g) :
    ¬ 5 ∣ GN5 g y := by
  sorry
```

Points of comparison include:

- whether the additive divisibility lemma is used in the correct direction,
- whether `Nat.Prime.dvd_of_dvd_pow` is used to pass from $5\mid g^4$ to $5\mid g$,
- whether the existing structural decomposition is reused instead of expanding the polynomial with heavy automation,
- whether the negation is handled naturally as a function.

Although short, it is a strong foundational challenge combining divisibility APIs, rewriting, and concrete primality.

## 12. Sources and Reservations

The declaration name, type, proof body, following declaration, and its placement in `SignedBranchA.lean` were verified in the generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The kernel-checked Lean code is the primary basis of the mathematical explanation.

The existing PDFs provide narrative context for the overall signed five-adic and golden-descent route, but the Lean source takes precedence for the exact proof. The exact import line of the split source file could not be confirmed, and this uncertainty is stated explicitly above.

## 13. Next Theorem to Read

The next declaration should be

```lean
DkMath.FLT.Five.five_not_dvd_x_of_branchB
```

It proves $5\nmid x$ for a Branch B candidate. Assuming that 5 divides `x`, the proof sends 5 into the perfect-fifth-power body and then uses primality to split divisibility of `gap * GN5`. The gap branch is ruled out by the Branch B hypothesis, while the `GN5` branch is ruled out by the theorem of this article. It is therefore the direct consumer of this result.

# 0329 — `GoldenZeroSectorInversionPacket.odd_factor_halves`

## Declaration kind

This declaration is a **`theorem`**.

It is a public theorem on `GoldenZeroSectorInversionPacket`. In the branch where `c` is odd, it proves that each natural inversion factor `A0`, `B0` contains **exactly one factor of two**.

## Lean type

```lean
/-- In the odd-`c` branch, each inversion factor has exactly one factor of two. -/
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 2 * A1 ∧ Odd A1 ∧
      p.source.B0 = 2 * B1 ∧ Odd B1 := by
  have hQodd : Odd (zeroSectorQ p.source.c) := by
    unfold zeroSectorQ
    exact (show Odd (5 ^ 5) by norm_num).mul hc.pow
  have hRhsNotEight : ¬ 8 ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
    intro h8
    rcases h8 with ⟨k, hk⟩
    have h2Q : 2 ∣ zeroSectorQ p.source.c ^ 5 := by
      refine ⟨k, ?_⟩
      omega
    exact hQodd.pow.not_two_dvd_nat h2Q
  have h2Product : 2 ∣ p.source.A0 * p.source.B0 := by
    rw [p.factor_product]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have h2Diff : 2 ∣ 8 * p.source.d ^ 5 := by
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hEven : 2 ∣ p.source.A0 ∧ 2 ∣ p.source.B0 := by
    rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2Product with hA | hB
    · exact ⟨hA, by rw [p.factor_difference]; exact dvd_add hA h2Diff⟩
    · have hsum : 2 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
        simpa [p.factor_difference] using hB
      exact ⟨(Nat.dvd_add_left h2Diff).mp hsum, hB⟩
  have hNotFourA : ¬ 4 ∣ p.source.A0 := by
    intro h4A
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have h4B : 4 ∣ p.source.B0 := by
      rw [p.factor_difference]
      exact dvd_add h4A h4Diff
    have h16Product : 16 ∣ p.source.A0 * p.source.B0 := by
      simpa using Nat.mul_dvd_mul h4A h4B
    have h8Product : 8 ∣ p.source.A0 * p.source.B0 :=
      (by norm_num : 8 ∣ 16).trans h16Product
    rw [p.factor_product] at h8Product
    exact hRhsNotEight h8Product
  have hNotFourB : ¬ 4 ∣ p.source.B0 := by
    intro h4B
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have hsum : 4 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
      simpa [p.factor_difference] using h4B
    have h4A : 4 ∣ p.source.A0 := (Nat.dvd_add_left h4Diff).mp hsum
    exact hNotFourA h4A
  obtain ⟨A1, hA, hAodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.1 hNotFourA
  obtain ⟨B1, hB, hBodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.2 hNotFourB
  exact ⟨A1, B1, hA, hAodd, hB, hBodd⟩
```

## Mathematical statement

The assumption is `hc : Odd p.source.c`, i.e. $c$ is odd.

The conclusion states that there exist natural numbers $A_1,B_1$ such that

$$
A_0=2A_1,
\qquad
B_0=2B_1,
$$

and both $A_1$ and $B_1$ are odd.

In terms of two-adic valuation, this corresponds to

$$
v_2(A_0)=v_2(B_0)=1.
$$

The Lean theorem does not introduce `padicValNat`; instead it proves the valuation statement elementarily through `2 ∣ n` together with `¬ 4 ∣ n`.

## Role in the overall proof

The zero-sector inversion packet already carries

$$
A_0B_0=4Q^5,
$$

and

$$
B_0=A_0+8d^5,
$$

where

$$
Q=5^5c^8.
$$

If $c$ is odd, then $Q$ is odd. Hence the right-hand side $4Q^5$ contains exactly the factor $2^2$ in its two-adic part.

Meanwhile, $B_0-A_0=8d^5$ is even, so $A_0$ and $B_0$ have the same parity. Their product contains a factor 4, so both must be even. If either factor were divisible by 4, the difference relation would force the other one to be divisible by 4 as well, and then the product would be divisible by 16. But $4Q^5$ is not even divisible by 8 because $Q$ is odd. Therefore neither factor is divisible by 4.

Thus

$$
2\mid A_0,
\quad 4\nmid A_0,
\qquad
2\mid B_0,
\quad 4\nmid B_0.
$$

The private theorem 0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd` then normalizes each factor into `2 × odd`.

This theorem is the entry point for introducing $A_1,B_1$ in the odd factor branch. It prepares the later use of 0328 `no_common_odd_prime` together with 0326 `coprime_of_odd_of_no_common_odd_prime` to obtain `Nat.Coprime A1 B1`.

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

The main packet fields used are:

- `p.factor_product`
- `p.factor_difference`
- `p.source.A0`
- `p.source.B0`
- `p.source.c`
- `p.source.d`

### `zeroSectorQ`

The proof unfolds this definition and uses

$$
Q=5^5c^8
$$

to derive oddness of $Q$ from oddness of $c$.

### 0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`

This private theorem is invoked twice at the end:

$$
2\mid n,
\quad 4\nmid n
\Longrightarrow
\exists m,\ n=2m\land Odd(m).
$$

### Main Mathlib tools

- `Odd.mul`, `Odd.pow`
- `Odd.not_two_dvd_nat`
- `Nat.Prime.dvd_mul`
- `Nat.mul_dvd_mul`
- `dvd_mul_of_dvd_left`
- `dvd_add`
- `Nat.dvd_add_left`
- transitivity of divisibility
- `norm_num`
- `simpa`
- `omega`

## Proof flow

### 1. Show that `Q` is odd

After unfolding `zeroSectorQ`, one has $Q=5^5c^8$. Since $5^5$ is odd and `hc.pow` makes $c^8$ odd, the proof obtains

$$
Q\text{ is odd}.
$$

### 2. Fix that `4Q^5` is not divisible by 8

Assume

$$
8\mid4Q^5.
$$

After exposing the divisibility witness, `omega` constructs

$$
2\mid Q^5.
$$

But $Q^5$ is odd, contradiction. The resulting fact `hRhsNotEight` is the upper bound on the two-adic content of the product.

### 3. Prove that `A0` and `B0` are both even

From the product identity,

$$
2\mid A_0B_0.
$$

Since 2 is prime, `Nat.Prime.dvd_mul` yields $2\mid A_0$ or $2\mid B_0$.

The difference term $8d^5$ is also divisible by 2, so the equation

$$
B_0=A_0+8d^5
$$

transfers evenness from either factor to the other. This constructs `hEven`.

### 4. Prove that `A0` is not divisible by 4

Assume $4\mid A_0$. Since $4\mid8d^5$, the difference identity gives $4\mid B_0$.

Hence

$$
16\mid A_0B_0,
$$

and therefore $8\mid A_0B_0$. Rewriting by the product identity yields $8\mid4Q^5$, contradicting `hRhsNotEight`.

### 5. Prove that `B0` is not divisible by 4

This is symmetric in content, but the implementation reuses `hNotFourA`: from $4\mid B_0$ and the difference relation it derives $4\mid A_0`, immediately contradicting the previous result.

### 6. Normalize both factors as `2 × odd`

Apply 0327 to

- `hEven.1`, `hNotFourA`, and
- `hEven.2`, `hNotFourB`.

This produces $A_1,B_1$ and their oddness, which are then packaged into the existential conclusion.

## Lean-specific processing

### Using `Odd` as the negation of divisibility by 2

Lean keeps parity as `Odd n`, and only converts it to `¬ 2 ∣ n` where needed through `not_two_dvd_nat`. This keeps the proof within elementary divisibility rather than a valuation API.

### `rcases (by norm_num : Nat.Prime 2).dvd_mul.mp ...`

This is Euclid's lemma specialized to 2: if 2 divides a product, it divides one factor. It is exactly the formal counterpart of “if a product is even, at least one factor is even.”

### `simpa [p.factor_difference] using hB`

Here `factor_difference` is used as a rewrite rule so divisibility of `B0` is converted into divisibility of `A0 + 8*d^5` without manually constructing an equality chain.

### `omega`

`omega` is used only in the local arithmetic step that turns a witness for `8 ∣ 4Q^5` into a witness for `2 ∣ Q^5`. This is linear integer arithmetic with fixed coefficients.

## Redundancy and repetition

The parity and non-divisibility-by-4 arguments for `A0` and `B0` are mathematically symmetric. The implementation is not fully symmetric because the stored difference identity is oriented as `B0 = A0 + ...`.

The local fact

```lean
have h4Diff : 4 ∣ 8 * p.source.d ^ 5 := ...
```

is reconstructed in both `hNotFourA` and `hNotFourB` and could be shared.

Likewise, `2 ∣ 8*d^5` and `4 ∣ 8*d^5` are immediate consequences of the coefficient 8, so the two-adic divisibility facts for the difference term could be grouped earlier.

## Optimization candidates

### 1. Shorten the proof with a two-adic valuation API

Conceptually the proof uses

$$
v_2(A_0)+v_2(B_0)=2
$$

plus the strong two-adic divisibility of the difference to force both valuations to be 1. A `padicValNat`-based proof might express this structure more directly.

However, the current elementary proof has lighter conceptual dependencies and feeds directly into later `Odd` lemmas, so such a replacement is not automatically preferable.

### 2. Generalize `hRhsNotEight`

The fact “if `Q` is odd, then `¬ 8 ∣ 4 * Q^5`” does not fundamentally depend on exponent 5. It can be abstracted to a small lemma such as `Odd u → ¬ 8 ∣ 4*u`. If the same pattern appears elsewhere in the branch analysis, that would remove duplication.

### 3. Share `h4Diff`

Moving

```lean
have h4Diff : 4 ∣ 8 * p.source.d ^ 5 := ...
```

outside the two contradiction blocks removes a small duplicated proof term.

## Required Mathlib imports and import optimization candidates

The standalone source uses `import Mathlib`.

The functionality directly exercised by this theorem is primarily:

- natural-number divisibility and primality,
- parity (`Odd`, `Even`),
- `norm_num`,
- `omega`.

If the standalone file were split into minimal modules, the broad `Mathlib` import could likely be replaced by narrower imports around natural-number prime/divisibility support, parity, `Mathlib.Tactic.Omega`, and `Mathlib.Tactic.NormNum`.

The exact minimal import set is an **optimization candidate**, not a verified claim, because no Lean build is performed in this run.

## Comparator challenge suitability

**Yes; suitability is high.**

A compact challenge can provide

- $A_0B_0=4Q^5$,
- $B_0=A_0+8d^5$,
- `Odd Q`,

and ask for

$$
\exists A_1 B_1,
A_0=2A_1\land Odd(A_1)\land
B_0=2B_1\land Odd(B_1).
$$

The central challenge is structural rather than tactic-only: combine “the product has exactly a $2^2$ contribution” with “the difference carries a $2^3$ contribution” to determine the individual two-adic exponents.

## Next declaration to read

The next declaration is 0330 `GoldenZeroSectorInversionPacket.coprime_Q_d`.

```lean
theorem GoldenZeroSectorInversionPacket.coprime_Q_d
    (p : GoldenZeroSectorInversionPacket) :
    Nat.Coprime (zeroSectorQ p.source.c) p.source.d := by
  have h5d : Nat.Coprime 5 p.source.d :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
  unfold zeroSectorQ
  exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

It composes the packet's existing coprimality facts to prove that the full mass term $Q=5^5c^8$ is coprime to $d$, a fact later used in factor ownership and `coprime_ef_d` arguments.

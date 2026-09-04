# 0032 — `exists_branchB_fifthPowerNormalForm`

## Declaration

```lean
theorem exists_branchB_fifthPowerNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBFifthPowerNormalForm x y z a b
```

## Mathematical statement

Suppose a positive primitive candidate for the fifth-power equation

$$
x^5+y^5=z^5
$$

satisfies the Branch B condition

$$
5\nmid z-y.
$$

Then there exist natural numbers $a,b$ such that the complete normal form holds:

$$
z-y=a^5,\qquad GN5(a^5,y)=b^5,
$$

$$
x=ab,\qquad z=y+a^5,
$$

$$
a>0,\qquad b>0,
$$

$$
\gcd(a,y)=\gcd(a,b)=\gcd(b,y)=1,
$$

$$
5\nmid a.
$$

This is the existence theorem that supplies every field required by the structure `BranchBFifthPowerNormalForm` from the previous article.

## Role in the complete proof

This theorem is the provider that converts factor separation from the Reduction layer into one normal-form packet that later layers can consume directly. The later Branch B, square/golden bridge, and golden-integer arguments can use this structure as their input instead of re-deriving individual facts from the original `CounterexamplePack`.

Thus the theorem does not introduce a new arithmetic obstruction. Its role is to normalize previously proved facts, fix the coordinate $z-y$ as $a^5$, and cache all side conditions needed downstream.

## Direct dependencies

The main repository declarations used directly are:

- `CounterexamplePack`
- `BranchBFifthPowerNormalForm`
- `branchB_fifth_power_factor_split`
- `right_lt_of_fermat5Equation`
- `pow_five_sub_pow_five_eq_gap_mul_GN5`
- `fifth_sub_eq_of_add_eq`
- `gap_pos_of_fermat5Equation`
- `coprime_gap_y_of_counterexamplePack`
- `branchB_coprime_gap_GN5`
- `coprime_GN5_y_of_coprime`

On the Mathlib side, the proof visibly uses at least:

- `mul_pow`
- `Nat.pow_left_injective`
- `Nat.coprime_pow_left_iff`
- `Nat.coprime_pow_right_iff`
- `Nat.Coprime.pow_left`
- `dvd_pow_self`
- `omega`
- `rw`, `simpa`, and `rcases`

## Proof flow

### 1. Extract fifth roots for the gap and `GN5`

```lean
rcases branchB_fifth_power_factor_split hPack hBranch with
  ⟨⟨a, hgap⟩, ⟨b, hGN0⟩⟩
```

This yields

$$
hgap:z-y=a^5,
$$

and

$$
hGN0:GN5(z-y,y)=b^5.
$$

### 2. Move `GN5` to normalized coordinates

```lean
have hGN : GN5 (a ^ 5) y = b ^ 5 := by
  simpa [hgap] using hGN0
```

The structure stores `GN5 (a^5) y`, so the gap equation is used to rewrite the extracted result.

### 3. Reconstruct the full body

The proof obtains `y≤z`, applies the natural-number difference factorization, and constructs

$$
(z-y)GN5(z-y,y)=x^5.
$$

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
  rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
  exact fifth_sub_eq_of_add_eq hPack.hEq
```

### 4. Recover $x=ab$

Substituting $z-y=a^5$ and `GN5(z-y,y)=b^5` gives

$$
(ab)^5=x^5.
$$

Injectivity of the fifth-power map then yields

$$
x=ab.
$$

```lean
have hxpow : (a * b) ^ 5 = x ^ 5 := by
  rw [mul_pow, ← hgap, ← hGN0]
  exact hbody
have hx : x = a * b :=
  (Nat.pow_left_injective (by decide : 5 ≠ 0) hxpow).symm
```

### 5. Recover $z=y+a^5$

From the natural-number difference equation `hgap` and the known ordering, `omega` proves

$$
z=y+a^5.
$$

### 6. Prove positivity of $a$ and $b$

If $a=0$, then $z-y=a^5=0$, contradicting positivity of the gap.

If $b=0$, then $x=ab=0$, contradicting `hPack.hx : 0<x`.

### 7. Descend the three coprimality facts from fifth powers

First, `coprime_gap_y_of_counterexamplePack` and `hgap` give

$$
\gcd(a^5,y)=1,
$$

which `Nat.coprime_pow_left_iff` lowers to

$$
\gcd(a,y)=1.
$$

Next, Branch B coprimality of the gap and `GN5` becomes

$$
\gcd(a^5,b^5)=1.
$$

The left- and right-power coprimality equivalences are applied in sequence to obtain

$$
\gcd(a,b)=1.
$$

Finally, `coprime_GN5_y_of_coprime` is applied to $a^5$ and $y$. After rewriting with `hGN`, it gives

$$
\gcd(b^5,y)=1,
$$

and hence

$$
\gcd(b,y)=1.
$$

### 8. Prove $5\nmid a$

If $5\mid a$, then $5\mid a^5$. Through `hgap`, this implies $5\mid z-y`, contradicting the Branch B hypothesis.

### 9. Construct the structure

The proof closes by passing `a,b` and the twelve field proofs in order:

```lean
exact ⟨a, b, hPack, hBranch, hgap, hGN, hx, hz,
  ha, hb, hay, hab, hby, h5a⟩
```

## Lean-specific processing

### Natural subtraction and ordering

Because `z-y` is truncated subtraction on natural numbers, the factorization at the concrete coordinates requires `y≤z`. The theorem obtains a strict inequality from `right_lt_of_fermat5Equation` and weakens it with `.le`.

### Direction of `rw [← hgap]`

In the proof of `hxpow`, `(a*b)^5` is expanded to `a^5*b^5`, then `← hgap` and `← hGN0` rewrite it back to the already established full body. The rewrite direction is chosen to match `hbody`, not to move toward the final normal form.

### Argument positions in the power-coprime equivalences

`Nat.coprime_pow_left_iff` and `Nat.coprime_pow_right_iff` specify which powered side is being removed. Eliminating powers from both $a^5$ and $b^5$ therefore requires two steps.

### `Nat.pow_left_injective`

The proof supplies the fact that the exponent $5$ is nonzero using `by decide`, and then recovers equality of bases from equality of fifth powers.

## Redundancy and duplication

The proof repeats constant-exponent side conditions such as

```lean
(by decide : 0 < 5)
(by decide : 5 ≠ 0)
```

several times. Since the exponent is a fixed constant, the execution cost is negligible; this is mainly a readability tradeoff.

The construction of `hbody` also closely repeats the same bridge already used inside `branchB_fifth_power_factor_split`. The current implementation keeps each theorem locally readable, but reconstructs the same fifth-power body identity.

## Optimization candidates

The following are unverified proposals, not corrections to the current Lean source.

1. Extract a named lemma from `CounterexamplePack` returning

$$
(z-y)GN5(z-y,y)=x^5.
$$

This would remove duplication between `branchB_fifth_power_factor_split` and the present theorem.

2. Introduce a local wrapper for descending

```lean
Nat.Coprime (a ^ 5) (b ^ 5) → Nat.Coprime a b
```

so the two nested `.mp` applications become easier to read.

3. Positivity of $a$ may admit a shorter proof through an existing `Nat.pow_pos` API. The best lemma name for Mathlib v4.33.0 has not been verified here.

4. Positivity of $b$ could alternatively be derived from `GN5(a^5,y)=b^5` and positivity of `GN5`, but the current route through $x=ab$ appears to require fewer dependencies.

## Required Mathlib imports and import optimization

The verified generated standalone file uses `import Mathlib`. This theorem requires `omega`, natural-number powers, divisibility, coprimality, and gcd-monoid infrastructure.

The individual import lines of the split source `NormalForm.lean` were not available in the repository material retrieved for this article. The following finer imports are therefore only candidates:

- `Mathlib.Data.Nat.GCD.Basic`
- `Mathlib.Algebra.GroupPower.Lemmas`
- `Mathlib.Tactic.Omega`
- the preceding DkMath `Reduction` module

Actual import minimization requires validation with `lake env lean`; no Lean build was run in this task.

## Comparator challenge suitability

The theorem is suitable when split into focused challenges:

1. **Basic** — derive `0<a` from `hgap : z-y=a^5` and positivity of the gap.
2. **Intermediate** — derive `x=a*b` from `hgap`, `hGN0`, and the full-body equality.
3. **Advanced** — recover `Coprime a b` from `Coprime (a^5) (b^5)` using the power-coprime equivalences.

The full provider is long for a single challenge, but it is a good comparison target for structure-construction and proof-organization strategies.

## Verified facts versus proposals

The declaration type, proof steps, used declarations, and following declaration order were verified from the generated repository source `Flt5DkMath/FLT5StandAlone.lean`. The import-splitting suggestions and helper-lemma proposals are unverified.

## Next declaration

```text
DkMath.FLT.Five.BranchBFifthPowerCore
```

This abbreviation describes the remaining unknown arithmetic kernel after the elementary reduction as a universal receiver that maps any `BranchBFifthPowerNormalForm` to `False`. The present theorem is the provider; the next declaration specifies the consumer interface that later arithmetic must satisfy.

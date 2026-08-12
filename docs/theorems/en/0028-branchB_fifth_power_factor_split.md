# 0028 — `branchB_fifth_power_factor_split`

## Declaration

```lean
theorem branchB_fifth_power_factor_split
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ 5) ∧
      (∃ b : ℕ, GN5 (z - y) y = b ^ 5) := by
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
    rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
    exact fifth_sub_eq_of_add_eq hPack.hEq
  exact fifth_power_factor_split (branchB_coprime_gap_GN5 hPack hBranch) hbody
```

## Lean type

The theorem takes a positive primitive FLT5 counterexample candidate `hPack` and the Branch B condition `5 ∤ z-y`, then returns both factors of the fifth-power difference as perfect fifth powers.

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  ((∃ a : ℕ, z - y = a ^ 5) ∧
    (∃ b : ℕ, GN5 (z - y) y = b ^ 5))
```

## Mathematical statement

From `CounterexamplePack` we have

$$
x^5+y^5=z^5.
$$

Since $y<z$, natural-number subtraction behaves as the ordinary difference, and the fifth-power factorization gives

$$
x^5=z^5-y^5=(z-y)GN5(z-y,y).
$$

Under the Branch B hypothesis

$$
5\nmid z-y,
$$

the previously established theorem `branchB_coprime_gap_GN5` gives

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1.
$$

Because the product of these two coprime factors is a fifth power, Article 0027, `fifth_power_factor_split`, yields natural numbers $a,b$ such that

$$
z-y=a^5,
\qquad
GN5(z-y,y)=b^5.
$$

## Role in the complete proof

This theorem is the boundary that converts the arithmetic information of Branch B into an **exact elementary normal form**.

The preceding results factor the counterexample equation into the gap and `GN5`, then prove those factors coprime under the Branch B condition. This theorem feeds both facts into the general power-splitting engine and turns them into two fifth-power equations that later layers can consume directly.

At this point, closing Branch B only requires an independent obstruction showing that `GN5 (z-y) y` cannot be a fifth power. The immediately following theorem, `branchB_false_of_GN5_not_fifth_power`, sends the second component produced here to such an obstruction.

## Direct dependencies

1. `CounterexamplePack`
   - Stores positivity, `Nat.Coprime x y`, and `Fermat5Equation x y z`.
2. `right_lt_of_fermat5Equation`
   - Derives $y<z$ from `hPack.hx` and `hPack.hEq`.
3. `pow_five_sub_pow_five_eq_gap_mul_GN5`
   - Gives $z^5-y^5=(z-y)GN5(z-y,y)$ under $y\le z$.
4. `fifth_sub_eq_of_add_eq`
   - Converts the FLT5 equation into $z^5-y^5=x^5$.
5. `branchB_coprime_gap_GN5`
   - Gives coprimality of the gap and `GN5` from `hPack` and `5∤z-y`.
6. `fifth_power_factor_split`
   - Splits a coprime product that is a fifth power into two fifth powers.

## Proof flow

1. Obtain $y<z$ from `right_lt_of_fermat5Equation`, then weaken it to $y\le z` with `.le`.

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
```

2. Rewrite the factorization theorem backwards and use the difference form of the counterexample equation to build the product identity.

```lean
have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
  rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
  exact fifth_sub_eq_of_add_eq hPack.hEq
```

3. Pass the Branch B coprimality result and `hbody` to `fifth_power_factor_split`.

```lean
exact fifth_power_factor_split
  (branchB_coprime_gap_GN5 hPack hBranch) hbody
```

4. The general theorem already returns exactly the target conjunction, so no further unpacking or reconstruction is required.

## Lean-specific processing

### Order proof for natural-number subtraction

Subtraction on `Nat` is truncated. Therefore the factorization theorem connecting the abstract difference to the concrete term `z-y` requires `y ≤ z`. This order fact is not stored directly in `CounterexamplePack`; it is derived from the equation and `x>0`.

### Rewrite direction

To transform the left-hand side of `hbody` into a fifth-power difference, the theorem is used backwards:

```lean
rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
```

After this rewrite, the goal is exactly `z^5-y^5=x^5`, which is supplied by `fifth_sub_eq_of_add_eq`.

### Structure projections

The proof passes `hPack.hx` and `hPack.hEq` explicitly, making the source of positivity and the equation visible. The complete structure `hPack` is then reused unchanged by the Branch B coprimality theorem.

### Exact agreement of conclusion shapes

Type inference instantiates the general variables `g,n` in `fifth_power_factor_split` as `z-y` and `GN5 (z-y) y`. Its returned conjunction is literally the goal, so `simpa` is unnecessary.

## Redundancy and duplication

The theorem contains no repeated prime-divisor argument or polynomial expansion. It is a thin orchestration theorem that composes already established APIs in three steps.

The construction of `hyz` and `hbody` may appear again in later normal-form providers. If the same proof fragment occurs in several modules, it would be worth extracting a dedicated theorem returning

```lean
(z - y) * GN5 (z - y) y = x ^ 5
```

from a `CounterexamplePack`. The repository-wide duplication count has not been verified in this article.

## Optimization candidates

1. Introduce a theorem such as `counterexamplePack_gap_mul_GN5_eq_fifth` to share the `hyz` and `hbody` construction.
2. The present proof exposes its dependencies clearly and is resistant to change; compressing it into tactics merely to save lines is not recommended.
3. `hyz` could be inlined into the proof of `hbody`, but doing so would hide the safety condition for natural-number subtraction.
4. If the later structured normal form is the main API, keep this theorem as the elementary bridge and provide the structure-valued theorem separately, as the current layering does.

## Required Mathlib imports and import optimization

The generated standalone artifact is checked under `import Mathlib`; the minimal import set for this theorem alone is not established.

Direct requirements include natural-number order, subtraction, powers, `Nat.Coprime`, the gcd/unit machinery used by Article 0027, and the repository declarations from `Basic`, `GN5`, and `Reduction`. In the modular source, many Mathlib dependencies may already arrive transitively from the earlier modules.

A minimal-import audit would need to check modules supplying:

1. Natural-number powers, order, and subtraction.
2. Gcd and `Nat.Coprime`.
3. `GCDMonoid`, `IsUnit`, and `exists_eq_pow_of_mul_eq_pow`.
4. Equality lemmas used by `rw`.

The exact Mathlib module names and sufficiency are unverified because no Lean build was run.

## Comparator challenge suitability

This theorem is suitable. The arithmetic steps are short, but it tests whether an implementation can discover and compose the existing APIs in the correct order.

### Challenge sketch

```lean
{x y z : ℕ}
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
⊢ (∃ a : ℕ, z - y = a ^ 5) ∧
    (∃ b : ℕ, GN5 (z - y) y = b ^ 5)
```

Possible comparison approaches:

1. The current three-lemma composition.
2. A `calc`-based construction of the fifth-power body identity.
3. Reproving factorization and coprimality locally.
4. First introducing a dedicated `CounterexamplePack` body theorem.
5. Packing the conclusion directly into a normal-form structure.

Evaluation criteria are dependency reuse, safety around natural-number subtraction, proof length, semantic clarity of local lemmas, and resistance to Mathlib API changes. The strongest comparator solution should favor correct reuse of kernel-checked APIs over reimplementing the number theory.

## Facts versus interpretation

The declaration type, proof body, direct dependencies, and the fact that `branchB_false_of_GN5_not_fifth_power` follows immediately afterward were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

Describing this theorem as the exact elementary normal-form boundary is an interpretation supported by the source comment and the following declarations. Extracting a dedicated body theorem, minimal imports, and alternative Comparator solutions are unverified proposals. Existing PDFs are narrative aids; when they differ from the Lean declarations, the Lean source is authoritative.

## Next theorem to read

```lean
DkMath.FLT.Five.branchB_false_of_GN5_not_fifth_power
```

It takes an independently supplied obstruction

$$
\neg\exists b\in\mathbb N,
\quad GN5(z-y,y)=b^5
$$

and directly contradicts the second component produced by this theorem, deriving `False` from a Branch B counterexample candidate.

# 0048 — `five_not_dvd_x_of_branchB`

## 1. Declaration

```lean
theorem five_not_dvd_x_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ¬ 5 ∣ x := by
  intro h5x
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have h5x5 : 5 ∣ x ^ 5 := h5x.trans (dvd_pow_self x (by decide))
  have h5body : 5 ∣ Body5 (z - y) y := by
    rw [hbody]
    exact h5x5
  unfold Body5 at h5body
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5body with h5gap | h5GN
  · exact hBranch h5gap
  · exact (five_not_dvd_GN5_of_five_not_dvd_gap hBranch) h5GN
```

Its fully qualified name is `DkMath.FLT.Five.five_not_dvd_x_of_branchB`.

## 2. Lean type

```lean
{x y z : ℕ} →
CounterexamplePack x y z →
(¬ 5 ∣ z - y) →
¬ 5 ∣ x
```

Given a positive primitive Fermat counterexample candidate `hPack` and the Branch B condition `hBranch`, the theorem concludes that the first coordinate `x` is not divisible by five.

## 3. Mathematical statement

From `CounterexamplePack x y z` we have

$$
x^5+y^5=z^5,
$$

while the Branch B condition is

$$
5\nmid(z-y).
$$

Rewriting the Fermat equation in gap coordinates gives

$$
Body5(z-y,y)=(z-y)GN5(z-y,y)=x^5.
$$

If $5\mid x$, then $5\mid x^5$, hence

$$
5\mid (z-y)GN5(z-y,y).
$$

Because 5 is prime, either

$$
5\mid(z-y)
$$

or

$$
5\mid GN5(z-y,y).
$$

The first alternative contradicts the Branch B hypothesis, and the second contradicts article 0047, `five_not_dvd_GN5_of_five_not_dvd_gap`. Therefore $5\nmid x$.

## 4. Role in the full proof

This lemma is preprocessing for the signed Branch A routing. In Branch B, neither the gap nor the residual factor is divisible by five. Since their product is the perfect fifth power `x^5`, this theorem confirms that the base `x` itself also avoids the exceptional prime five.

The following modular and signed branch lemmas organize which of the two differences `z-y` and `z-x` is divisible by five and use the fact that fifth powers reduce to their bases modulo five. This theorem supplies the local guard that `x` itself contains no factor five.

## 5. Direct dependencies

1. `CounterexamplePack`

   The structure carrying positivity, primitivity, and the Fermat equation.

2. `right_lt_of_fermat5Equation`

   Derives $y<z$, hence $y\le z$, from `hPack.hx` and `hPack.hEq`.

3. `Body5`

   The fifth-power body defined by `Body5 g y = g * GN5 g y`.

4. `body5_eq_fifth_power_of_fermat`

   The bridge deriving `Body5 (z-y) y = x^5` from the Fermat equation.

5. `dvd_pow_self`

   Gives $x\mid x^5$, which is composed with `h5x : 5 ∣ x` to obtain $5\mid x^5$.

6. `Nat.Prime.dvd_mul`

   Splits divisibility of a product by the prime five into divisibility of one factor or the other.

7. `five_not_dvd_GN5_of_five_not_dvd_gap`

   Article 0047, which derives $5\nmid GN5(z-y,y)$ from the Branch B condition.

## 6. Proof flow

1. Since the conclusion is a negation, introduce the contrary assumption `h5x : 5 ∣ x`.
2. Obtain `hyz : y ≤ z` from `right_lt_of_fermat5Equation`.
3. Use `body5_eq_fifth_power_of_fermat` to derive `Body5 (z-y) y = x^5`.
4. Combine `h5x` with `dvd_pow_self` to prove $5\mid x^5$.
5. Rewrite by `hbody` to obtain $5\mid Body5(z-y,y)$.
6. Unfold `Body5` and use primality of five to split into the gap and `GN5` cases.
7. Close the gap case with `hBranch` and the `GN5` case with article 0047.

## 7. Lean-specific processing

### 7.1 Negation as a function

The goal `¬ 5 ∣ x` is definitionally `(5 ∣ x) → False`, so the proof starts with `intro h5x`. Each final branch applies a negation hypothesis to a divisibility proof.

### 7.2 Narrow order conversion via `.le`

`right_lt_of_fermat5Equation ...` returns `y < z`. The suffix `.le` converts it to `y ≤ z`, which is exactly the hypothesis required by `body5_eq_fifth_power_of_fermat` because natural-number subtraction is involved.

### 7.3 Transitivity of divisibility

```lean
h5x.trans (dvd_pow_self x (by decide))
```

composes $5\mid x$ with $x\mid x^5$. The `by decide` term discharges the side condition that the exponent five is nonzero.

### 7.4 Prime-product splitting after unfolding

`Body5` must be exposed as a product before `Nat.Prime.dvd_mul` applies. Thus `unfold Body5 at h5body` changes the hypothesis into divisibility of `(z-y) * GN5 ...`, and `rcases ... with h5gap | h5GN` handles the resulting disjunction.

### 7.5 Concrete primality by `decide`

`Nat.Prime 5` is a closed decidable proposition, so it is supplied as `(by decide : Nat.Prime 5)`.

## 8. Redundancy and duplication

The proof is short and contains little substantive duplication. Some local compression is possible:

- `hbody` and `h5body` could potentially be combined with a `simpa` step.
- `(by decide : Nat.Prime 5)` appears in neighboring five-adic lemmas as well.
- The two terminal branches could be folded into an `Or.elim` expression.

The current form is nevertheless preferable for exposition because it visibly separates the equation bridge, transfer of divisibility to the fifth power, and the prime-product split.

## 9. Optimization candidates

### 9.1 Construct body divisibility with `simpa`

One may be able to shorten the construction to

```lean
have h5body : 5 ∣ Body5 (z - y) y := by
  simpa [hbody] using h5x5
```

but this depends on rewrite orientation. The existing `rw [hbody]` is stable and explicit.

### 9.2 A dedicated prime divisor lemma for `Body5`

If the pattern recurs, one could extract

```lean
Nat.Prime p → p ∣ Body5 g y → p ∣ g ∨ p ∣ GN5 g y.
```

At present, however, unfolding `Body5` and using the standard library API is already concise.

### 9.3 Share the proof that five is prime

A local theorem such as `five_prime : Nat.Prime 5` could remove repeated `by decide` terms. Since the proposition is closed and trivial for the kernel to decide, the extra name may not justify itself.

## 10. Required Mathlib imports and import optimization

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`, and the theorem is confirmed to work in that environment.

Its direct requirements are approximately:

- order and subtraction on natural numbers,
- divisibility transitivity and `dvd_pow_self`,
- `Nat.Prime.dvd_mul`,
- `decide` for closed propositions,
- upstream declarations `CounterexamplePack`, `Body5`, the Fermat bridge, and article 0047.

In the generated artifact this declaration belongs to the `SignedBranchA.lean` section. The exact imports of the split source module were not available in this repository, so a minimal import list is not asserted. Presumably the upstream Branch A, Provider, and GN5 modules transitively provide the required Mathlib components. Import minimization should be checked against the split source in the original `dkmath` repository with per-file compilation or an import-audit tool. No Lean build was run for this article.

## 11. Comparator challenge suitability

 **Suitable.** 

```lean
theorem challenge
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ¬ 5 ∣ x := by
  sorry
```

Useful comparison points are:

- whether the solver normalizes the Fermat equation to `Body5 = x^5`,
- whether it constructs $5\mid x^5$ by divisibility transitivity,
- whether it unfolds `Body5` and applies `Nat.Prime.dvd_mul`,
- whether it closes the two branches with the Branch B hypothesis and article 0047,
- whether it reuses existing bridges instead of expanding the polynomial or relying on broad automation.

This is a good challenge for measuring dependency tracking and practical command of Lean's divisibility API.

## 12. Sources and reservations

The declaration name, type, proof body, membership in the generated `SignedBranchA.lean` section, and the fact that the next declaration is `pow_five_mod_five` were checked in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The mathematical explanation takes this kernel-checked Lean code as its primary source.

The existing Japanese and English PDFs provide narrative context for the signed five-adic and golden-descent layers, while the Lean source remains authoritative for the exact declaration. The precise import line of the split `SignedBranchA.lean` source was not available and is explicitly left unverified.

## 13. Next theorem to read

The next theorem should be

```lean
DkMath.FLT.Five.pow_five_mod_five
```

It proves

$$
n^5\bmod 5=n\bmod 5,
$$

reducing fifth powers to their bases modulo five. It is the next foundational lemma for organizing the signed Branch A / Branch B routing by modular arithmetic.

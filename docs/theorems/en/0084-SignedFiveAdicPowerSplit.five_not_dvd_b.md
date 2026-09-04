# 0084 — `SignedFiveAdicPowerSplit.five_not_dvd_b`

## Lean type

```lean
theorem SignedFiveAdicPowerSplit.five_not_dvd_b
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) : ¬ 5 ∣ s.b := by
  intro h5b
  have h25 : 25 ∣ s.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [s.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [s.fiveAdic.residual_mod_twentyFive] at hzero
  omega
```

## Mathematical statement

In `SignedFiveAdicPowerSplit`, the residual is decomposed as

$$
\mathrm{residual}=5b^5.
$$

This theorem states that the fifth-power base `b` contains no further factor of 5, namely

$$
5\nmid b.
$$

It can be viewed as the power-split-coordinate form of the fact that the 5-adic valuation of the residual is exactly one.

## Role in the overall proof

0083 `SignedFiveAdicPowerSplit` records the exact power split

$$
\mathrm{carrier}=5^4a^5,\qquad
\mathrm{residual}=5b^5,\qquad
\mathrm{distinguished}=5ab.
$$

However, `residual = 5b^5` alone does not exclude an additional factor of 5 inside `b`.

By proving $5\nmid b$, this theorem guarantees that after stripping the ramified prime 5 exactly once from the residual, the remaining part is coprime to 5. The immediately following theorem `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5` uses this fact to build coprimality between a left factor containing a high power of 5 and $b^5$.

## Direct dependencies

- `SignedFiveAdicPowerSplit`
  - especially `s.residual_eq : s.fiveAdic.residual = 5 * s.b ^ 5`
- `SignedFiveAdicPacket.residual_mod_twentyFive`
  - `s.fiveAdic.residual % 25 = 5`
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

This theorem does not directly mention the earlier `GN5`, `SumGN5`, orientation split, or gcd proof. Those facts have already been packaged into fields of `SignedFiveAdicPowerSplit` and `SignedFiveAdicPacket`.

## Proof flow

1. Introduce the negated divisibility hypothesis `h5b : 5 ∣ s.b`.
2. Expand `h5b` as `⟨c, hc⟩`, obtaining $b=5c$.
3. Substitute into `s.residual_eq`. Then

$$
\mathrm{residual}=5(5c)^5=5^6c^5,
$$

so in particular $25\mid\mathrm{residual}$.
4. `Nat.mod_eq_zero_of_dvd h25` gives

$$
\mathrm{residual}\bmod25=0.
$$

5. Rewrite with the packet field

$$
\mathrm{residual}\bmod25=5.
$$

This produces the contradiction $5=0$, closed by `omega`.

## Lean-specific processing

`¬ 5 ∣ s.b` is a function type, so `intro h5b` assumes a divisibility witness.

```lean
rcases h5b with ⟨c, hc⟩
```

expands natural-number divisibility into a concrete product representation. `use 5 ^ 4 * c ^ 5` explicitly supplies the witness for `25 ∣ residual`, and `ring` normalizes the resulting powers and products.

The final step converts divisibility into a remainder equation using `Nat.mod_eq_zero_of_dvd`, then collides it with the stored field `residual_mod_twentyFive`. `omega` closes the resulting natural-number arithmetic contradiction.

## Redundancy and duplication

Later source code contains the same proof pattern again at another packet layer: assume $5\mid b$, derive $25\mid residual$, and contradict `residual % 25 = 5`. Thus the local proof is short, but the development as a whole duplicates the same mod-25 obstruction more than once.

Also, `SignedFiveAdicPacket` already stores `residual_padicValNat : padicValNat 5 residual = 1`, so it may be possible to derive $5\nmid b$ through the valuation API instead. Whether that route is shorter with the current Mathlib API has not been checked; this is therefore a conjectural optimization.

## Optimization candidates

A natural abstraction would be a general lemma of the following conceptual shape.

```lean
-- conceptual form
theorem not_dvd_base_of_mul_pow_mod_sq
    (p x b n : ℕ)
    (hshape : x = p * b ^ n)
    (hmod : x % (p ^ 2) = p) :
    ¬ p ∣ b := ...
```

A real statement would need suitable assumptions such as primality, `n > 0`, and `p > 1`. In the FLT5-specific case, however, $p=5$ and $n=5$ are fixed, so keeping the present few-line arithmetic proof may still be preferable for readability.

Another comparison is API design: use `residual_mod_twentyFive` as the primary fact, or derive the theorem from `residual_padicValNat = 1`. The mod-25 route is elementary and has a short kernel trace; the valuation route would align more closely with later 5-adic reasoning.

## Required Mathlib imports and import optimization

The standalone artifact on the museum branch is built with `import Mathlib`, so this theorem is confirmed to work with the full Mathlib import.

The proof visibly needs only natural-number divisibility/remainder support plus the `ring` and `omega` tactics. Therefore its true minimal import set should be much smaller than `Mathlib`. However, the exact import list of the split source module `SignedFiveAdicPowerSplit.lean` was not independently verified on this museum branch, so no precise minimal import path is asserted here.

A safe optimization procedure would inspect the source-module import graph and then test whether the theorem builds with only the modules needed for natural-number divisibility/mod together with the Mathlib `Ring` and `Omega` tactics. No Lean build is performed in this museum pass.

## Comparator challenge suitability

Yes. This theorem makes a small, self-contained comparison task.

Three useful variants are:

1. the current mod-25 proof;
2. a valuation proof from `padicValNat 5 residual = 1`;
3. a generalized lemma deriving `p ∤ b` from `x = p*b^n` and `x % p^2 = p`.

Good evaluation axes are proof length, import footprint, tactic dependence, reuse potential, and compatibility with the downstream API.

## PDF correspondence

The existing Japanese and English PDFs are treated as narrative background for this development, but the GitHub code search temporarily returned a 502 during this pass, and the exact PDF location corresponding to this short theorem could not be identified uniquely. Therefore no PDF page or section number is guessed.

The final formal basis for the statement and proof in this article is the actual Lean declaration in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next theorem to read

The next declaration should be

```lean
theorem SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (5 ^ 15 * s.a ^ 20) (s.b ^ 5) := by
  ...
```

It combines this theorem's $5\nmid b$ with `s.coprime_a_b` to construct

$$
\gcd(5^{15}a^{20},b^5)=1.
$$

This is the factor-separation statement needed after stripping the ramifier 5, in a form suitable for the later square/golden bridge.

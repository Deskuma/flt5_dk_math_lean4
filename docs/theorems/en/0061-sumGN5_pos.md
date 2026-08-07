# 0061 — `sumGN5_pos`

## 1. Lean type

```lean
theorem sumGN5_pos
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    0 < SumGN5 u v := by
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    have hv4 : 0 < v ^ 4 := pow_pos hv 4
    omega
  · rw [SumGN5, if_neg h]
    have hu4 : 0 < u ^ 4 := pow_pos hu 4
    omega
```

## 2. Mathematical statement

For positive natural numbers `u`,`v`, the fifth-power-sum residual `SumGN5 u v` defined in article 0059 is positive.

$$
0<u,\quad 0<v
\Longrightarrow
0<\operatorname{SumGN5}(u,v).
$$

According to the ordering of `u` and `v`, `SumGN5` is represented by one of two polynomials with nonnegative coefficients. In the `v ≤ u` branch the final term is $v^4>0$; in the opposite branch the final term is $u^4>0$. Hence the whole polynomial is positive.

## 3. Role in the overall proof

This theorem supplies nonzeroness of the residual in the sum orientation. In the later `sumGap` branch of `nonempty_signedFiveAdicPacket_of_normalForm`, it is used directly as

```lean
have hresPos : 0 < SumGN5 u v := sumGN5_pos hPack.hx hPack.hy
```

From this positivity one obtains `hresPos.ne'`, which is passed to `padicValNat_carrier_shape_of_mul_eq_fifth`. This makes it safe to use additivity of the 5-adic valuation in the product

$$
(u+v)\,SumGN5(u,v)=w^5.
$$

Thus this theorem is a small but necessary bridge turning the factorization identity from 0060 into a genuinely nonzero residual that the exact five-adic packet can consume.

## 4. Direct dependencies

The only direct user-defined dependency is 0059 `SumGN5`.

On the Lean / Mathlib side the proof uses:

- `by_cases h : v ≤ u`
- `rw [SumGN5, if_pos h]` / `rw [SumGN5, if_neg h]`
- `pow_pos`
- `omega`

It does not logically depend on 0060 `add_mul_sumGN5_eq_add_pow_five`. Positivity is proved directly from the definition of `SumGN5`, not from the factorization equation.

## 5. Proof flow

1. Split on whether `v ≤ u`, matching the two branches of the `SumGN5` definition.
2. In the `v ≤ u` branch, derive `0 < v^4` from `hv : 0 < v` using `pow_pos hv 4`.
3. Every other term of the expanded `SumGN5` is a natural number and therefore nonnegative; since the sum contains the strictly positive final term `v^4`, `omega` closes the positivity goal.
4. In the `¬ v ≤ u` branch, use `hu : 0 < u` analogously to obtain `0 < u^4`, then close with `omega` using the final term `u^4`.

## 6. Lean-specific processing

Mathematically the proof is only: “a sum of nonnegative terms containing one strictly positive term is strictly positive.” Because `SumGN5` is defined piecewise by `if v ≤ u then ... else ...`, Lean must first expose the relevant branch with `by_cases` and `rw`.

`pow_pos hv 4` / `pow_pos hu 4` explicitly identifies the term responsible for strict positivity. The final `omega` then uses natural-number arithmetic and order information without requiring separate nonnegativity proofs for every other term.

Unlike article 0060, there is no need to eliminate `Nat.sub` with `Nat.exists_eq_add_of_le`. Whatever values the subtraction terms take, they are natural numbers, and positivity of the final fourth-power term alone is enough.

## 7. Redundancy and duplication

The two branches are completely symmetric. The only difference is whether the positivity witness is `v^4` or `u^4`. This duplication arises naturally from directly unfolding the piecewise definition of `SumGN5`.

The local names `hv4` / `hu4` make the proof intent explicit. If brevity were the only goal, they could be replaced by anonymous local facts such as `have : 0 < v ^ 4 := pow_pos hv 4`.

## 8. Optimization candidates

The most natural structural optimization would be to prove a symmetry lemma for `SumGN5` first, prove only one branch essentially, and transport the result by swapping the arguments. For this theorem alone, however, adding a symmetry API may cost more structure than it saves.

Another comparison candidate is whether a `positivity`-oriented proof can discharge the expanded polynomial directly. The current `pow_pos` + `omega` proof is short and makes the strictly positive term explicit, so it has good auditability.

## 9. Required Mathlib imports and import optimization

The generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch is confirmed to use `import Mathlib`. This theorem specifically needs natural-number order, `pow_pos`, the `omega` tactic, and the local module containing `SumGN5`.

The exact imports of the original split file `DkMath/FLT/Five/SignedFiveAdic.lean` cannot be recovered with certainty from the standalone artifact, so concrete minimal import names are not guessed here. An import-minimization pass should first separate the tactic import providing `omega` from the library location of `pow_pos`, using `#print` / import tracing.

## 10. Comparator challenge suitability

This theorem is well suited to a Comparator challenge because the alternatives are small and easy to measure.

- A: current `by_cases` + `pow_pos` + `omega`
- B: a proof centered on `positivity`
- C: prove one branch and transport it using a symmetry lemma for `SumGN5`
- D: derive positivity indirectly from the factorization in 0060 and positivity of $u^5+v^5$

Useful metrics are proof length, number of piecewise unfoldings, required imports, automation dependence, readability of intent, and downstream API reuse. Variant D is mathematically indirect and would need extra work to recover positivity of one factor from a positive product, so it is likely inferior to the current proof.

## 11. Evidence and conjectural points

The confirmed source is the generated `DkMath/FLT/Five/SignedFiveAdic.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch. It confirms the theorem type, proof body, and the direct downstream use `sumGN5_pos hPack.hx hPack.hy` in the `sumGap` branch of `nonempty_signedFiveAdicPacket_of_normalForm`.

The standalone artifact is also confirmed to use `import Mathlib`. The minimal imports of the original split file, and the exact pages corresponding to this lemma in the existing Japanese and English PDFs, were not established in this run, so no details about them are guessed.

## 12. Next theorem to read

The next unexplained lemma in dependency order is the immediately following private lemma in the same `SignedFiveAdic.lean` section:

```lean
private theorem five_not_dvd_left_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ u
```

It is the entry point for the modulo-25 residual calculation in the sum orientation: from `Nat.Coprime u v` and $5\mid u+v$, it extracts $5\nmid u$.
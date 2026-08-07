# 0060 — `add_mul_sumGN5_eq_add_pow_five`

## 1. Lean type

```lean
theorem add_mul_sumGN5_eq_add_pow_five (u v : ℕ) :
    (u + v) * SumGN5 u v = u ^ 5 + v ^ 5 := by
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    subst u
    simp only [Nat.add_sub_cancel_left]
    ring
  · rw [SumGN5, if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
    subst v
    simp only [Nat.add_sub_cancel_left]
    ring
```

## 2. Mathematical statement

For all natural numbers `u`,`v`, the `SumGN5` defined in the previous article is the residual of the sum of fifth powers and satisfies

$$
(u+v)\,\operatorname{SumGN5}(u,v)=u^5+v^5.
$$

This is the usual alternating-sign factorization

$$
u^5+v^5=(u+v)(u^4-u^3v+u^2v^2-uv^3+v^4)
$$

translated into the piecewise representation that handles `Nat.sub` safely.

## 3. Role in the whole proof

In the sum orientation, `Fermat5Equation u v w` gives `u^5+v^5=w^5`. This theorem turns it into

$$
(u+v)\,SumGN5(u,v)=w^5,
$$

matching the difference orientation's shape `gap * GN5 = fifth power`. This common “carrier × residual = fifth power” interface is one of the reasons the later exact five-adic packet can treat the sum and difference orientations uniformly.

## 4. Direct dependencies

The direct project dependency is 0059 `SumGN5`. On the Lean / Mathlib side the proof uses `by_cases`, `Nat.exists_eq_add_of_le`, `Nat.le_of_not_ge`, `Nat.add_sub_cancel_left`, and `ring`.

## 5. Proof flow

1. Split on `v ≤ u`, matching the two branches of `SumGN5`.
2. In the `v ≤ u` branch, obtain `u = v + d` and substitute for `u`.
3. Simplify `u-v` to `d` via `Nat.add_sub_cancel_left`.
4. Close the remaining polynomial identity with `ring`.
5. In the other branch derive `u ≤ v`, write `v = u + d`, and repeat the symmetric argument.

## 6. Lean-specific processing

Mathematically this is only a polynomial factorization, but over `ℕ`, `u-v` is truncated subtraction. Therefore the proof cannot simply ask `ring` to interpret subtraction as a signed difference. The order hypothesis is converted with `Nat.exists_eq_add_of_le` into an additive decomposition, after which substitution removes the truncated subtraction and leaves a pure semiring polynomial identity.

The `simp only [Nat.add_sub_cancel_left]` step after `subst u` / `subst v` is the key bridge that removes the natural-subtraction representation issue.

## 7. Redundancy and duplication

The two branches are nearly identical under exchange of `u` and `v`. This duplication mirrors the piecewise definition of `SumGN5` and keeps both `Nat.sub` safety conditions explicit for auditing.

## 8. Optimization candidates

A shared helper lemma for the positive-coefficient polynomial in variables `a,d : ℕ` could prove the factorization once, leaving only substitutions in the two branches. Another option is to first prove symmetry of `SumGN5` and transport one branch to the other. The current proof is already short, however, and explicitly exposes both natural-subtraction branches.

## 9. Required Mathlib imports and import optimization

The checked generated file `Flt5DkMath/FLT5StandAlone.lean` imports all of `Mathlib`. This theorem specifically needs the `ring` tactic together with natural-number order and subtraction lemmas. The exact import list of the original split `SignedFiveAdic.lean` could not be retrieved on the target branch, so no exact minimal import module is asserted here. Unlike `SumGN5` alone, this theorem does require an import providing `ring`.

## 10. Comparator challenge suitability

It is well suited. Candidate A is the current two-branch `ring` proof; B factors out a common helper-polynomial lemma; C proves the standard factorization over `ℤ` and transports it back to `ℕ`. Useful comparison metrics are proof length, cast count, number of `Nat.sub` helper steps, imports, and downstream reuse.

## 11. Evidence and conjecture

The confirmed source is the generated `SignedFiveAdic.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch, where both the theorem type and complete proof body were inspected. Searching for the existing PDFs hit an upstream error in the GitHub connector during this run, so no PDF page number or narrative detail is guessed here.

## 12. Next theorem to read

Next is

```lean
theorem sumGN5_pos
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    0 < SumGN5 u v
```

It follows the factorization identity by proving that the sum residual is genuinely positive, supplying a positivity condition needed by later five-adic packet construction.

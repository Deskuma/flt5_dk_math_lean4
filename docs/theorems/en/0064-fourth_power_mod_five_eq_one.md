# 0064 — `fourth_power_mod_five_eq_one`

## Lean type

```lean
private theorem fourth_power_mod_five_eq_one
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    n ^ 4 % 5 = 1 := by
  rw [Nat.pow_mod]
  have hnlt : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hn0 : n % 5 ≠ 0 := by
    intro hn0
    exact h5n (Nat.dvd_of_mod_eq_zero hn0)
  interval_cases h : n % 5
  · exact (hn0 rfl).elim
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]
```

This declaration is `private` and is used only as a local lemma inside `SignedFiveAdic.lean`.

## Mathematical statement

If a natural number `n` is not divisible by 5, then its fourth power is congruent to 1 modulo 5.

$$
5\nmid n \Longrightarrow n^4\equiv 1\pmod 5.
$$

This is the special case of Fermat's little theorem for the prime 5. A nonzero residue class is one of $1,2,3,4$, and each of their fourth powers returns to 1 modulo 5.

## Role in the overall proof

This is a foundational lemma for analyzing the sum orientation of `SumGN5` modulo 25. The immediately following theorem `fourth_power_zmod25_decomposition` uses it to obtain an integer decomposition `n^4 = 1 + 5q`, then transports that identity into `ZMod 25` as

$$
(n: \mathrm{ZMod}\ 25)^4 = 1 + 5q.
$$

That decomposition is then used in the later computation of `SumGN5_cast_mod25_eq_five`.

Thus this lemma converts the facts `5 ∤ u` and `5 ∤ v` obtained around Articles 0062–0063 into fourth-power residue information.

## Direct dependencies

- `Nat.pow_mod`
- `Nat.mod_lt`
- `Nat.dvd_of_mod_eq_zero`
- `interval_cases`
- `norm_num`

It does not directly depend on Articles 0062–0063, but later code feeds the nondivisibility facts produced there into this lemma.

## Proof flow

1. Rewrite `n ^ 4 % 5` using `Nat.pow_mod`, reducing to the residue `n % 5`.
2. Obtain `n % 5 < 5` from `Nat.mod_lt`.
3. Derive `n % 5 ≠ 0` from `5 ∤ n`.
4. Use `interval_cases h : n % 5` to split exhaustively into residues `0,1,2,3,4`.
5. The residue-0 branch contradicts `hn0`.
6. The residues `1,2,3,4` are discharged by `norm_num`.

## Lean-specific processing

Mathematically this is a one-line consequence of Fermat's little theorem, but the implementation performs an explicit finite residue classification. `interval_cases` uses the bound `hnlt : n % 5 < 5` to enumerate the possible natural values.

The proof also uses `Nat.dvd_of_mod_eq_zero` to turn residue zero back into a divisibility statement and contradict `h5n`.

## Redundancy and duplication

The four `norm_num [h]` branches are structurally identical. The tail can potentially be compressed, for example:

```lean
interval_cases h : n % 5
· exact (hn0 rfl).elim
all_goals norm_num [h]
```

The statement itself is also a special case of a standard general theorem, so the finite split could in principle be replaced by an appropriate Mathlib version of Fermat's little theorem.

## Optimization candidates

The first candidate is to use Fermat's little theorem for `Nat.Prime` or the unit group of `ZMod 5`. On the other hand, because the modulus is fixed at 5, the current finite proof is small and very auditable.

A safe local simplification is to merge the four repeated `norm_num` branches after `interval_cases`.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact is confirmed to use `import Mathlib`. The split source file `DkMath/FLT/Five/SignedFiveAdic.lean` itself could not be retrieved from this museum branch, so the exact minimal imports are not confirmed.

As an inference, the proof requires modules providing natural-number modular arithmetic, the `interval_cases` tactic, and the `norm_num` tactic. Exact import minimization should remain uncommitted until the split source can be checked and built directly.

## Comparator challenge suitability

This is a good Comparator challenge. The statement is short, the input and output are clear, and several proof strategies are available:

- Current: finite enumeration with `interval_cases`
- Candidate A: Fermat's little theorem
- Candidate B: a `ZMod 5` proof
- Candidate C: recoding as a finite decidable proposition and using `decide` / `native_decide`

Useful comparison axes are proof length, import footprint, kernel transparency, and generalizability.

## Evidence and inference

The theorem name, type, proof body, and immediate consumer were confirmed in `Flt5DkMath/FLT5StandAlone.lean`. A concrete page in the existing Japanese or English PDFs corresponding to this local lemma was not confirmed in this run, so no PDF-specific narrative has been invented.

## Next theorem to read

```lean
private theorem fourth_power_zmod25_decomposition
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    ∃ q : ℕ, (n : ZMod 25) ^ 4 = 1 + 5 * (q : ZMod 25)
```

It lifts the modulo-5 fourth-power congruence from this article into a first-order five-adic decomposition usable inside `ZMod 25`.

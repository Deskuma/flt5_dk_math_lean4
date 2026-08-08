# 0071 — `not_twentyFive_dvd_of_mod_eq_five`

## Lean type

```lean
private theorem not_twentyFive_dvd_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ¬ 25 ∣ n := by
  intro h25
  have hzero : n % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
  omega
```

This declaration is `private`. Inside `SignedFiveAdic.lean`, it is a local bridge that converts the remainder information `n % 25 = 5` into the non-divisibility statement `¬ 25 ∣ n`.

## Mathematical statement

If a natural number `n` satisfies

$$
n\bmod 25=5,
$$

then

$$
25\nmid n.
$$

Indeed, if instead $25\mid n$, the remainder modulo 25 would have to be $0$. That contradicts the assumption that the remainder is $5$.

## Role in the full proof

Article 0068 converts an equality in `ZMod 25` into `n % 25 = 5`. Articles 0069–0070 extract `5 ∣ n` from the same information. The present article 0071 extracts the opposite boundary,

$$
25\nmid n.
$$

Thus 0070 and 0071 together give

$$
5\mid n,\qquad 25\nmid n,
$$

and the immediately following theorem `padicValNat_five_eq_one_of_dvd_not_sq` converts these two facts into

$$
v_5(n)=1.
$$

In the actual FLT5 proof, this lemma is used for both the difference orientation residual `GN5 (w-v) v` and the sum orientation residual `SumGN5 u v`. In each branch it supplies the input that rules out a second factor of 5 and thereby fixes the residual 5-adic valuation at 1.

## Direct dependencies

- `Nat.mod_eq_zero_of_dvd` — derives `n % 25 = 0` from `25 ∣ n`.
- `omega` — closes the numerical contradiction between `hmod : n % 25 = 5` and `hzero : n % 25 = 0`.
- `intro` — introduces the contrary assumption for the negated goal `¬ 25 ∣ n`.

Article 0070 is not called directly in this proof, but the two lemmas form a pair of inputs to the next valuation theorem.

## Proof flow

1. For the target `¬ 25 ∣ n`, introduce the contrary assumption `h25 : 25 ∣ n`.
2. Apply `Nat.mod_eq_zero_of_dvd h25` to obtain

   $$
   n\bmod 25=0.
   $$
3. This is incompatible with the original hypothesis

   $$
   n\bmod 25=5,
   $$

   so `omega` closes the contradiction.

## Lean-specific processing

Mathematically, this is the one-line observation that a multiple of 25 has remainder 0 modulo 25. In Lean, `Nat.mod_eq_zero_of_dvd` performs this conversion explicitly.

`omega` is not reasoning about divisibility itself. After divisibility has been converted to a remainder equality, it only sees the inconsistent natural-number equations

```lean
hmod  : n % 25 = 5
hzero : n % 25 = 0
```

and closes the contradiction. This keeps the number-theoretic data flow relatively transparent.

## Redundancy and duplication

The proof has only four lines and contains essentially no logical duplication.

The final `omega`, however, is stronger than necessary for a contradiction between the constants 0 and 5. One could instead rewrite `hzero` using `hmod` and close the resulting contradiction with `norm_num`, making the final step more local.

The statement is also specialized to 25 and 5, while its core is the general bridge

```lean
n % m = r → r ≠ 0 → ¬ m ∣ n
```

for an arbitrary modulus `m` and nonzero residue `r`.

## Optimization candidates

The first candidate is to replace `omega` by a smaller normalization step. For example, after `rw [hmod] at hzero`, `norm_num at hzero` may make the exact contradiction more explicit.

The second candidate is generalization. A helper deriving `¬ m ∣ n` from `n % m = r` and `r ≠ 0` would reduce this 25/5-specific lemma to a thin specialization.

The third candidate is to reorganize the bridge sequence 0068–0071 as an API and provide a combined theorem taking `(n : ZMod 25) = 5` directly to

$$
5\mid n\land 25\nmid n.
$$

That would shorten downstream proof code, while the current staged form has the advantage that each representation change can be audited separately.

## Required Mathlib imports and import optimization

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. This lemma itself directly needs only the natural-number remainder/divisibility API and the `omega` tactic.

A plausible minimal import would therefore involve Nat modular arithmetic plus something equivalent to `Mathlib.Tactic.Omega`. However, the exact import line of the split source file `DkMath/FLT/Five/SignedFiveAdic.lean` was not directly confirmed on the target branch, so the exact minimal module names remain an explicitly unverified inference.

If `omega` were replaced by `norm_num` or a direct contradiction proof, the tactic import requirements could change as well. No Lean build was run in this article, so import minimization remains unverified.

## Comparator challenge suitability

This theorem is suitable for a Comparator challenge because its small size makes proof-style differences easy to inspect.

- Current: `Nat.mod_eq_zero_of_dvd` + `omega`
- Candidate A: `Nat.mod_eq_zero_of_dvd` + rewrite + `norm_num`
- Candidate B: general helper `mod_eq_nonzero → not_dvd`, then specialize
- Candidate C: derive `25 ∤ n` directly from the `ZMod 25` equality produced in article 0068

Useful comparison axes are tactic strength, visibility of the remainder/divisibility conversion, generalizability, and clarity when paired with article 0070 as an API boundary.

## Evidence and inference

The theorem name, type, complete proof body, and the fact that `padicValNat_five_eq_one_of_dvd_not_sq` immediately follows it were confirmed in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The same source also confirms that both the later difference and sum branches call this lemma directly.

The generated standalone manifest lists `DkMath/FLT/Five/SignedFiveAdic.lean` as the source module. However, the split source file's exact import line was not directly confirmed on the target branch, so statements about minimal imports are explicitly treated as inference.

The exact corresponding page in the existing Japanese and English PDFs was not confirmed in this run. No PDF-specific description or page number has therefore been guessed.

## Next theorem to read

```lean
theorem padicValNat_five_eq_one_of_dvd_not_sq
    {n : ℕ} (h5 : 5 ∣ n) (h25 : ¬ 25 ∣ n) :
    padicValNat 5 n = 1
```

Articles 0070 and 0071 provide the two conditions “divisible by 5 but not by 25”; the next theorem converts them into the exact 5-adic valuation `1`.
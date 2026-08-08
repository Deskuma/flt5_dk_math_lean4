# 0070 — `five_dvd_of_eq_five_add_twentyFive_mul`

## Lean type

```lean
private theorem five_dvd_of_eq_five_add_twentyFive_mul
    {n M : ℕ} (h : n = 5 + 25 * M) :
    5 ∣ n := by
  use 1 + 5 * M
  omega
```

This declaration is `private`. Inside `SignedFiveAdic.lean`, it converts the explicit residue decomposition `n = 5 + 25*M` into the ordinary divisibility statement `5 ∣ n`.

## Mathematical statement

If natural numbers `n,M` satisfy

$$
n=5+25M,
$$

then

$$
5\mid n.
$$

Indeed,

$$
n=5+25M=5(1+5M),
$$

so one may take

$$
1+5M
$$

as the divisibility witness.

## Role in the whole proof

Article 0068 converted an equality in `ZMod 25` back into `n % 25 = 5`, and 0069 expanded that into

$$
n=5+25M.
$$

The present lemma 0070 extracts from this explicit decomposition the fact that the residual contains at least one factor of 5.

The flow is

```text
(residual : ZMod 25) = 5
             ↓ 0068
      residual % 25 = 5
             ↓ 0069
      residual = 5 + 25*M
             ↓ 0070
          5 ∣ residual
```

However, `5 ∣ residual` alone is not enough to prove the exact valuation `v₅(residual)=1`. The immediately following lemma `not_twentyFive_dvd_of_mod_eq_five` supplies `25 ∤ residual`, and `padicValNat_five_eq_one_of_dvd_not_sq` combines the two conditions.

## Direct dependencies

- natural-number divisibility `Dvd.dvd`
- `use` for supplying the existential divisibility witness
- `omega` for closing the remaining linear natural-number arithmetic

Mathematically, the lemma does not require any specialized previous theorem. It only consumes the equation `h` produced by the previous bridge.

## Proof flow

1. Choose `1 + 5 * M` as the witness for `5 ∣ n`.
2. After unfolding the divisibility goal, the remaining equality is equivalent to

   $$
   n=5(1+5M).
   $$
3. Give the hypothesis `h : n = 5 + 25*M` and the elementary arithmetic identity to `omega`.
4. The goal closes.

## Lean-specific processing

In Lean, `5 ∣ n` asks for a natural number `c` such that `n = 5 * c`. The command `use 1 + 5 * M` supplies this witness directly.

Thus the constructive content is explicit: `omega` is not discovering the witness. It is only normalizing the elementary Presburger-arithmetic identity

$$
5+25M=5(1+5M).
$$

## Redundancy and duplication

The proof is only two lines long and has almost no logical duplication.

Still, `omega` is stronger than necessary for such a small identity. One could potentially replace it by rewriting with `h` and then using basic divisibility or ring-normalization lemmas.

The statement also looks specific to 5 and 25, while its core is the general fact that a divisor of each summand divides their sum. A more abstract proof could use existing `dvd_add` and multiplication divisibility APIs.

## Optimization candidates

The first candidate is to remove `omega` and prove the goal using divisibility lemmas only. After rewriting by `h`, one can combine `5 ∣ 5` and `5 ∣ 25*M` directly.

The second candidate is to fuse this lemma with 0069 and introduce a helper deriving `5 ∣ n` directly from `n % 25 = 5`. That is shorter in use, although the current 0069→0070 separation makes the transformation “remainder equation → explicit decomposition → divisibility” particularly easy to audit.

A third option is to generalize the pattern to a lemma such as `n % (p*p) = p → p ∣ n`. For this FLT5 layer, however, the explicit fixed-prime form also has readability value.

## Required Mathlib imports and import optimization candidates

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. This lemma itself only needs natural-number divisibility and the `omega` tactic.

A plausible minimal import set would therefore consist of the Nat divisibility API and something equivalent to `Mathlib.Tactic.Omega`. The exact imports of the split source file `DkMath/FLT/Five/SignedFiveAdic.lean` were not directly confirmed on the target branch, so concrete minimal module names remain an explicitly marked inference.

If the proof is rewritten tactic-free, this lemma may no longer require `Omega` at all. No Lean build was run in this session, so import minimization has not been verified.

## Comparator challenge suitability

Very suitable. The proposition is small enough that proof-style differences are easy to inspect.

- Current: explicit witness + `omega`
- Candidate A: rewrite by `h`, then close using divisibility API only
- Candidate B: construct `⟨1 + 5*M, ...⟩` directly and use only lightweight arithmetic normalization
- Candidate C: specialize a generalized lemma `n % (p*p) = p → p ∣ n`

Useful comparison criteria are tactic dependence, visibility of the arithmetic structure, generalizability, and clarity of connection to the surrounding bridge lemmas.

## Evidence and inference

The theorem name, type, complete proof body, and the fact that it is immediately followed by `not_twentyFive_dvd_of_mod_eq_five` and `padicValNat_five_eq_one_of_dvd_not_sq` were confirmed in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

GitHub code search returned a temporary 502 upstream error during this run, so dependency order was verified by directly reading the standalone source. The exact corresponding pages in the existing Japanese and English PDFs were not confirmed, and no PDF-specific page references or descriptions have been guessed.

## Next theorem to read

```lean
private theorem not_twentyFive_dvd_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ¬ 25 ∣ n
```

Article 0070 supplies `5 ∣ n`; this next lemma supplies `25 ∤ n`. Together they provide the two hypotheses needed to pin the five-adic valuation down to exactly 1.

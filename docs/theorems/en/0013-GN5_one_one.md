# 0013 — `GN5_one_one`

> This document is the English translation of the Japanese canonical edition.

## Lean type

```lean
theorem GN5_one_one : GN5 1 1 = 31 := by
  norm_num [GN5]
```

Its fully qualified name is `DkMath.FLT.Five.GN5_one_one`.

## Mathematical statement

Evaluating `GN5` at gap $g=1$ and base coordinate $y=1$ gives $31$.

$$
GN5(1,1)=1^4+5\cdot1^3\cdot1+10\cdot1^2\cdot1^2+10\cdot1\cdot1^3+5\cdot1^4=31
$$

The same value can be read from the standard cyclotomic-factor form as

$$
GN5(1,1)=2^4+2^3+2^2+2+1=31
$$

## Role in the complete proof

This theorem specializes the general fifth cyclotomic factor to a concrete finite-prime escape example. The later theorem `cleanGN5Channel_one_one_31` checks that $31$ is prime, divides `GN5 1 1`, and that $31^2$ does not divide it. This leads to a small demonstration that `GN5 1 1` is not a fifth power.

The lemma is not a principal reduction in the general FLT5 proof. It is a smoke test and auditable demonstration of the local no-lift mechanism by finite computation.

## Direct dependencies

- `DkMath.FLT.Five.GN5`
- the `norm_num` tactic

Mathematically, the result can also be derived through `GN5_eq_homogeneous_cyclotomic`, but the current proof does not depend on that theorem. It unfolds the definition directly.

## Proof flow

1. `norm_num [GN5]` unfolds the definition of `GN5`.
2. It substitutes $g=y=1$ into every monomial.
3. It normalizes natural-number powers, products, and sums.
4. It closes the equality because both sides evaluate to $31$.

The proof uses neither `ring`, `omega`, primality checking, nor divisibility reasoning.

## Lean-specific processing

The definition listed in `norm_num [GN5]` is unfolded before numerical normalization. Plain `rfl` need not normalize all remaining powers, products, and sums into the required form, so the tactic specialized for numerical propositions makes the intent explicit.

The theorem is closed: it has no variables or assumptions. The proof term checked by the kernel establishes only a concrete equality of natural numbers.

## Redundancy and duplication

The value $31$ is recomputed later inside `cleanGN5Channel_one_one_31` with `norm_num [GN5]`. There is therefore duplicated evaluation.

Keeping this theorem as a named API still records the semantic value and makes it available to articles, tests, and later proofs. The fact that the later theorem does not reuse it is an optimization candidate.

## Optimization candidates

The `dvd_GN5` and `noLift` fields in `cleanGN5Channel_one_one_31` could rewrite or simplify with `GN5_one_one`, avoiding repeated polynomial evaluation. The current closed uses of `norm_num [GN5]` are nevertheless local and robust.

Another proof could pass through `GN5_eq_homogeneous_cyclotomic 1 1`, but that adds a dependency on a general identity to solve a simple evaluation and does not necessarily improve brevity or maintainability.

## Required Mathlib imports and import optimization

The generated standalone file uses `import Mathlib`. This theorem directly needs natural numbers, powers and arithmetic, and the `norm_num` tactic. It may be possible to narrow the imports to `Mathlib.Tactic.NormNum` together with basic natural-number algebra modules, but the exact minimum is unverified because no Lean build was run.

## Comparator challenge suitability

It is suitable. The goal is small and exact, and different proof styles are easy to compare.

1. The current `norm_num [GN5]` proof.
2. `unfold GN5; norm_num`.
3. Rewrite with `GN5_eq_homogeneous_cyclotomic` and then use `norm_num`.
4. Test whether `decide` or `native_decide` is applicable.

Useful comparison axes are proof-term transparency, reuse of general lemmas, execution cost, import requirements, and resilience under definition changes. The applicability and trust-boundary implications of `native_decide` require an actual build and are therefore proposals rather than verified facts.

## Next theorem to read

The next theorem is `DkMath.FLT.Five.GN5_two_one`.

$$
GN5(2,1)=121
$$

It is a second small evaluation of the same kernel and strengthens the definition-and-normalization smoke test. After that, the reading path enters the `CleanGN5Channel` structure and the no-lift demonstration at the finite prime $31$.

## Sources and distinction between fact and inference

The type, proof, declaration order, value $31$, and following declarations were verified in the generated `DkMath/FLT/Five/GN5.lean` and `CleanChannel.lean` sections of `Flt5DkMath/FLT5StandAlone.lean`. The discussion of its proof-wide role, duplicated evaluation, import minimization, and Comparator variants includes explanatory analysis or unverified proposals. The Lean source is treated as the formal authority over narrative PDF material; this article makes no additional PDF-specific claim. No Lean build was run.
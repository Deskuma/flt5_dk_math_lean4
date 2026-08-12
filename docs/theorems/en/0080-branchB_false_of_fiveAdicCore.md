# 0080 — `branchB_false_of_fiveAdicCore`

## Lean type

```lean
theorem branchB_false_of_fiveAdicCore
    (hCore : SignedFiveAdicCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_fiveAdicCore hCore) hPack hBranch
```

## Mathematical statement

Given `CounterexamplePack x y z` and the Branch B condition $5\nmid(z-y)$, if `SignedFiveAdicCore` is available—meaning every exact five-adic packet yields a contradiction—then `False` follows.

Conceptually,

$$
\mathrm{SignedFiveAdicCore}
\Longrightarrow\mathrm{SignedBranchARefuter}
\Longrightarrow\mathrm{BranchB\ candidate}
\Longrightarrow\bot.
$$

This theorem adds no new congruence or valuation computation. It connects the existing five-adic core layer to Branch B closure.

## Role in the overall proof

Articles 0075–0079 construct a common `SignedFiveAdicPacket` from a signed normal form and lift a packet-level contradiction to `SignedBranchARefuter`. This theorem passes that refuter to 0058 `branchB_false_of_signedBranchARefuter`, thereby closing the original Branch B counterexample candidate.

It is therefore the closure theorem at the end of the `DkMath/FLT/Five/SignedFiveAdic.lean` layer, reconnecting the local five-adic invariant machinery to the FLT5 Branch-B contradiction.

## Direct dependencies

- `SignedFiveAdicCore`
- `signedBranchARefuter_of_fiveAdicCore`
- `branchB_false_of_signedBranchARefuter`
- `CounterexamplePack`

`GN5`, `SumGN5`, `padicValNat`, and `ZMod 25` are not referenced directly. They are hidden behind the packet/core API.

## Proof flow

1. Receive `hCore : SignedFiveAdicCore`.
2. Build `SignedBranchARefuter` via `signedBranchARefuter_of_fiveAdicCore hCore`.
3. Pass that refuter together with `hPack` and `hBranch` to `branchB_false_of_signedBranchARefuter`.
4. Obtain `False`.

The proof is simply the composition of two previously established adapters.

## Lean-specific processing

`{x y z : ℕ}` are implicit and inferred from `hPack`. The result type of the inner theorem is exactly `SignedBranchARefuter`, which is exactly the first argument type required by the outer theorem, so the proof closes with a single `exact`. No intermediate `have`, rewriting, casts, or arithmetic tactics are needed. This exposes that the existing API boundaries line up correctly at the type level.

## Redundancy and duplication

The proof script itself is essentially irreducible. Article 0079 could be inlined, but then the packet-to-normal-form adapter responsibility would leak into the Branch B theorem. Merging this theorem with 0058 would also remove the reusable boundary where a `SignedBranchARefuter` may be supplied by another implementation. The current wrapper is best understood as an architectural seam rather than code duplication.

## Optimization candidates

The first candidate is to leave the theorem unchanged: it is already one line and its name clearly records its role. A generic composition helper would only become attractive if many closure theorems of the same shape appear. If the classical selection in 0076–0077 were replaced by a constructive packet constructor, this theorem could keep the same surface form while reducing its indirect dependence on `Classical.choice`; that remains an unverified design proposal.

## Required Mathlib imports and import optimization candidates

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses `import Mathlib`. Its manifest comment places this theorem in the `DkMath/FLT/Five/SignedFiveAdic.lean` segment. The theorem itself directly uses no specialized Mathlib number-theory API; its meaningful dependencies are the local declarations listed above.

A smaller import set is therefore likely possible in the split module, but the exact import graph of the original split source was not revalidated on the museum branch in this run. The minimal import set is consequently left unconfirmed.

## Relation to the existing PDFs

The target-branch Lean source is the primary evidence for the exact type and proof term. A one-to-one page in the existing Japanese and English PDFs corresponding to this short architecture-level closure theorem was not identified in this run, so no PDF-specific page number or explanation has been inferred.

## Comparator challenge suitability

Suitable, primarily as a proof-architecture challenge rather than a number-theory search challenge. Useful variants include the current named two-stage adapter, inlining article 0079, generic refuter composition, and preserving this theorem after replacing packet selection with a constructive constructor. Evaluation criteria include brevity, dependency boundaries, reuse, error locality, and indirect dependence on classical choice.

## Next theorem to read

In the Lean source, this theorem ends the `SignedFiveAdic.lean` segment and the generated artifact then enters `SignedFiveAdicPowerSplit.lean`. The next declaration is

```lean
private theorem dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
    {u v q : ℕ} (hqsum : q ∣ u + v) (hqres : q ∣ SumGN5 u v) :
    q ∣ 5 * u ^ 4 := by
  ...
```

For the sum orientation, it shows that if `q` divides both `u+v` and `SumGN5 u v`, then `q` also divides `5*u^4`, using arithmetic in `ZMod q`. This feeds the subsequent theorem `signedFiveAdicPacket_gcd_eq_five`.
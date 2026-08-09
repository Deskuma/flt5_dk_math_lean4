# 0079 — `signedBranchARefuter_of_fiveAdicCore`

## Lean Type

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

## Mathematical Statement

`SignedFiveAdicCore` is a receiver that sends every exact five-adic packet to a contradiction.

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPacket}(u,v,w)\to\bot.
$$

On the other hand, `SignedBranchARefuter` is a receiver that sends every signed Branch-A normal form to a contradiction. This theorem chooses a packet from a normal form using 0077 `signedFiveAdicPacket_of_normalForm`, then passes that packet to `hCore`, thereby constructing a normal-form-level refuter from a packet-level refuter.

Conceptually, it is the two-stage composition

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\bot.
$$

## Role in the Overall Proof

This theorem is the adapter between the five-adic packet layer and the signed Branch-A layer. Articles 0076–0077 provide a packet from a normal form, and 0078 defines the type `SignedFiveAdicCore` for sending a packet to contradiction. This article connects those two interfaces and obtains `SignedBranchARefuter`.

The immediately following theorem `branchB_false_of_fiveAdicCore` passes this refuter to the existing `branchB_false_of_signedBranchARefuter`, thereby closing Branch B. Thus this theorem is the connection point that promotes a local five-adic contradiction core into a refuter usable by the Branch-B closure layer.

## Direct Dependencies

The direct dependencies are:

- `SignedFiveAdicCore`
- `SignedBranchARefuter`
- `signedFiveAdicPacket_of_normalForm`

`SignedFiveAdicPacket`, `padicValNat`, `GN5`, `SumGN5`, and the mod-25 lemmas are not referenced directly here. They are hidden behind the packet returned by 0077 and the core contract defined in 0078.

## Proof Flow

1. Assume `hCore : SignedFiveAdicCore`.
2. Unfold the target `SignedBranchARefuter` as needed via `intro u v w hNF`, receiving an arbitrary signed normal form `hNF`.
3. Obtain `SignedFiveAdicPacket u v w` from `signedFiveAdicPacket_of_normalForm hNF`.
4. Pass that packet to `hCore` and obtain `False`.

The proof is essentially one function composition.

## Lean-Specific Processing

### `intro` through an `abbrev`

`SignedBranchARefuter` is a proposition alias, so Lean can unfold it as necessary and accept `intro u v w hNF`. The adapter theorem does not need to restate the underlying function type.

### Inference of implicit arguments

The type of `hCore` is

```lean
∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

and `u v w` are implicit. Lean infers them from the result type of `signedFiveAdicPacket_of_normalForm hNF`, so the concise term

```lean
hCore (signedFiveAdicPacket_of_normalForm hNF)
```

is sufficient.

### Use of a `noncomputable def`

Article 0077 is a `noncomputable def` based on `Classical.choice`. This theorem itself does not need to be marked `noncomputable`, because it does not compute with the chosen packet; it only uses the packet's proof content as input to `hCore` to derive `False`.

## Redundancy and Duplication

The proof script itself is essentially irreducible. After the introductions, the core is applied in one line, which is close to the minimum possible adapter.

At the architectural level, if `branchB_false_of_fiveAdicCore` were the only consumer, this theorem could be inlined there. However, keeping `SignedBranchARefuter` as a named boundary decouples the five-adic core from the Branch-B routing layer. The current standalone theorem therefore has a clear role despite its brevity.

## Optimization Candidates

The first candidate is to combine the existence proof of 0076 and the classical selection of 0077 into a direct constructive constructor returning `SignedFiveAdicPacket`. The shape of this theorem would remain the same, but its indirect dependence on classical choice could potentially disappear. This is an unverified design proposal; no Lean build was run.

A second candidate would be a generic function-composition adapter, but this theorem is already transparent in one line, so such an abstraction would likely be excessive.

Third, there appears to be little reason to mark this theorem `[simp]` or otherwise prioritize it for rewriting automation. It is an architectural bridge rather than a rewrite lemma.

## Required Mathlib Imports and Import Optimization

The target `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. This theorem directly uses only the local declarations `SignedFiveAdicCore`, `SignedBranchARefuter`, and `signedFiveAdicPacket_of_normalForm`, together with basic tactic syntax. It does not directly invoke any specialized Mathlib number-theory API.

According to the generated-source manifest, this region belongs to `DkMath/FLT/Five/SignedFiveAdic.lean`. Therefore, in the split source it is plausible that importing the local modules providing those three declarations plus the basic tactic environment is sufficient.

However, the exact import graph of the split module was not re-verified in this run. The precise minimal Mathlib import therefore remains unconfirmed.

## Relation to the Existing PDFs

The final authority for this article is the Lean source on the target branch. A concrete page in the existing Japanese or English PDFs corresponding one-to-one with this short adapter theorem was not identified in this run, so no PDF-specific explanation or page number has been inferred.

## Comparator Challenge Suitability

**Suitable.** The interesting comparison is not difficult theorem proving but proof architecture.

Possible variants are:

- the current named adapter theorem,
- inlining it into `branchB_false_of_fiveAdicCore`,
- expressing it through a generic function-composition helper,
- keeping the same adapter after replacing 0076–0077 by a constructive packet constructor.

Useful evaluation criteria are clarity of dependency boundaries, error messages, reusability, reliance on classical choice, and code size.

## Next Theorem to Read

Next is

```lean
theorem branchB_false_of_fiveAdicCore
    (hCore : SignedFiveAdicCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_fiveAdicCore hCore) hPack hBranch
```

This article constructs a signed Branch-A refuter from the five-adic core. The next theorem passes that refuter to the existing Branch-B routing theorem, so the common five-adic core reaches a contradiction for the entire Branch B.
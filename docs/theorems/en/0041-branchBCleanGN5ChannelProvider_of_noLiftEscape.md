# 0041 — `branchBCleanGN5ChannelProvider_of_noLiftEscape`

## Declaration

```lean
theorem branchBCleanGN5ChannelProvider_of_noLiftEscape
    (hEscape : BranchBNoLiftEscape) :
    BranchBCleanGN5ChannelProvider := by
  intro x y z hPack hBranch
  rcases hEscape hPack hBranch with ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
  exact ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

The fully qualified name is:

```text
DkMath.FLT.Five.branchBCleanGN5ChannelProvider_of_noLiftEscape
```

## 1. Lean type

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

After expansion, the input `hEscape` returns, for every Branch B counterexample candidate, a natural number `q` together with the following four facts:

```lean
Nat.Prime q
q ∣ GN5 (z - y) y
¬ q ∣ z - y
¬ q ^ 2 ∣ GN5 (z - y) y
```

The output is a provider returning the same data bundled as `CleanGN5Channel (z-y) y q`.

## 2. Mathematical statement

Under the Branch B condition

$$
5\nmid z-y,
$$

if a no-lift escape supplies a prime $q$ satisfying

$$
q\mid GN5(z-y,y),\qquad q\nmid z-y,
$$

$$
q^2\nmid GN5(z-y,y),
$$

then those four facts are exactly sufficient to construct a clean channel.

This theorem adds no new arithmetic content. It converts local arithmetic data returned as a conjunction into a proposition structure with named fields.

## 3. Role in the whole proof

The previous declaration `BranchBNoLiftEscape` returned primality and three divisibility conditions through an unbundled conjunction. Local refuters such as `counterexample_false_of_clean_GN5Channel_by_dvd`, however, consume a `CleanGN5Channel`.

This theorem is the adapter between those interfaces.

```text
BranchBNoLiftEscape
        ↓ this theorem
BranchBCleanGN5ChannelProvider
        ↓ provider-based refuter
Branch B contradiction
```

Thus the proof that supplies a no-lift prime may return a simple conjunction without knowing the structure interface. The contradiction side can use named `CleanGN5Channel` fields without depending on the conjunction's association order.

## 4. Direct dependencies

### `BranchBNoLiftEscape`

For every `CounterexamplePack x y z` and Branch B hypothesis, it returns a prime `q` and four local facts.

### `BranchBCleanGN5ChannelProvider`

For every Branch B counterexample candidate, it returns some `q` and a `CleanGN5Channel (z-y) y q`.

### `CleanGN5Channel`

This proposition structure has four fields:

```lean
prime : Nat.Prime q
dvd_GN5 : q ∣ GN5 g y
not_dvd_gap : ¬ q ∣ g
noLift : ¬ q ^ 2 ∣ GN5 g y
```

The proof invokes no arithmetic lemma directly. Its dependencies are interface unfolding and structure construction only.

## 5. Proof flow

1. `intro x y z hPack hBranch` introduces the provider's implicit variables and two assumptions.
2. Applying `hEscape hPack hBranch` produces an existential witness `q` and four proofs.
3. `rcases` eliminates the existential and the right-associated conjunction in one step.
4. `⟨q, ...⟩` repackages the same five components as the existential clean-channel provider required by the target.

No data is reordered or discarded; it is moved unchanged into another container.

## 6. Lean-specific processing

### Transparent unfolding of `abbrev`

Both `BranchBNoLiftEscape` and `BranchBCleanGN5ChannelProvider` are `abbrev ... : Prop`. Lean unfolds them transparently during type checking, so no explicit `unfold` is required.

### Introducing implicit universal variables

The provider body begins with `∀ {x y z : ℕ}, ...`. Although these variables are declared implicit, a proof constructing the function may introduce them with `intro x y z`.

### Simultaneous existential and conjunction elimination with `rcases`

```lean
rcases hEscape hPack hBranch with
  ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

This destructures both `Exists` and the right-associated `And` chain.

### Positional structure construction

```lean
⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

The first element is the existential witness; the remaining elements fill the `CleanGN5Channel` fields in declaration order. This is concise but sensitive to field reordering.

## 7. Redundancy and duplication

The proof is intentionally nothing but repackaging, so there is no duplicated arithmetic argument. At the logical level, however, the input and output represent essentially the same four conditions.

That duplication is useful at an API boundary:

- provider proofs may prefer an unbundled conjunction;
- consumers benefit from named structure fields;
- placing the conversion in one theorem localizes dependence on field order.

## 8. Optimization candidates

### Construct with named fields

For stronger maintenance robustness, one could write:

```lean
  refine ⟨q, ?_⟩
  exact {
    prime := hqPrime
    dvd_GN5 := hqGN
    not_dvd_gap := hqGap
    noLift := hqNoLift
  }
```

The current proof is shorter and reasonable because the structure is small.

### Abstract a general constructor lemma

If the same bundled/unbundled conversion appears repeatedly, a constructor lemma such as `CleanGN5Channel.of_components` could be introduced. For a single use, that would be over-abstraction.

### Prove the reverse direction

For auditing or interchangeability of providers, the reverse implication

```lean
BranchBCleanGN5ChannelProvider → BranchBNoLiftEscape
```

is immediate. One could state logical equivalence between the interfaces, but it is unnecessary unless the reverse direction is used later.

## 9. Required Mathlib imports and optimization candidates

The standalone generated source is checked under `import Mathlib`. This theorem itself uses only Lean's basic logical machinery, natural numbers, existentials, conjunctions, and structure construction.

The exact import line of the individual `Provider.lean` module is not retained in the generated standalone artifact. By dependency structure, a project-local import must expose `BranchBNoLiftEscape`, `BranchBCleanGN5ChannelProvider`, `CleanGN5Channel`, `CounterexamplePack`, and `GN5`.

On the Mathlib side, the required surface is minimal, so `import Mathlib` is clearly broader than necessary for this theorem alone. The precise minimal project import remains an audit candidate requiring a Lean build. No build was run for this article.

## 10. Comparator challenge suitability

This theorem is suitable as a proof-engineering comparator rather than a mathematical-difficulty challenge.

### Challenge

Prove the adapter without explicitly unfolding either proposition interface:

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

### Comparison criteria

- one-shot `rcases` versus staged `obtain`;
- positional versus named-field construction;
- use of `simpa [BranchBNoLiftEscape, BranchBCleanGN5ChannelProvider]`;
- robustness under changes to structure field order.

The current proof is excellent for brevity; named-field construction is stronger for maintenance.

## 11. Scope of verification and explicit conjecture

The declaration name, type, proof body, and surrounding provider-layer declarations were verified in the standalone Lean source.

The minimal-import discussion contains design inference because the individual `Provider.lean` import line is not preserved in the generated artifact. It has not been checked by a Lean build. Existing PDFs provide architectural narrative, while the Lean source remains the authority for the theorem type and proof.

## 12. Next theorem to read

The natural next consumer is:

```text
DkMath.FLT.Five.branchB_false_of_clean_provider_by_dvd
```

It obtains a concrete clean channel from a `BranchBCleanGN5ChannelProvider` and applies the already established local refuter to close Branch B. This article converts interfaces; the next one shows that the converted provider actually carries the contradiction.

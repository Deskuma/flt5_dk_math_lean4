# 0043 — `branchB_false_of_noLiftEscape_by_dvd`

## 1. Target declaration

```lean
theorem branchB_false_of_noLiftEscape_by_dvd
    (hEscape : BranchBNoLiftEscape)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_clean_provider_by_dvd
    (branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape) hPack hBranch
```

The declaration is in the `DkMath.FLT.Five` namespace in `DkMath/FLT/Five/Provider.lean`.

## 2. Lean type

The theorem has the following dependent function type.

```lean
BranchBNoLiftEscape →
  {x y z : ℕ} →
  CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  False
```

The first argument `hEscape` is an unbundled kernel that supplies a no-lift prime for every Branch B counterexample candidate. Given implicit variables `x y z`, a counterexample pack `hPack`, and the Branch B condition `hBranch`, the theorem returns a contradiction.

## 3. Mathematical statement

`CounterexamplePack x y z` represents a primitive positive-natural-number candidate satisfying

$$
x^5+y^5=z^5.
$$

Branch B is the case in which the natural-number gap $z-y$ is not divisible by $5$:

$$
5\nmid(z-y).
$$

`BranchBNoLiftEscape` supplies a prime $q$ such that

$$
q\mid GN5(z-y,y),\qquad q\nmid(z-y),
$$

and

$$
q^2\nmid GN5(z-y,y).
$$

Consequently, $q$ occurs with local exponent exactly one in the complete fifth-power body

$$
(z-y)\,GN5(z-y,y)=x^5,
$$

which is incompatible with the exponent multiplicity required of a fifth power. This theorem derives that contradiction by composing the existing adapter and consumer.

## 4. Role in the whole proof

This theorem is the terminal declaration of `Provider.lean`. It is the public API that closes all of Branch B from the local no-lift assumption.

The responsibilities are separated as follows.

1. `BranchBNoLiftEscape` supplies primality and divisibility facts in conjunction form.
2. `branchBCleanGN5ChannelProvider_of_noLiftEscape` repackages them as a `CleanGN5Channel` structure.
3. `branchB_false_of_clean_provider_by_dvd` extracts a clean channel and contradicts the perfect-fifth-power body with the local no-lift obstruction.
4. The present theorem composes steps 2 and 3 while hiding the intermediate provider from callers.

It adds no new number-theoretic fact. It is an orchestration theorem connecting the already separated provider and consumer layers.

## 5. Direct dependencies

### 5.1 `BranchBNoLiftEscape`

For each Branch B counterexample candidate, this interface returns primality and three divisibility conditions required by a clean channel as an unbundled existential proposition.

### 5.2 `branchBCleanGN5ChannelProvider_of_noLiftEscape`

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

This adapter bundles the conjunctive local data into `CleanGN5Channel`.

### 5.3 `branchB_false_of_clean_provider_by_dvd`

```lean
BranchBCleanGN5ChannelProvider →
  CounterexamplePack x y z →
  (¬ 5 ∣ z - y) → False
```

This consumer extracts a concrete clean channel from the provider and passes it to the local refuter.

### 5.4 `CounterexamplePack`

This structure packages positivity, `Nat.Coprime x y`, and the Fermat equation for a primitive counterexample candidate.

## 6. Proof flow

The proof is completed by a single `exact` expression.

```lean
exact branchB_false_of_clean_provider_by_dvd
  (branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape) hPack hBranch
```

Reading from the inside out gives three steps.

1. Pass `hEscape` to the adapter to obtain a `BranchBCleanGN5ChannelProvider`.
2. Pass that provider as the first argument of the consumer.
3. Pass the same `hPack` and `hBranch` to the consumer and obtain `False`.

No intermediate value is named with `have`; the function composition is written directly as a proof term.

## 7. Lean-specific processing

### 7.1 Composing propositions as functions

In Lean, proofs are ordinary terms. Therefore the proof returned by the adapter can be passed directly as an argument to the consumer. This theorem is a particularly clear instance of the Curry–Howard correspondence.

### 7.2 Transparency of `abbrev`

`BranchBNoLiftEscape` and `BranchBCleanGN5ChannelProvider` are proposition abbreviations. Lean unfolds them transparently when required, so no explicit `unfold` is needed.

### 7.3 Implicit-argument inference

The variables `x y z` are implicit. Lean infers all three from the types of `hPack` and `hBranch`.

### 7.4 Line breaks do not change application structure

The two-line `exact` expression is a single term that applies the consumer successively to the adapter result, `hPack`, and `hBranch`.

## 8. Redundancy and duplication

Logically, this theorem is exactly the composition of articles 0041 and 0042 and contains no new intermediate fact. In that sense, the duplication is intentional.

At the API level it is useful. Callers can derive the Branch B contradiction directly from the mathematically natural assumption `BranchBNoLiftEscape` without knowing about the bundled provider or the repackaging into `CleanGN5Channel`. It should therefore be viewed as a façade theorem rather than a deletion candidate.

## 9. Optimization candidates

The current proof is already near-minimal. A more pedagogical alternative is:

```lean
  have hProvider : BranchBCleanGN5ChannelProvider :=
    branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape
  exact branchB_false_of_clean_provider_by_dvd hProvider hPack hBranch
```

This version exposes the intermediate API but adds lines. The current single-expression proof better represents the declaration as a composition theorem.

A shorter name such as `branchB_false_of_noLiftEscape` could be considered, but the `_by_dvd` suffix may distinguish this route from a valuation-based route. Renaming should be decided only after inspecting later declarations; here it remains an unverified design proposal.

## 10. Required Mathlib imports and import optimization

The theorem itself only applies existing declarations. It invokes no Mathlib theorem or tactic directly. In isolation, it only requires project modules providing:

- `BranchBNoLiftEscape`
- `branchBCleanGN5ChannelProvider_of_noLiftEscape`
- `branchB_false_of_clean_provider_by_dvd`
- `CounterexamplePack`

The exact minimal import set depends on the import graph of `Provider.lean`. The standalone file uses `import Mathlib` as an aggregate import, but that is not a theorem-specific requirement. An optimization audit should start from the direct DkMath imports of `Provider.lean` and use minimal-import experiments together with `#print axioms`. No Lean build was run in this edition, so the exact minimal set is an unverified candidate.

## 11. Comparator challenge suitability

This declaration is well suited to a short interface-composition challenge rather than a number-theoretic search challenge.

### Challenge

Using only

```lean
branchBCleanGN5ChannelProvider_of_noLiftEscape
branchB_false_of_clean_provider_by_dvd
```

prove the declaration of this article.

Possible comparison axes are:

- a two-step proof with an intermediate `have`
- the current one-expression `exact` proof
- a tactic proof combining `apply` and `exact`

The evaluation should reward not only character count but also clarity of dependency direction and API boundaries.

## 12. Evidence and explicit conjectural notes

The declaration name, type, proof body, and its position as the terminal declaration of `Provider.lean` were verified in the generated standalone Lean source in the repository.

The mathematical explanation is based on the definitions and proofs of `BranchBNoLiftEscape`, the adapter, the consumer, `CleanGN5Channel`, and `Body5` in the same source.

The exact minimal import set and the shorter-name proposal are optimization candidates rather than verified facts because no Lean build or import-minimization experiment was performed.

## 13. Next declaration to read

The next declaration is `DkMath.FLT.Five.BranchACondition`.

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

The Branch B provider layer is complete with this article. The next article begins the exceptional side of the proof: the public interface for Branch A, where the gap is divisible by $5$.
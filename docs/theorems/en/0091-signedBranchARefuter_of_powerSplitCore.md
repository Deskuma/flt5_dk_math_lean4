# 0091 — `signedBranchARefuter_of_powerSplitCore`

## Lean type

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

This theorem is an adapter theorem that lifts the “refuter sending every exact power split to contradiction” represented by 0090 `SignedFiveAdicPowerSplitCore` to a refuter for the whole signed Branch-A normal-form layer required by 0057 `SignedBranchARefuter`.

## Mathematical statement

The core contract from 0090 is

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\Longrightarrow\bot.
$$

Meanwhile, `SignedBranchARefuter` conceptually has the form

$$
\forall u,v,w,\quad
\mathrm{SignedBranchANormalForm}(u,v,w)\Longrightarrow\bot.
$$

By 0089 `signedFiveAdicPowerSplit_of_normalForm`, we already have

$$
\mathrm{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}(u,v,w).
$$

Composing these maps yields

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\longrightarrow
\mathrm{SignedBranchARefuter}.
$$

The mathematics performed by this theorem is exactly this function composition.

## Role in the whole proof

This is a closure adapter that transports a contradiction core proved at the five-adic power-split layer back to the upstream signed Branch-A routing layer.

Layer by layer, the proof flow is

$$
\mathrm{SignedBranchANormalForm}
\xrightarrow{\;0089\;}
\mathrm{SignedFiveAdicPowerSplit}
\xrightarrow{\;hCore\;}
\bot.
$$

The important architectural effect is that the subsequent Branch-B closure no longer needs to know the internal structure of a power split. How `hCore` contradicts a `SignedFiveAdicPowerSplit` is fully abstracted away; this theorem only converts a normal form into a split and applies the refuter.

The immediately following `branchB_false_of_powerSplitCore` passes this theorem to `branchB_false_of_signedBranchARefuter`, thereby closing routed Branch-B candidates. Thus this theorem is the intermediate bridge between an exact power-split contradiction and Branch-B closure.

## Direct dependencies

The direct dependencies are these three declarations.

1. `SignedFiveAdicPowerSplitCore` (0090)
2. `SignedBranchARefuter` (0057)
3. `signedFiveAdicPowerSplit_of_normalForm` (0089)

This theorem itself does not directly inspect fields of `SignedFiveAdicPowerSplit`, gcd facts, mod-$25$ facts, `padicValNat`, or fifth-power splitting. Those details have already been encapsulated in the construction layer through 0089 and on the implementation side of `hCore`.

## Proof flow

The proof finishes in two steps.

1. `intro u v w hNF` receives the three natural-number indices and the normal-form witness required by `SignedBranchARefuter`.
2. `signedFiveAdicPowerSplit_of_normalForm hNF` chooses the exact power split, which is then supplied to `hCore` to obtain `False`.

The essential code is one line:

```lean
exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

As a proof term, it is simply the composition of the normal-form-to-split map with the split refuter.

## Lean-specific processing

### 1. Letting Lean unfold the `SignedBranchARefuter` interface

`SignedBranchARefuter` is the project-local API type for the refuter, and `intro u v w hNF` follows its argument structure. Proving the theorem against the named API preserves the meaning of the upstream layer in the declaration type.

### 2. Inference of implicit indices

The type of `hNF` determines `u v w`, so neither

```lean
signedFiveAdicPowerSplit_of_normalForm hNF
```

nor

```lean
hCore (...)
```

needs the three indices to be written explicitly. The elaborator connects the indexed families.

### 3. Using a `noncomputable` value inside a theorem

0089 `signedFiveAdicPowerSplit_of_normalForm` is a `noncomputable def` because it ultimately uses `Classical.choice` from 0088. This declaration, however, is a theorem and only uses that selected value in a proof-only derivation of `False`; therefore this theorem itself does not need a `noncomputable` modifier.

### 4. Only `intro` and `exact`

No normalization, arithmetic tactic, or rewrite is used. Because the dependency APIs have already been shaped appropriately, Lean's type checker nearly expresses the proof composition directly.

## Redundancy and duplication

There is essentially no local code redundancy. Architecturally, however, there is a choice between retaining a named adapter theorem and composing the functions directly at the call site.

In principle, the following theorem could likely inline something of the form

```lean
branchB_false_of_signedBranchARefuter
  (fun u v w hNF => hCore (signedFiveAdicPowerSplit_of_normalForm hNF))
  ...
```

without passing through this declaration.

Keeping `signedBranchARefuter_of_powerSplitCore` as an independent theorem preserves the proof-graph edge

$$
\text{power-split core} \Rightarrow \text{signed Branch-A refuter}
$$

as a named object. From the viewpoint of the theorem museum, this one-line declaration explicitly records which abstraction layer is being exited and which one is being re-entered, so it is not merely redundant code.

## Optimization candidates

### Candidate A — Keep the current named adapter

This is the most readable option. Subsequent theorems can entirely forget the details of power-split construction and reuse the existing API expecting a `SignedBranchARefuter`.

### Candidate B — Point-free / term-style form

Since the theorem is close to pure function composition, an even shorter term-style proof may be possible depending on how the aliases unfold. Because implicit indexed arguments are involved, however, the current `intro` / `exact` form gives clearer type-error locations.

### Candidate C — Generic lifting combinator

Abstractly this is the contravariant refuter-lifting pattern

$$
A\to B,\qquad (B\to\bot)
\Longrightarrow
(A\to\bot).
$$

A generic helper is possible, but this theorem connects meaningful indexed project-local types. Over-abstraction could make the FLT5 proof graph harder to read.

### Candidate D — Replace the split provider constructively

If the `Classical.choice` path in 0088–0089 were replaced by a constructive direct constructor, the logical shape of this theorem would remain unchanged. The practical benefit here would therefore be small; that is primarily a design issue for 0087–0089 rather than an optimization specific to this theorem.

## Required Mathlib imports and import optimization

The generated standalone artifact on the target branch uses `import Mathlib`.

This theorem itself directly uses only `intro` and `exact`; it does not directly require arithmetic Mathlib theorems, `ring`, `omega`, `norm_num`, or `ZMod`. What it needs is availability of the project-local declarations

- `SignedBranchARefuter`
- `SignedFiveAdicPowerSplitCore`
- `signedFiveAdicPowerSplit_of_normalForm`.

The standalone manifest places this theorem at the end of `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`. Earlier parts of that module use gcd, coprimality, natural-number division, primality, powers, `ring`, `omega`, `norm_num`, and related APIs, so the true minimal import set must be determined for the module as a whole.

A safe import-optimization path would preserve the directly imported project modules first, then inventory umbrella `Mathlib` usage theorem-by-theorem and tactic-by-tactic. This task does not run a Lean build, so no concrete minimal import set is asserted without verification.

## Comparator challenge suitability

Suitable, although it is an API / proof-composition challenge rather than a difficult number-theory challenge.

Useful comparison variants include:

1. The current `intro` + `exact` proof.
2. An explicit `fun` term proof.
3. A generic refuter-lifting combinator.
4. Removing this theorem and inlining the composition inside `branchB_false_of_powerSplitCore`.
5. Preserving the same interface after replacing the split provider by a constructive one.

The evaluation criteria should include not only line count but proof-graph visibility, locality of type errors, preservation of domain terminology, reusability, and clarity of dependency direction.

The current implementation is near-minimal while retaining the important layer transition `SignedFiveAdicPowerSplitCore → SignedBranchARefuter` as a declaration name. Thus the central Comparator question is the design value of keeping a one-line adapter.

## PDF and source basis

The formal final authority is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. In the source, this theorem appears at the end of the `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` section, immediately after 0090 `SignedFiveAdicPowerSplitCore` and immediately before `branchB_false_of_powerSplitCore`.

The existing Japanese and English PDFs are treated as narrative background sources. During this run, GitHub code search returned an upstream 502 error, so a specific PDF page or section corresponding one-to-one with this one-line adapter could not be established. No PDF theorem number, page number, or wording is therefore supplied by inference.

## Next theorem to read

The theorem immediately following in the source is

```lean
theorem branchB_false_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

Now that this article has lifted the power-split core to `SignedBranchARefuter`, the next article passes that refuter to the existing `branchB_false_of_signedBranchARefuter` and completes the closure

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\text{every routed Branch-B pack is contradictory}.
$$

This is the final theorem of `SignedFiveAdicPowerSplit.lean`; `SquareGoldenBridge.lean` begins immediately afterward.
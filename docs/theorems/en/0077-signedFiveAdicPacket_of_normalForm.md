# 0077 — `signedFiveAdicPacket_of_normalForm`

## Lean type

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

This declaration is not a theorem but a `noncomputable def`. From the statement proved in 0076,

```lean
Nonempty (SignedFiveAdicPacket u v w)
```

it uses `Classical.choice` to select one `SignedFiveAdicPacket u v w` that downstream code can refer to directly.

## Mathematical statement

This declaration adds no new arithmetic theorem. It selects one packet from the existence statement already established in 0076 that at least one five-adic packet exists.

By the specification of 0075, the selected packet stores, for some `carrier`, `residual`, and `distinguished`, information such as

$$
carrier\cdot residual=distinguished^5,
$$

$$
residual\equiv5\pmod{25},
$$

$$
v_5(residual)=1,
$$

$$
v_5(carrier)=4+5m.
$$

The declaration itself does not computationally specify which inhabitant is selected.

## Role in the overall proof

Up through 0076, existence of the packet was wrapped inside `Nonempty`. For downstream refuters and power-split constructions, it is more convenient to pass an actual `SignedFiveAdicPacket` than to unpack an existence statement repeatedly.

This declaration is the canonical-choice adapter that bridges that boundary. Immediately afterward,

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

and

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

use this chosen packet to connect the normal form directly to the contradiction core.

## Direct dependencies

The direct dependencies are very small in number.

- `SignedBranchANormalForm`
- `SignedFiveAdicPacket`
- `nonempty_signedFiveAdicPacket_of_normalForm`
- `Classical.choice`

This declaration does not directly invoke the mod-25 calculations or `padicValNat` lemmas. Those have already been encapsulated inside the existence proof of 0076.

## Proof flow

The flow has only one substantive step.

1. Pass `hNF : SignedBranchANormalForm u v w` to 0076.
2. Obtain `Nonempty (SignedFiveAdicPacket u v w)` from `nonempty_signedFiveAdicPacket_of_normalForm hNF`.
3. Use `Classical.choice` to extract one inhabitant.

Thus the proof term is exactly

```lean
Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

itself.

## Lean-specific processing

The key Lean-specific features are `noncomputable` and `Classical.choice`.

Existence of an inhabitant of `SignedFiveAdicPacket u v w` has been proved, but no executable procedure for exposing a specific witness is provided. Lean can extract a value from the existence proof using classical choice, but such a definition does not in general carry executable computational content, hence `noncomputable def`.

Also, `Nonempty α` is not the same kind of data-bearing interface as an ordinary term of `α`. This declaration is a standard bridge from `Nonempty` to an actual term.

## Redundancy and duplication

There is essentially no duplication inside this declaration. It is deliberately a thin wrapper that hides the long constructor proof of 0076 from downstream code.

One subtle point is the word “canonical” in the source comment. It does not assert mathematical uniqueness. No theorem proves that the inhabitant selected by `Classical.choice` is unique. It is safest to read “canonical” here as a fixed representative at the API level.

## Optimization candidates

There are two natural candidates.

First, if the proof of 0076 were rewritten to return a value directly,

```lean
SignedBranchANormalForm u v w → SignedFiveAdicPacket u v w
```

then this declaration and its use of `Classical.choice` might become unnecessary. Since 0076 already constructs concrete record literals in both orientations, such a design appears plausible.

Second, retaining the current “existence theorem + chosen definition” split has a genuine abstraction benefit: it separates specification/existence from selection. Optimization should therefore be judged not only by line count but also by whether constructive API design or proof abstraction is the priority.

Both are design proposals only; no Lean build was run here.

## Required Mathlib imports and import optimization candidates

The standalone artifact on the target branch uses `import Mathlib`. The only external feature visible directly in this declaration is `Classical.choice`; the five-adic arithmetic itself is not used directly here.

Therefore the declaration in isolation likely needs a much smaller import surface. However, the dependencies of `SignedBranchANormalForm` and `SignedFiveAdicPacket` must also be available, so the exact minimum import cannot be asserted without inspecting the original module import graph.

A sensible optimization experiment is to inspect the actual imports of `SignedFiveAdic.lean` and test whether this wrapper can be isolated with only the local definitions plus the relevant classical-choice support.

## Relation to the existing PDFs

The final authority used here is the Lean source in the repository. A concrete page in the existing Japanese or English PDFs corresponding one-to-one with this `noncomputable def` was not identified in this pass, so no PDF-specific statement or page number has been guessed.

## Comparator challenge suitability

**Suitable.** It is most useful as an API-design comparison rather than a mathematical-proof challenge.

A good comparison is between:

- the current `Nonempty` theorem + `Classical.choice` definition, and
- a constructive constructor returning the packet directly.

Useful evaluation axes are classical dependency, downstream proof brevity, transparency under unfolding, extractability, and reusability of the constructor proof.

## Next declaration to read

Next is

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

0077 makes an actual packet available from a normal form. The next article defines, in one line, the receiver contract saying that every exact five-adic packet yields a contradiction. This is where packet construction and contradiction logic become cleanly separated.
# 0078 — `SignedFiveAdicCore`

## Lean type

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

This declaration is not a theorem but a proposition alias introduced with `abbrev`. It defines, in one line, the type of a contradiction receiver: for arbitrary `u v w : ℕ`, if one is given a corresponding `SignedFiveAdicPacket u v w`, one must be able to return `False`.

## Mathematical statement

Mathematically, this is the specification of a refuter asserting that the exact five-adic packets defined in 0075 cannot exist.

A `SignedFiveAdicPacket u v w` stores the carrier / residual / distinguished factorization and the five-adic information constructed from a signed Branch-A normal form. Conceptually, therefore, `SignedFiveAdicCore` expresses

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPacket}(u,v,w)\Longrightarrow\bot.
$$

The declaration itself does not yet prove a contradiction. It only fixes the type of the function that later code must implement: a function sending every packet to a contradiction.

## Role in the overall proof

Articles 0076–0077 establish the construction-side API from a normal form to a packet. This article defines the consumption-side API for that packet.

The immediately following theorem

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

simply passes the chosen packet from 0077 to `hCore`, yielding a `SignedBranchARefuter`. This cleanly separates packet construction from the contradiction argument.

The next theorem, `branchB_false_of_fiveAdicCore`, then routes the resulting signed refuter through the existing `branchB_false_of_signedBranchARefuter`. Thus this declaration is the receiving interface for the five-adic contradiction and a common boundary on the route to closing Branch B.

## Direct dependencies

There is only one direct local dependency:

- `SignedFiveAdicPacket`

The body of `SignedFiveAdicCore` does not directly mention `SignedBranchANormalForm`, `padicValNat`, `GN5`, or `ZMod 25`. That arithmetic information is already encapsulated in the packet fields.

This is precisely where the record abstraction introduced in 0075 pays off.

## Proof flow

There is no proof script in this declaration. Since it is an `abbrev`, the entire flow is the shape of the function type itself:

1. Accept arbitrary implicit `u v w : ℕ`.
2. Accept a `SignedFiveAdicPacket u v w`.
3. Return `False`.

In other words, this declaration fixes in advance the function type that a later contradiction core must inhabit.

## Lean-specific processing

### Meaning of `abbrev`

`abbrev` introduces a reducible abbreviation. Lean may unfold

```lean
SignedFiveAdicCore
```

into

```lean
∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

when needed.

Compared with an ordinary `def`, this makes the alias behave transparently in type checking, so downstream theorems can use `hCore packet` directly with essentially no adapter machinery.

### Why it lives in `Prop`

The codomain is `False`, so this core is a proof object rather than computational data. It therefore naturally lives in `Prop`.

### Implicit parameters

The parameters `{u v w : ℕ}` are implicit, so Lean can normally infer them from the packet type. This is why the next theorem can write

```lean
hCore (signedFiveAdicPacket_of_normalForm hNF)
```

without spelling out `u v w`.

## Redundancy and duplication

There is essentially no internal redundancy. The declaration is a one-line type alias whose purpose is instead to reduce repetition in later APIs.

One could omit the named alias and write the raw function type directly in every theorem argument:

```lean
∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

That would reduce the number of declarations but would lose the architectural name “five-adic contradiction core.” The current one-line alias is therefore a reasonable piece of intentional redundancy in favor of a clearer proof boundary.

## Optimization candidates

The main optimization possibilities concern API design.

First, if several packet-like types later need the same treatment, one could generalize the receiver shape, for example:

```lean
abbrev Refuter (α : Sort _) : Prop := α → False
```

However, in this repository a domain-specific name may make the proof route easier to audit, so the generic form could be over-abstraction.

Second, if later proofs are found to consume only a small subset of `SignedFiveAdicPacket` fields, the core interface might be reduced from the full packet to a thinner contradiction kernel. That should only be decided after reading the downstream contradiction implementation; at this point it is a conjectural design optimization.

Third, one could compare `abbrev` and `def`, but the reducible alias is natural here and there is currently little reason to make it opaque.

All of these are design suggestions; no Lean build was run for them.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself uses no specialized Mathlib arithmetic API; beyond Lean's basic logic it only needs the local definition `SignedFiveAdicPacket`.

The manifest places this region in `DkMath/FLT/Five/SignedFiveAdic.lean`. Therefore, in the split source tree, importing the local module that exposes `SignedFiveAdicPacket` may be sufficient.

However, this run uses the generated standalone file as the final source of truth and did not re-verify the split module's exact import graph. The exact minimal Mathlib import is therefore unconfirmed.

## Relation to the existing PDFs

The final authority for this article is the Lean source on the target branch. I did not identify a specific page in the existing Japanese or English PDFs that corresponds one-to-one with this single-line `abbrev`, so no PDF-specific narrative or page number has been inferred.

## Comparator challenge suitability

**Suitable.** It is more useful as a proof-architecture / API-design comparison than as a theorem-proving challenge.

Candidate variants include:

- the current domain-specific `SignedFiveAdicCore`,
- writing the raw function type directly in each theorem,
- a generic `Refuter α := α → False`,
- receiving a minimal contradiction kernel instead of the full packet.

Useful evaluation criteria are dependency visibility, error-message clarity, downstream theorem brevity, reuse, and the risk of over-abstraction.

## Next theorem to read

The next declaration is

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

Article 0078 defines the type of the contradiction receiver. The next theorem combines it with the normal-form-to-packet adapter from 0077 to construct an actual `SignedBranchARefuter`. This is the point where the packet-level five-adic core is promoted to a refuter for the whole signed Branch-A interface.
# 0236 — `signedGoldenRamifierStrippedPacket_of_normalForm`

## Lean type

```lean
/-- Chosen ramifier-stripped packet directly from a signed normal form. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

This is a `noncomputable def`, not a theorem. It exposes a composition API that takes a signed Branch-A normal form `hNF`, passes through the five-adic power-split layer, and returns one ramifier-stripped packet.

## Mathematical statement and meaning of the declaration

This declaration proves no new algebraic identity or divisibility fact. It composes two transformations that are already available:

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

and

$$
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}.
$$

It therefore publishes a direct path from the normal-form layer to the stripped-packet layer.

From the downstream point of view, the resulting packet conceptually retains the normalized state

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta.
$$

Thus the declaration is a representation bridge from the signed normal form to the state in which the visible ramified factor $\tau$ has already been removed once.

## Role in the full proof

Declaration 0233 constructs the existence of a stripped packet from an exceptional packet, and 0234 uses `Classical.choice` to select an actual packet object. Declaration 0235 adds a direct bridge from the exact five-adic power split to that object.

0236 moves the entry point one level higher: a consumer that only has `SignedBranchANormalForm` can now obtain the stripped packet without explicitly constructing either the power split or the exceptional representation.

This matters immediately downstream. The theorem `signedBranchARefuter_of_goldenRamifierStrippedCore` applies the present definition directly to a normal form `hNF` and feeds the resulting packet to the stripped contradiction core.

The declaration is therefore best understood as an adapter or facade in the signed Branch-A pipeline rather than as a local algebra theorem.

## Direct dependencies

The two direct computational dependencies are:

- `signedFiveAdicPowerSplit_of_normalForm`
- 0235 `signedGoldenRamifierStrippedPacket_of_powerSplit`

The types involved are:

- `SignedBranchANormalForm`
- `SignedFiveAdicPowerSplit`
- `SignedGoldenRamifierStrippedPacket`

Conceptually, the dependency graph is

$$
\texttt{SignedBranchANormalForm}
\xrightarrow{\texttt{signedFiveAdicPowerSplit_of_normalForm}}
\texttt{SignedFiveAdicPowerSplit}
\xrightarrow{\texttt{signedGoldenRamifierStrippedPacket_of_powerSplit}}
\texttt{SignedGoldenRamifierStrippedPacket}.
$$

## Construction flow

The implementation is pure function composition:

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

1. Build the signed five-adic power split from `hNF`.
2. Pass that split to 0235.
3. Return the selected ramifier-stripped packet.

There is no tactic proof, coordinate expansion, `ring`, `omega`, or `norm_num`. All heavy mathematics is delegated to the upstream API.

## Lean-specific processing

The declaration is marked `noncomputable` because the dependency chain eventually reaches 0234 `signedGoldenRamifierStrippedPacket_of_exceptional`, which selects a packet using `Classical.choice`. The present definition does not invoke choice itself, but it inherits noncomputability from the chosen packet API.

In Lean, a named facade of this form lets downstream proofs simply write

```lean
signedGoldenRamifierStrippedPacket_of_normalForm hNF
```

without introducing local intermediate values or exposing their types. This reduces coupling to representation changes and keeps the consumer proof at the semantic level of “normal form to stripped packet.”

## Redundancy and duplication

Logically, the declaration is completely redundant: every use can be replaced by

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

Nevertheless, the dedicated name provides useful API redundancy:

- consumers of the normal-form layer need not know the intermediate representation;
- the pipeline becomes visible in declaration names;
- downstream proofs are less sensitive to refactoring of intermediate conversions;
- contradiction and closure theorems become shorter and easier to audit.

Thus the declaration adds no logical information, but it improves interface stability and proof readability.

## Optimization candidates

1. **Keep the current facade**
   - gives the smallest downstream dependency surface and the clearest intent.

2. **Remove 0235/0236 and use explicit composition everywhere**
   - reduces declaration count but leaks intermediate representations to consumers.

3. **Standardize the conversion pipeline as a namespace API**
   - a consistent family such as `of_normalForm`, `of_powerSplit`, and `of_exceptional` could make the conversion graph easier to discover.

4. **Concentrate the choice boundary**
   - if packet construction could be exposed as explicit witness data, the propagation of `noncomputable` declarations might be reduced.

Locally, the current one-line implementation is already close to optimal.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself uses no tactic and no generic Mathlib theorem directly.

Its immediate requirements are the upstream FLT5 types and conversion functions. The actual Mathlib dependency surface is therefore inherited from the modules implementing five-adic arithmetic, `GoldenInt`, norms, and divisibility.

The declaration in isolation is extremely lightweight, but import minimization must be measured at the level of `SignedGoldenRamifierStripped.lean`. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes, although this is primarily an API-architecture challenge rather than a theorem-proving challenge.

Possible variants are:

- A: the current named facade;
- B: explicit composition at every call site;
- C: a generic conversion pipeline or typeclass-based design;
- D: redesign packet construction around explicit computable witness data.

Useful metrics include downstream proof length, coupling to intermediate representations, refactor resilience, propagation of `noncomputable`, and API discoverability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this declaration appears immediately after 0235 `signedGoldenRamifierStrippedPacket_of_powerSplit` and immediately before `SignedGoldenRamifierStrippedCore`.

Japanese and English PDFs also exist on the target branch, but the exact PDF page or section corresponding to this `noncomputable def` was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0237 `SignedGoldenRamifierStrippedCore`**:

```lean
/-- Receiver contract for contradictions stated after the visible ramifier is removed. -/
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

By 0236, the pipeline can move directly from a signed normal form to a stripped packet. Declaration 0237 now defines the downstream contradiction contract: any such stripped packet is enough to derive `False`.

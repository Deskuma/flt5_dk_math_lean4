# 0237 — `SignedGoldenRamifierStrippedCore`

## Lean type

```lean
/-- Receiver contract for contradictions stated after the visible ramifier is removed. -/
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

This is an `abbrev`, not a theorem. It gives a short name to the downstream contradiction contract saying that any `SignedGoldenRamifierStrippedPacket`, after the visible ramifier `tau` has been removed once, is sufficient to derive `False`.

## Mathematical statement and meaning of the declaration

Conceptually, `SignedGoldenRamifierStrippedCore` is the proposition

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w)
\Longrightarrow \bot.
$$

The stripped packet constructed in 0231–0236 records a normalized state conceptually containing

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

The present `abbrev` isolates the remaining mathematical obligation: once the proof pipeline reaches such a stripped packet, a contradiction can be produced.

It therefore proves no new number-theoretic identity by itself. Instead, it packages the residual contradiction goal as a named proposition.

## Role in the full proof

By 0236, the direct pipeline

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

has been completed. Declaration 0237 appears immediately afterward and defines the abstract contract needed to turn the stripped packet into a refuter.

The next theorem in the source is

```lean
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

which lifts this local stripped-packet contradiction into a `SignedBranchARefuter`. The source then uses that refuter to close routed Branch-B counterexamples as well.

Thus 0237 is the architectural boundary between the local mathematics after ramifier stripping and the higher-level closure machinery for the signed Branch-A / Branch-B pipeline.

## Direct dependencies

The direct type dependencies are minimal:

- 0231 `SignedGoldenRamifierStrippedPacket`
- Lean's `False`

The indices `u v w : ℕ` are universally quantified.

There is no proof script and no direct theorem dependency. Conceptually, the declaration merely names the family of function types

$$
\texttt{SignedGoldenRamifierStrippedPacket}
\longrightarrow
\texttt{False}.
$$

Downstream, however, it is paired directly with 0236 `signedGoldenRamifierStrippedPacket_of_normalForm`.

## Construction flow

The declaration is only a transparent proposition alias:

```lean
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

1. Universally quantify over natural-number indices `u v w`.
2. Accept a corresponding `SignedGoldenRamifierStrippedPacket u v w`.
3. Require a proof of `False`.

No contradiction proof is supplied here. Later theorems assume a value `hCore` of this type and use it as a function from packets to contradiction.

## Lean-specific processing

Because this is an `abbrev`, Lean treats it as a transparent abbreviation rather than as a separate opaque definition. It can therefore unfold easily to

```lean
∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

when elaboration or simplification needs the underlying function type.

A function into `False` is Lean's direct refuter form: given a packet `p`,

```lean
hCore p : False
```

closes the branch immediately.

The indices are implicit binders `{u v w : ℕ}`, so downstream code normally lets Lean infer them from the packet type rather than supplying them explicitly.

## Redundancy and duplication

Logically, the alias is unnecessary. Every theorem could state the full type

```lean
(∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False)
```

directly.

The named contract is nevertheless useful:

- it makes the remaining proof core visible as a semantic object;
- adapters such as the signed Branch-A refuter become shorter;
- later equivalences between the stripped core and unit/fifth-power exclusion can be expressed cleanly;
- downstream code is insulated from changes in packet internals.

So the declaration is logically thin but architecturally valuable.

## Optimization candidates

1. **Keep the current `abbrev`**
   - minimal implementation and maximum transparency.

2. **Use a `def` instead**
   - would create a stronger definition boundary, but there is little benefit for such a simple proposition alias.

3. **Introduce a generic refuter abstraction**
   - for example `PacketRefuter P := P → False`; this is reusable but weakens FLT5-specific naming.

4. **Reformulate through `¬ Nonempty`**
   - possible as a no-packet formulation, but the current function-to-`False` shape composes more naturally with downstream adapters.

The current design is already close to minimal for an API contract.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present declaration itself directly needs almost no Mathlib surface beyond basic logic and natural numbers:

- `Nat`
- `Prop`
- `False`
- dependent universal quantification

The real import burden comes from the upstream definition of `SignedGoldenRamifierStrippedPacket`. No advanced tactic or number-theory theorem is used by 0237 itself.

Because this museum pass does not run a Lean build, the exact minimal import set for the full `SignedGoldenRamifierStripped.lean` module remains unverified.

## Comparator challenge suitability

Yes, although this is mainly an API-contract design challenge rather than a proof-search challenge.

Possible variants are:

- A: current `abbrev` contract;
- B: write the full function type at every call site;
- C: introduce a generic `PacketRefuter` abstraction;
- D: use a `¬ Nonempty` no-packet formulation.

Useful metrics include proof-term length, readability of types, simplicity of downstream adapters, refactor resilience, and ease of unfolding.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this `abbrev` immediately after 0236 `signedGoldenRamifierStrippedPacket_of_normalForm` and immediately before `signedBranchARefuter_of_goldenRamifierStrippedCore`.

The current Japanese and English 0236 documents record the same source order. The target branch also records the presence of Japanese and English PDFs, but the exact PDF page or section corresponding to this small `abbrev` was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0238 `signedBranchARefuter_of_goldenRamifierStrippedCore`**:

```lean
/-- A refuter for all stripped packets closes both signed orientations. -/
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

Declaration 0237 defines the contract from a stripped packet to `False`. Declaration 0238 uses the bridge from 0236 to create such a packet from a signed normal form and feeds it to `hCore`, thereby lifting the stripped core into the full `SignedBranchARefuter` interface.

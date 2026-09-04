# 0116 — `signedBranchARefuter_of_squareGoldenExceptionalCore`

## Lean type

```lean
/-- A refuter for every exceptional square-golden packet closes both signed orientations. -/
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

This theorem is an adapter theorem that constructs a `SignedBranchARefuter` from a `SignedSquareGoldenExceptionalCore`.

## Mathematical statement

`SignedSquareGoldenExceptionalCore` is a contradiction receiver giving, for every $u,v,w$,

$$
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot.
$$

On the other hand, `SignedBranchARefuter` requires, for every $u,v,w$,

$$
\operatorname{SignedBranchANormalForm}(u,v,w)\to\bot.
$$

Article 0114, `signedSquareGoldenExceptionalPacket_of_normalForm`, provides

$$
\operatorname{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w).
$$

The present theorem composes that conversion in front of `hCore` and obtains

$$
\operatorname{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)
\longrightarrow
\bot.
$$

Mathematically, no new algebraic identity or divisibility fact is proved here. The theorem only connects the already established map from normal forms to packets with the core assertion that every such packet is contradictory.

## Role in the overall proof

This theorem is the **boundary adapter** between the signed Branch-A layer and the square-golden exceptional layer.

Articles 0111–0114 prepare the producer side that constructs a square-golden exceptional packet. Article 0115 defines the receiver contract that returns `False` from such a packet. Article 0116 connects the two and pulls the downstream contradiction back to the whole `SignedBranchANormalForm` layer.

```text
SignedBranchANormalForm
  → SignedSquareGoldenExceptionalPacket
  → False
```

As a result, subsequent Branch-B closure theorems do not need to unpack the internal structure of the square-golden packet again. They can receive the contradiction through the existing `SignedBranchARefuter` API.

## Direct dependencies

### `SignedSquareGoldenExceptionalCore`

The contradiction receiver discussed in 0115.

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

### `SignedBranchARefuter`

The existing contract excluding signed Branch-A normal forms.

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

### `signedSquareGoldenExceptionalPacket_of_normalForm`

The producer discussed in 0114.

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

These three declarations are enough to close the logical structure of the present theorem.

## Proof flow

The proof has only two stages.

1. `intro u v w hNF` introduces the universally quantified indices and the normal-form hypothesis required by `SignedBranchARefuter`.
2. `signedSquareGoldenExceptionalPacket_of_normalForm hNF` constructs the packet, which is then passed to `hCore` to obtain `False`.

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

This single line expresses almost the entire mathematical content of the theorem.

## Lean-specific processing

### `intro` through the expected type

The goal is the abbreviation `SignedBranchARefuter`, but Lean unfolds its body sufficiently to accept

```lean
intro u v w hNF
```

against

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False.
```

### Inference of implicit indices

Both `hCore` and the producer use `{u v w : ℕ}` as implicit parameters. The type of `hNF` determines those indices, so neither

```lean
signedSquareGoldenExceptionalPacket_of_normalForm hNF
```

nor

```lean
hCore (...)
```

requires explicit named arguments.

### Propagation of `noncomputable`

The used definition `signedSquareGoldenExceptionalPacket_of_normalForm` is `noncomputable`, but the present declaration is a theorem proving a proposition, so it does not need a `noncomputable` modifier. Object construction involving classical choice remains isolated in the producer layer; this theorem merely consumes its result as a proof term.

### Almost tactic-free structure

Apart from `intro`, the body is a single `exact`. There is no `rw`, `simp`, `ring`, `omega`, or cast handling. This shows that all algebraic, five-adic, and signed-orientation processing has already been encapsulated by upstream declarations.

## Redundancy and duplication

The theorem has the same shape as earlier producer/consumer bridges.

Conceptually it is just precomposition of a negation:

```lean
(A → B) → (B → False) → (A → False)
```

Thus there is structural duplication that could be abstracted into a generic helper. However, the name `signedBranchARefuter_of_squareGoldenExceptionalCore` records the transition between proof layers and is therefore useful as architecture-level documentation.

The proof

```lean
by
  intro u v w hNF
  exact ...
```

is also close to the lambda expression

```lean
fun hNF => hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

and could be shortened further. The current form remains clearer because it makes the indices and the normal-form hypothesis explicit.

## Optimization candidates

### 1. Direct lambda form

Conceptually the theorem can be compressed toward a point-free or lambda-style composition. The current proof is already so short that the practical gain would be minimal.

### 2. Generic refuter transport

For indexed propositions or packet families, one could introduce a generic helper transporting

```lean
(A i → B i) → (B i → False) → (A i → False).
```

This would factor out identical adapters. The tradeoff is that a named theorem currently exposes the proof-layer transition directly in the declaration graph, so such abstraction is most attractive only if many more identical adapters appear.

### 3. Preserve producer/core API alignment

The most valuable optimization is not reducing line count but preserving the interface in which the producer returns exactly `SignedSquareGoldenExceptionalPacket` and the core consumes exactly that packet. This type-level alignment is why the adapter closes in one line.

## Required Mathlib imports and import optimization

The target standalone source uses

```lean
import Mathlib
```

at the top level.

This theorem itself directly needs almost no Mathlib-specific functionality: only Lean function application, universal quantification, `False`, `intro` / `exact`, and project declarations. It does not directly use `ring`, `omega`, integer arithmetic APIs, or divisibility APIs.

Therefore, in a modular source file, `Mathlib` as a whole should not be required solely for this theorem. The actual import requirement is determined by the transitive closure of the modules providing `SignedSquareGoldenExceptionalCore`, `SignedBranchARefuter`, and `signedSquareGoldenExceptionalPacket_of_normalForm`.

In this repository the standalone artifact concatenates source modules and aggregates them under `import Mathlib`, so an exact minimal import set cannot be established from the standalone artifact alone. No Lean build was performed, so any concrete import reduction remains unverified.

## Comparator challenge suitability

**Yes. It is especially suitable as a proof-composition and API-design comparison task.**

Possible variants include:

- the current `intro` + `exact` proof;
- a direct lambda-expression composition;
- a version using a generic refuter-transport helper;
- a version that expands the producer and constructs the packet directly from `SignedFiveAdicPowerSplit`;
- a version using the `SignedBranchARefuter` abbreviation versus writing its expanded type directly.

Evaluation criteria should include not just line count but locality of dependencies, error quality, readability of the proof graph, and robustness against changes in upstream implementation.

In particular, expanding the producer would break the abstraction boundary established in 0112–0114 without actually reducing dependencies. The current theorem is therefore likely superior from an architectural perspective.

## Correspondence with the existing PDFs

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The formal source for this article is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The corresponding PDF pages were not directly inspected through the GitHub connector in this run, so no specific section or page number is supplied by inference.

## Next theorem to read

The next unexplained theorem in source order is

```lean
/-- The same square-golden core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_squareGoldenExceptionalCore hCore) hPack hBranch
```

Article 0116 transports `SignedSquareGoldenExceptionalCore` into `SignedBranchARefuter`; the next theorem passes that refuter to the existing `branchB_false_of_signedBranchARefuter` and closes the entire Branch-B candidate. In dependency order, this should naturally become article 0117.

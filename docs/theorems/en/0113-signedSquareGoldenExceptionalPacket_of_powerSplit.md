# 0113 — `signedSquareGoldenExceptionalPacket_of_powerSplit`

## Lean type

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

This declaration is not a theorem but a `noncomputable def`. From the fact proved in 0112, `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`, namely

```lean
Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

it uses `Classical.choice` to select one concrete packet and exposes it as a value directly usable downstream.

## Mathematical statement

The input is an exact signed five-adic power split

```lean
s : SignedFiveAdicPowerSplit u v w
```

By 0112, there already exist integer coordinates $M,N,\delta$ and provenance associated with this `s` such that

$$
\operatorname{GoldenNorm}(M,N)=5b^5,
$$

$$
M-2N=5^8a^{10},
$$

$$
M^2-4N^2=\delta^2,
$$

$$
(2M+N)^2-5N^2=20b^5
$$

all hold simultaneously. Here $a,b$ are the power-split witnesses stored in the input `s`.

This declaration proves no new mathematical identity. It selects one already-proved witness of `SignedSquareGoldenExceptionalPacket u v w` and fixes all of its fields as a reusable object.

## Role in the overall proof

Up through 0112, the development only had the proposition-level fact that such a packet exists. Declaration 0113 turns that existence proof into an object-level API whose fields can be projected by later definitions and theorems.

Because of this conversion, downstream code no longer needs to repeatedly write

```lean
rcases nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s with ⟨p⟩
```

to extract an existential witness. Instead it can simply use

```lean
let p := signedSquareGoldenExceptionalPacket_of_powerSplit s
```

or directly project fields such as `p.M`, `p.N`, `p.golden_eq`, and `p.tenth_boundary`.

The immediately following declaration

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

reuses 0113 unchanged to provide the public conversion from a signed normal form to the packet. Thus 0113 is the public constructor API between the power-split layer and the square-golden exceptional-packet layer.

## Direct dependencies

The direct dependency set is very small.

1. `SignedFiveAdicPowerSplit`
   - Input type.
2. `SignedSquareGoldenExceptionalPacket`
   - Output type.
3. `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`
   - 0112. A private theorem proving that the output type is inhabited.
4. `Classical.choice`
   - The classical choice operator selecting a value of `α` from `Nonempty α`.

The mathematically heavy dependencies, such as `GN5_eq_goldenNorm_squareLink`, `sumGN5_eq_goldenNorm_signed`, the square-discriminant identities, and the discriminant-five identity, have all been encapsulated inside 0112. Declaration 0113 does not depend on them directly.

## Definition flow

The body is a single line:

```lean
Classical.choice
  (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

There are only two steps.

1. Apply 0112 to `s` and obtain

```lean
Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

2. Use `Classical.choice` to extract one inhabitant and return it as

```lean
SignedSquareGoldenExceptionalPacket u v w
```

There is no difference/sum case split here, and no casts, `ring`, or `simpa`. Those operations are completely hidden inside the construction proof of 0112.

## Lean-specific processing

### `noncomputable def`

Because selection by `Classical.choice` does not provide an executable algorithm, the declaration must be marked `noncomputable`. The purpose here is not to compute executable values of $M,N,\delta$, but to obtain a witness that can be referenced consistently inside proofs.

### `Classical.choice`

`Nonempty α` is a proof-irrelevant proposition asserting that `α` has an element; by itself it does not return a value on which fields can be projected. `Classical.choice` lifts this existence fact to a value of type `α`.

This separation is useful in Lean architecture. Declaration 0112 is the private implementation theorem proving the correctness of the construction, while 0113 is the short public object constructor used downstream.

### Definitional transparency

Unfolding this definition exposes `Classical.choice (...)`, but downstream proofs should normally not depend on the concrete mechanism by which the witness is selected. The stable interface is to use only the theorem fields carried by `SignedSquareGoldenExceptionalPacket`.

## Redundancy and duplication

There is almost no computational or logical duplication in the body itself. Architecturally, however, the development uses the two-stage pattern

```lean
private theorem ... : Nonempty Packet := by ...
noncomputable def ... : Packet := Classical.choice (...)
```

so it introduces one more declaration than a design that directly constructs the packet inside a `noncomputable def`.

That extra layer appears intentional: the complicated proof term remains isolated inside a private theorem, while the public API remains one line long.

The following `signedSquareGoldenExceptionalPacket_of_normalForm` also returns the same output type, but it is not a duplicate constructor. It is an adapter that raises the input interface one level to `SignedBranchANormalForm`.

## Optimization candidates

1. Keep the current design.
   - The complex construction of 0112 and the public API of 0113 are cleanly separated.
2. Direct-constructor version.
   - Construct the packet inside a `noncomputable def` using `by classical ...` and remove the `Nonempty` theorem. This would reduce declarations but mix proof implementation back into the public definition.
3. Compare `choose` / `Classical.choose`-style formulations.
   - Mostly a notational comparison, with little essential improvement.
4. Investigate a computable constructor.
   - The witness in 0112 is in fact built explicitly by a source case split, so it may be worth checking whether the packet can be returned without classical choice. This depends on Lean's reducibility and `Prop`-elimination restrictions when data is assembled from proof fields. Because no Lean build is performed here, this remains an optimization hypothesis rather than a confirmed refactor.
5. Avoid unfolding this definition downstream.
   - Use only the packet-field API and avoid coupling later proofs to choice implementation details.

## Required Mathlib imports and import optimization

The generated standalone artifact begins with

```lean
import Mathlib
```

so this is sufficient for the artifact containing the declaration.

For 0113 itself, the main Mathlib facilities directly needed are `Nonempty` and `Classical.choice`; no algebraic tactics are used. Therefore `import Mathlib` is vastly broader than necessary if this declaration is considered in isolation.

However, the actual module `SignedSquareGoldenExceptional.lean` also contains the algebraic construction of 0112 and depends on many DkMath declarations. The module-level minimal import set cannot be determined from 0113 alone. Since no Lean build is performed in this task, no exact minimal-import claim is made.

## Comparator challenge suitability

**Suitable.** This is more interesting as a Lean API-design challenge than as a mathematical challenge.

Useful variants to compare are:

1. The current `Nonempty` theorem + `Classical.choice` design.
2. A `noncomputable def` that constructs the packet directly.
3. A computable candidate that returns data directly from the source case split without classical choice.
4. An intermediate dependent-pair or subtype witness design.

Evaluation criteria should include:

- brevity of the public API
- degree of proof-implementation isolation
- presence or absence of classical dependencies
- stability under reduction and unfolding
- locality of downstream error messages
- dependency footprint under refactoring

In particular, the question “if 0112 explicitly constructs the witness, why does 0113 still use classical choice?” makes this a useful example for comparing Lean's `Prop` elimination with API-separation choices.

## Position in the source material

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The current GitHub connector does not directly expose the relevant PDF body pages, so no page or section numbers are guessed.

The formal source of truth is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section inside `Flt5DkMath/FLT5StandAlone.lean`. There, this declaration appears immediately after 0112 and immediately before the normal-form adapter.

## Next declaration to read

The next declaration is

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

If 0113 is the public constructor selecting a packet from a power split, the next declaration composes `SignedBranchANormalForm` → `SignedFiveAdicPowerSplit` → square-golden packet in one line. Reading it next makes the conversion pipeline explicit.
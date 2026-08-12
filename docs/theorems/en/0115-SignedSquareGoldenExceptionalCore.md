# 0115 — `SignedSquareGoldenExceptionalCore`

## Lean type

```lean
/-- Receiver contract for contradictions stated on the common signed square/norm packet. -/
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

This declaration is not a theorem but an `abbrev`. It gives a name to a universal contradiction receiver: given any `SignedSquareGoldenExceptionalPacket u v w`, it must be possible to return `False`.

## Mathematical statement

`SignedSquareGoldenExceptionalPacket u v w` stores integer coordinates $M,N,\delta$ and witnesses $a,b$ obtained from a signed five-adic power split, including at least

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
(2M+N)^2-5N^2=20b^5,
$$

as well as the difference / sum provenance.

`SignedSquareGoldenExceptionalCore` expresses the contradiction contract that **no such packet can exist for any $u,v,w$**:

$$
\forall u,v,w,\quad
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot.
$$

At this point the declaration does not specify which invariant creates the contradiction. Later layers involving golden integers, the ramifier, unit sectors, and descent are expected to implement this contract; once they do, the upstream signed Branch-A normal form can be ruled out uniformly.

## Role in the overall proof

This declaration is the **receiver interface** of the square-golden exceptional layer.

Articles 0111–0114 were on the **producer side**, progressively transforming input into a `SignedSquareGoldenExceptionalPacket`:

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
```

At 0115 the direction reverses:

```text
SignedSquareGoldenExceptionalPacket
  → False
```

This separation lets the upstream development focus only on constructing the packet, while downstream arguments can prove contradiction using only the packet invariants. They no longer need to carry the original Fermat equation or the signed-orientation case split.

The immediately following theorem uses this architecture in one line:

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

Thus 0114 is the producer, 0115 is the consumer contract, and the next theorem is the adapter connecting them.

## Direct dependencies

### `SignedSquareGoldenExceptionalPacket`

This is the only direct project declaration used by the alias. It is the `Type` packet explained in 0111, carrying the five-adic split, signed provenance, golden norm, tenth-power boundary, square discriminant, and five-discriminant relation.

### `False`

Lean's built-in empty proposition. It is the codomain of the contradiction function obtained from a packet.

### Implicit natural-number parameters

```lean
{u v w : ℕ}
```

are implicit binders. At use sites, Lean infers them from the type of the supplied packet.

## Proof / definition flow

Because this is an `abbrev`, there is no proof script. Logically, the definition can be read as follows.

1. Take arbitrary natural numbers `u v w`.
2. Assume `SignedSquareGoldenExceptionalPacket u v w`.
3. Require a term of `False` from that packet.
4. Give the resulting universally quantified function type the name `SignedSquareGoldenExceptionalCore`.

The important point is that this declaration does **not itself prove the contradiction**. The actual mathematical task is to construct an inhabitant of this type in the later golden-arithmetic development.

## Lean-specific processing

### `abbrev`

`abbrev` is a transparent abbreviation. During elaboration and reduction, Lean can readily unfold it to

```lean
∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

This is appropriate here because the goal is only to assign a meaningful name to a long receiver type, without introducing a wrapper structure or an opaque definition.

### Implicit binders

Because `{u v w : ℕ}` are implicit, an application such as

```lean
hCore hPacket
```

lets Lean infer the indices from

```lean
hPacket : SignedSquareGoldenExceptionalPacket u v w
```

and normally avoids the need to write

```lean
hCore (u := u) (v := v) (w := w) hPacket
```

explicitly.

### `P → False` and negation

In Lean, `¬ P` is definitionally `P → False`. Therefore, for fixed `u v w`, the core has the same logical content as

```lean
¬ SignedSquareGoldenExceptionalPacket u v w
```

The current form quantifies the indices outside and is convenient to pass directly as a higher-order receiver.

## Redundancy and duplication

The same architecture previously appeared in

- `BranchBFifthPowerCore`
- `BranchBSquareGoldenCore`

Each names a receiver contract of the form “given the normalized packet / normal form, return `False`.”

This is logically repetitive, but the duplication is **intentional and useful at the architecture level**. A layer-specific core name tells the reader exactly how far the reduction has progressed without inspecting the body of the proposition.

Likewise,

```lean
∀ {u v w}, Packet u v w → False
```

is mathematically close to an existential exclusion such as

```lean
¬ ∃ u v w, Packet u v w
```

or to a formulation using a suitable dependent existential / `Nonempty`. The current curried receiver form has the practical advantage that a concrete packet can be consumed immediately as `hCore packet`.

## Optimization candidates

### 1. Generic contradiction receiver

If many more identical core declarations appear, a generic refuter type for indexed packets could be introduced. Conceptually:

```lean
abbrev IndexedRefuter (P : ℕ → ℕ → ℕ → Type) : Prop :=
  ∀ {u v w}, P u v w → False
```

However, the dedicated name `SignedSquareGoldenExceptionalCore` makes the proof layer explicit. Generalizing merely to save a line may reduce the readability of the proof graph.

### 2. Compare with `¬ Nonempty ...`

Because the packet lives in `Type`, one could instead state, for fixed indices,

```lean
¬ Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

But the producer side already returns a concrete packet object, so `Packet → False` avoids unnecessary `Nonempty.intro` construction and elimination and is therefore more direct.

### 3. Minimize the core input

If later contradiction proofs turn out not to use all fields of the packet, a smaller packet containing only the required invariants could be extracted. This could reduce proof dependencies and would make a useful Comparator challenge.

This should be decided only after reading the downstream golden-arithmetic and ramifier-stripping code in dependency order; at this point it remains an optimization candidate rather than a confirmed improvement.

## Required Mathlib imports and import optimization

The standalone source currently uses

```lean
import Mathlib
```

The declaration itself requires very little directly: Lean's `Prop`, `False`, universal quantification, function types, natural numbers, and the project declaration `SignedSquareGoldenExceptionalPacket`. It invokes no tactic, ring-normalization lemma, divisibility API, or golden-arithmetic lemma from Mathlib.

Therefore there is no reason to import all of `Mathlib` solely for this alias in a modular source file. The actual minimum import is determined by the import closure of the module defining `SignedSquareGoldenExceptionalPacket`.

If the core alias remains in the same module as the packet definition, no additional import may be needed at all. No Lean build was run in this pass, so a concrete minimal import set has not been verified.

## Comparator challenge suitability

**Yes. It is well suited as a proof-API / interface-design challenge.**

Possible designs to compare include:

- the current `∀ {u v w}, Packet u v w → False`
- `∀ {u v w}, ¬ Packet u v w`
- an existential exclusion equivalent to `¬ ∃ u v w, Nonempty (Packet u v w)`
- a generic indexed-refuter alias
- a receiver that accepts only the minimal invariant packet required for contradiction

Evaluation should consider not only kernel-proof length but also simplicity of connection to producers, implicit inference, locality of error messages, readability of the proof graph, and coupling to downstream layers.

In particular, the fact that the next theorem closes with

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

is a strong advantage of the current API.

## Correspondence with the existing PDFs

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The formal basis of this article is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The corresponding PDF pages were not directly inspected through the GitHub connector in this pass, so no page or section numbers are supplied by inference.

## Next theorem to read

The next unexplained theorem is

```lean
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

It directly connects the 0114 producer to the 0115 receiver contract and shows that excluding every square-golden exceptional packet is enough to refute the entire signed Branch-A normal form. In dependency order, this is the natural declaration to read as 0116.

# 0114 — `signedSquareGoldenExceptionalPacket_of_normalForm`

## Lean type

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

This declaration is not a theorem but a `noncomputable def`. Starting from a `SignedBranchANormalForm`, it first applies

```lean
signedFiveAdicPowerSplit_of_normalForm
```

to obtain an exact five-adic power split, and then passes that value to 0113

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit
```

to return a signed square-golden exceptional packet directly.

## Mathematical statement

The input is a signed Branch-A normal form

```lean
hNF : SignedBranchANormalForm u v w
```

By composing previously established transformations, one can choose from it integer coordinates $M,N,\delta$, five-adic power witnesses $a,b$, and difference / sum provenance, all packaged into a single object.

Thus downstream code can access directly from `hNF` the invariants stored in the packet:

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
(2M+N)^2-5N^2=20b^5.
$$

This declaration does not reprove these equations. Their mathematical content is encapsulated upstream in `signedFiveAdicPowerSplit_of_normalForm` and `signedSquareGoldenExceptionalPacket_of_powerSplit`.

## Role in the full proof

This declaration is a **composition adapter** between the signed normal-form layer and the square-golden exceptional layer.

The transformation pipeline is

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
```

0113 exposed an API whose direct input was a power split. The present declaration provides a convenience constructor callable one layer earlier, from `SignedBranchANormalForm`. As a result, downstream contradiction cores do not need to mention the five-adic intermediate packet and can move directly from signed normal form to square-golden packet.

Indeed, the later theorem `signedBranchARefuter_of_squareGoldenExceptionalCore` can write

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

which makes the architectural purpose of this declaration explicit.

## Direct dependencies

### `SignedBranchANormalForm`

The input type. It stores the orientation and normal-form data for signed Branch-A.

### `signedFiveAdicPowerSplit_of_normalForm`

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

This is the upstream adapter that chooses an exact five-adic power split from a normal form.

### `signedSquareGoldenExceptionalPacket_of_powerSplit`

Article 0113. This is the public constructor that chooses a square-golden exceptional packet from a power split.

### `SignedSquareGoldenExceptionalPacket`

The output type. It packages the five-adic split, signed provenance, golden norm, tenth boundary, square discriminant, and five-discriminant relation.

## Definition flow

The body is simply function composition.

1. Receive `hNF : SignedBranchANormalForm u v w`.
2. Obtain `SignedFiveAdicPowerSplit u v w` via `signedFiveAdicPowerSplit_of_normalForm hNF`.
3. Pass that value to `signedSquareGoldenExceptionalPacket_of_powerSplit`.
4. Return `SignedSquareGoldenExceptionalPacket u v w`.

There is no new case split, arithmetic normalization, cast management, or witness construction.

## Lean-specific processing

### `noncomputable def`

As in 0113, the downstream packet is ultimately selected using `Classical.choice` upstream. Therefore this composition adapter is also `noncomputable`.

However, `Classical.choice` does not appear directly in this declaration. Noncomputability is inherited from the constructor on which it depends.

### Implicit parameters

`{u v w : ℕ}` are implicit and inferred by Lean from the type of `hNF`. No explicit type annotation is needed for the intermediate value.

### Tactic-free definition

The right-hand side after `:=` is a plain expression rather than a `by` proof block. The elaborator only has to match the codomain of one function with the domain of the next.

## Redundancy and duplication

This declaration is intentional API-level redundancy.

In principle, every caller could write

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

directly, so the named wrapper is not logically necessary.

It is nevertheless useful because it hides the five-adic intermediate layer from downstream theorems and makes the architectural boundary explicit. In particular, it keeps the proof of `signedBranchARefuter_of_squareGoldenExceptionalCore` to a single line.

## Optimization candidates

### 1. Generalize as function composition

If many adapters of exactly this shape accumulate, a generic composition helper could be introduced. For a one-line definition, however, excessive abstraction may make the proof graph less readable rather than more readable.

### 2. Move to a computable constructor

If the upstream packet construction were redesigned to avoid `Classical.choice`, then the `noncomputable` marker could potentially be removed here as well. This is not a local optimization: it would require redesigning the witness construction across 0112–0113.

### 3. Keep adapter naming consistent

The naming pattern `..._of_normalForm` / `..._of_powerSplit` is highly informative and worth preserving. Explicitly naming the source type in the suffix makes the dependency graph easier to inspect.

## Required Mathlib imports and import optimization

The current standalone source uses `import Mathlib`.

This declaration itself invokes no tactic, ring-theoretic lemma, or number-theoretic theorem. It only applies existing project declarations. Its noncomputability also comes from an upstream constructor rather than from direct use of a Mathlib API in the body.

Therefore there is no reason for this declaration alone to require the full `Mathlib` import. In a modularized source tree, the practical minimum is determined by the project modules that provide `SignedBranchANormalForm`, `signedFiveAdicPowerSplit_of_normalForm`, `SignedSquareGoldenExceptionalPacket`, and `signedSquareGoldenExceptionalPacket_of_powerSplit`.

It is plausible that a future adapter-only module could import only those project modules. This is an explicit optimization hypothesis rather than a verified claim, because no Lean build was run in this pass.

## Comparator challenge suitability

**Suitable, especially as an API-design challenge.**

Useful alternatives to compare include:

- the current named `..._of_normalForm` wrapper,
- direct two-function composition at every call site,
- a generic composition helper,
- a redesigned computable constructor avoiding `Classical.choice`.

The key evaluation criteria are not proof length but visibility of dependency boundaries, discoverability, locality of errors, refactor resilience, and readability of downstream theorems.

## Relation to the existing PDFs

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

For this declaration, the repository Lean source is used as the formal authority. The exact corresponding PDF page was not directly inspected through the GitHub connector in this pass, so no page or section number is guessed.

## Next declaration to read

The next unexplained declaration is

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

At this point the square-golden exceptional packet changes role: from an object to construct into an object whose existence is rejected by a universal contradiction receiver. Since 0114 provides the packet directly from a normal form, reading this core next is the natural continuation in dependency order.

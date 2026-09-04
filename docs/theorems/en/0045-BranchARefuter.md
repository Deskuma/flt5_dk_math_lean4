# 0045 — `DkMath.FLT.Five.BranchARefuter`

## 1. Declaration

```lean
/-- Reusable receiver for the completed signed five-adic and golden-order refutation
of a primitive candidate whose natural gap is divisible by five. -/
abbrev BranchARefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False
```

This article studies not a theorem proof but a proposition-level interface for receiving a completed refutation of Branch A.

## 2. Lean type

`BranchARefuter` itself has type `Prop`. After transparent expansion it is a function type over implicit natural numbers `x y z`:

```lean
CounterexamplePack x y z → BranchACondition y z → False
```

Because it is an `abbrev`, Lean can unfold the right-hand side transparently when needed. It introduces neither a new structure nor an opaque definition.

## 3. Mathematical statement

`CounterexamplePack x y z` represents a positive primitive candidate satisfying

$$
x^5+y^5=z^5,
$$

and `BranchACondition y z` represents

$$
5\mid(z-y).
$$

Thus `BranchARefuter` is the contract for a refutation procedure asserting that no candidate can satisfy both conditions:

$$
\forall x,y,z\in\mathbb N,\quad
CounterexamplePack(x,y,z)\land 5\mid(z-y)\Longrightarrow\bot.
$$

The declaration does not itself prove the contradiction. The later signed five-adic normalization and golden-order descent eventually construct a concrete term satisfying this contract.

## 4. Role in the complete proof

The preceding declaration `BranchACondition` names the exceptional branch. This declaration specifies the public receiver used to close it.

```text
natural-number branch test
  CounterexamplePack + BranchACondition
                 ↓
          BranchARefuter
                 ↓
signed five-adic packet / golden-order descent
```

The upper-level final theorem need not know the internal details of the Branch A descent; it only applies a `BranchARefuter`. Conversely, the long lower-level descent can compress its final output into this small function type.

## 5. Direct dependencies

### 5.1 `CounterexamplePack`

The primitive candidate packet containing positivity, coprimality of the two left bases, and the Fermat equation.

### 5.2 `BranchACondition`

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

This names the exceptional branch where the natural-number gap is divisible by five.

### 5.3 `False`

The result is a contradiction rather than data. Hence `BranchARefuter` behaves as a negating function that eliminates every Branch A candidate.

## 6. Proof flow

Since this is an `abbrev`, it has no proof script. A standard use has the form

```lean
have hFalse : False := hRefuter hPack hBranchA
exact hFalse
```

or, when the goal is already `False`, simply

```lean
exact hRefuter hPack hBranchA
```

The actual proof obligation is deferred to the later module that constructs a term of type `BranchARefuter`.

## 7. Lean-specific processing

### 7.1 Implicit quantification

`{x y z : ℕ}` are implicit arguments inferred from the types of `hPack` and `hBranchA`.

### 7.2 Curried implication

The right-hand side is a two-stage function rather than a conjunction:

```lean
CounterexamplePack x y z → BranchACondition y z → False
```

It is applied as `hRefuter hPack hBranchA`.

### 7.3 Transparency of `abbrev`

`abbrev` behaves like a transparent type alias. Later proofs may start directly with `intro x y z hPack hBranchA`; normally no explicit `unfold BranchARefuter` is needed.

### 7.4 Computation inside `Prop`

The interface hides implementation details but does not bypass kernel checking. Every concrete refuter term must ultimately return a proof of `False`.

## 8. Redundancy and duplication

Logically, `BranchARefuter` only names its right-hand function type. The declaration is therefore redundant in a strict logical sense, but not in design: it is a semantic alias stabilizing the exit point of a long proof route.

As with the earlier Branch B provider interfaces, it separates the number-theoretic core from upper-level routing.

## 9. Optimization candidates

### 9.1 Preserve the current form

The type is short and its purpose is clear. Replacing it with a `def` or `structure` offers little immediate benefit.

### 9.2 Strengthen argument naming

Consistent use-site names such as `hBranchA` improve readability compared with repeatedly passing a raw proof of `5 ∣ z - y`.

### 9.3 Generalize cautiously

One could abstract a generic branch refuter of the form

```lean
∀ p, Pack p → Condition p → False
```

but `BranchARefuter` is already a small, useful part of the FLT5 public vocabulary. Further abstraction may make dependency tracking harder.

## 10. Required Mathlib imports

The declaration itself only requires the prior availability of

```lean
CounterexamplePack
BranchACondition
```

The types `ℕ`, `Prop`, `False`, implication, and universal quantification belong to Lean's foundational environment. Thus a minimal DkMath import providing those two declarations is sufficient; importing all of `Mathlib` is excessive for this declaration alone.

The generated standalone file uses `import Mathlib`, but that is not evidence of minimality.

## 11. Import optimization candidate

If `BranchA.lean` defines `BranchACondition` locally and only imports the module containing `CounterexamplePack`, the conceptual minimum is likely

```lean
import DkMath.FLT.Five.Basic
```

However, the exact import line of the canonical module was not established from the generated standalone source alone. This is an optimization candidate, not a verified fact.

## 12. Comparator challenge suitability

The declaration is highly suitable as an API-design and Lean-type-reading challenge rather than as a difficult mathematics problem.

### Challenge A

Define an `abbrev` for

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False
```

### Challenge B

Given `hRefuter : BranchARefuter`, `hPack : CounterexamplePack x y z`, and `hA : BranchACondition y z`, prove `False` in one line.

Expected solution:

```lean
exact hRefuter hPack hA
```

### Challenge C

Compare this contract with a `structure` wrapper and explain the differences in application syntax, transparency, and future field extensibility.

## 13. Verified facts and explicit conjectural points

The following facts were verified:

- The declaration is named `DkMath.FLT.Five.BranchARefuter`.
- It is defined as `abbrev BranchARefuter : Prop`.
- Its expansion is `CounterexamplePack x y z → BranchACondition y z → False`.
- The source comment presents it as a reusable receiver for the completed signed five-adic and golden-order refutation.
- It is the final declaration of `BranchA.lean`.

The exact minimal import line remains a candidate requiring inspection of the canonical module header.

## 14. Next declaration to read

The next declaration is

```lean
DkMath.FLT.Five.CounterexamplePack.swap
```

It is the entry point to signed Branch A routing and proves that swapping the two left coordinates preserves a `CounterexamplePack`. This symmetry bridge is used when routing a Branch B candidate into either the difference-gap or sum-gap five-adic orientation.

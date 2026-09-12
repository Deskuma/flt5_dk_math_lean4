# 0403 `CounterexamplePackRefuter`

## Declaration kind

`abbrev`

## Lean type

```lean
/-- Refuters for both routed orientations refute every primitive packet. -/
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

## Mathematical meaning

`CounterexamplePackRefuter` is not itself a theorem. It is a named proposition used as a shared target type by the subsequent closure theorems.

After unfolding, it says

$$
\forall x,y,z\in\mathbb N,
\quad
\mathrm{CounterexamplePack}(x,y,z)\to\bot.
$$

A `CounterexamplePack x y z` packages a positive primitive FLT5 counterexample candidate, so mathematically this means that any primitive candidate satisfying

$$
x^5+y^5=z^5,
\qquad
x,y,z>0,
\qquad
\gcd(x,y)=1
$$

can be turned into a contradiction.

Thus, constructing one inhabitant of this proposition is enough to rule out every primitive FLT5 counterexample.

The important point is that this declaration does not yet construct such an inhabitant. It fixes, as a named type, exactly what must be proved in order to close the primitive layer.

## Role in the full proof

The immediately preceding theorem `CounterexamplePack.branchB_orientation` shows that every primitive packet satisfies

$$
5\nmid(z-y)
\quad\text{or}\quad
5\nmid(z-x).
$$

Hence either the original packet or `p.swap` can always be routed into a clean Branch-B orientation.

`CounterexamplePackRefuter` is the receiving interface that turns this routing information into the global primitive-level target

$$
\text{primitive packet}\longrightarrow\bot.
$$

The very next theorem

```lean
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

constructs the first concrete inhabitant of this interface.

The proof architecture can therefore be summarized as

$$
\text{local Branch-B exclusion}
\longrightarrow
\text{orientation routing}
\longrightarrow
\texttt{CounterexamplePackRefuter}
\longrightarrow
\text{positive FLT5 refuter}.
$$

This `abbrev` marks the API boundary between the local algebraic, five-adic, and golden-order arguments and the final FLT5 closure layer.

## Direct dependencies

### `CounterexamplePack`

This is the only DkMath-specific definition directly referenced by the declaration.

At the beginning of the canonical standalone source it is defined as

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
```

Accordingly, `CounterexamplePackRefuter` is a function type taking the entire primitive packet to `False`.

### `False`

Lean's standard proposition `False : Prop`. Returning `False` from a packet means deriving a contradiction from its assumed existence.

### Implicit binders `{x y z : ℕ}`

The three natural-number indices are implicit, so later uses can infer them from a term `p : CounterexamplePack x y z` instead of passing them explicitly.

The declaration itself does not directly depend on `branchB_orientation` or any golden-order theorem. Those results are dependencies of the later theorems that construct inhabitants of `CounterexamplePackRefuter`.

## Construction flow

Because this is an `abbrev`, there is no proof script. The construction consists entirely of designing the target proposition.

### 1. Fix the boundary at primitive packets

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → ...
```

The closure layer does not work directly with arbitrary triples of naturals. Its input boundary is a primitive-normalized packet.

### 2. Fix the output at `False`

```lean
CounterexamplePack x y z → False
```

For each packet it is enough to derive a contradiction.

### 3. Quantify over all packets

```lean
∀ {x y z : ℕ}, ...
```

The refuter is uniform over all primitive candidates, not tied to one particular triple.

Conceptually,

$$
\mathrm{CounterexamplePackRefuter}
\simeq
\prod_{x,y,z:\mathbb N}
\bigl(\mathrm{CounterexamplePack}(x,y,z)\to\bot\bigr).
$$

## Lean-specific details

### Why `abbrev`

The declaration uses `abbrev` rather than `def`.

An `abbrev` behaves as a lightweight reducible alias, so Lean's elaborator can readily expose its right-hand side when needed. Consequently, a later theorem can start proving the alias directly with

```lean
CounterexamplePackRefuter := by
  intro x y z p
  ...
```

without manual unfolding.

For this use case, a transparent interface alias is more natural than an opaque abstraction.

### Implicit binders

Using

```lean
∀ {x y z : ℕ}, ...
```

means callers usually do not have to write the indices explicitly. A packet carries enough type information for Lean to infer them.

This is why later code can simply write

```lean
exact hPrimitive p
```

when applying a primitive refuter.

### A `Prop`-level interface

The alias produces no computational data. The entire declaration lives in `Prop`, expressing only the proof capability "every primitive packet can be refuted."

## Redundancy and duplication

The declaration is a one-line type alias, so there is essentially no internal redundancy.

At the architecture level, however, the same pattern reappears later as

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

This repetition is better understood as intentional boundary design than as accidental duplication: each proof layer publishes a named refuter contract corresponding to its own input normalization level.

## Optimization candidates

### Keeping the current declaration is preferable

The alias could be removed and its expansion

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

written directly in every downstream theorem, but doing so would erase the semantic name of the primitive-closure target.

The current named interface is therefore better for readability and reuse.

### Generalizing to a generic refuter type

In principle one could introduce something like

```lean
abbrev Refuter (P : α → Prop) : Prop := ∀ a, P a → False
```

and encode this declaration through a generic abstraction.

That is not especially attractive here. `CounterexamplePack` is a dependent proposition indexed by three naturals, and forcing it into a generic wrapper would make the type-level presentation less direct. Moreover, preserving explicit names such as `CounterexamplePackRefuter` and `PositiveFermat5Refuter` documents the proof architecture.

No such generalization is recommended at this point.

### Comparison with negation syntax

The right-hand side could equivalently be written

```lean
∀ {x y z : ℕ}, ¬ CounterexamplePack x y z
```

because `¬ P` is definitionally `P → False`.

The current spelling

```lean
CounterexamplePack x y z → False
```

fits the downstream function-application style well, especially expressions such as `hPrimitive p`. There is little reason to change it.

## Required Mathlib imports

The canonical standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

but `CounterexamplePackRefuter` itself does not invoke any Mathlib-specific theorem or tactic. Directly, it only needs

- `ℕ`,
- `Prop`,
- `False`,
- universal quantification and function types,
- the previously defined `CounterexamplePack`.

According to the standalone manifest, the original source of `CounterexamplePack` is `DkMath/FLT/Five/Basic.lean`, so in the modular DkMath development the conceptual direct module dependency is that Basic module.

### Import optimization

There is no reason for this one-line declaration alone to require the whole `Mathlib` umbrella import.

However, because `CounterexamplePack` itself contains `Nat.Coprime` and `Fermat5Equation`, the true minimal Mathlib import should be determined at the level of compiling `Basic.lean`, not by inspecting this alias in isolation.

No Lean build is performed in this documentation task, so the exact minimal fine-grained import set is not established here. It is safe to say that the umbrella import can in principle be narrowed, but the precise minimal replacement remains unverified.

## Comparator challenge suitability

**Possible, but very weak as a standalone challenge.**

The reason is that the declaration contains no proof and is only an `abbrev`.

For example,

```lean
example : CounterexamplePackRefuter ↔
    (∀ {x y z : ℕ}, CounterexamplePack x y z → False) := by
  rfl
```

would test little beyond reducibility and elaboration.

A better Comparator challenge would pair this declaration with the next theorem and ask the prover to

1. unfold or elaborate `CounterexamplePackRefuter`,
2. split using `branchB_orientation`,
3. route the original packet or `p.swap` to the appropriate Branch-B refuter.

Thus the assessment is:

- interface/elaboration challenge: suitable,
- number-theoretic proof challenge: unsuitable,
- premise type for a closure-routing challenge: highly useful.

## Next declaration to read

The next declaration is

```lean
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

`CounterexamplePackRefuter` defines only the **target type** "all primitive packets are refutable." The next theorem actually constructs an inhabitant of that type from `SignedGoldenUnitFifthPowerExclusion`.

It is also the first closure theorem that directly consumes 0402 `CounterexamplePack.branchB_orientation`.

The flow is

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\longrightarrow
\mathrm{branchB\ orientation}
\longrightarrow
\mathrm{CounterexamplePackRefuter}.
$$

So the next declaration is the key closure step lifting the local Branch-B exclusion to a refutation of every primitive FLT5 packet.

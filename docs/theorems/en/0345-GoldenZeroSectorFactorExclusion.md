# 0345 — `GoldenZeroSectorFactorExclusion`

## Declaration kind

This declaration is an **`abbrev`**.

```lean
/-- Exclusion of every certified exact factor branch. -/
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

It is not a theorem or an ordinary `def`; it is a reducible abbreviation that assigns a short name to an existing proposition type.

## Lean type

The declaration itself has type

```lean
GoldenZeroSectorFactorExclusion : Prop
```

and unfolds to

```lean
GoldenZeroSectorFactorPacket → False
```

Thus a term

```lean
h : GoldenZeroSectorFactorExclusion
```

is a function taking any

```lean
p : GoldenZeroSectorFactorPacket
```

and returning `False`. In other words, it is evidence that no certified exact factor packet can exist.

## Mathematical meaning

`GoldenZeroSectorFactorPacket` packages a zero-sector inversion packet together with exact factor data dependent on that inversion packet. The factor data has already been classified into exactly three branches:

- the odd branch,
- the even-left-low branch,
- the even-right-low branch.

Therefore the proposition

$$
\operatorname{GoldenZeroSectorFactorPacket}\to\bot
$$

means that **none of the three certified exact factorizations can occur**.

This declaration does not yet prove exclusion of those branches. It merely names the proposition that later code must establish.

## Role in the overall proof

By 0344 `nonempty_goldenZeroSectorFactorPacket`, every raw zero-sector candidate has been shown to produce at least one exact factor packet.

Declaration 0345 introduces the logical receiver pointing in the opposite direction.

The preceding layer gives

$$
\text{raw candidate}
\longrightarrow
\operatorname{Nonempty}(\text{factor packet}),
$$

while the following layer aims to provide

$$
\text{factor packet}
\longrightarrow
\bot.
$$

Combining the two excludes the original raw candidate.

Thus this `abbrev` is the **logical interface** between the factorization-construction layer and the exclusion / closure layer.

## Direct dependencies

The only directly referenced project declaration is

- 0337 `GoldenZeroSectorFactorPacket`.

On the Lean side, the declaration uses only

- `Prop`,
- `False`,
- the function / implication type `→`.

0344 `nonempty_goldenZeroSectorFactorPacket` is an important immediately preceding result in the proof architecture, but it is not referenced directly by the body of this `abbrev`.

Likewise, 0334 `GoldenZeroSectorFactorData` and its three constructors are hidden behind `GoldenZeroSectorFactorPacket`, so 0345 does not mention them directly.

## Construction flow

There is no tactic proof in this declaration.

It simply binds the name

```lean
GoldenZeroSectorFactorExclusion
```

to the proposition

```lean
GoldenZeroSectorFactorPacket → False
```

Conceptually there is only one step:

1. assume an exact factor packet;
2. define the proposition saying that such a packet can be turned into a contradiction.

How the contradiction is actually derived is left to later theorems.

## Lean-specific processing

### Meaning of `abbrev`

In Lean, `abbrev` is a definition, but it is treated as a reducible abbreviation more aggressively than an ordinary `def`.

Hence

```lean
h : GoldenZeroSectorFactorExclusion
```

can normally be used directly as a function:

```lean
h packet
```

without inserting an explicit conversion such as

```lean
show GoldenZeroSectorFactorPacket → False from h
```

### `P → False` and negation

In Lean,

```lean
Not P
```

is definitionally

```lean
P → False
```

Therefore this contract has the same logical shape as

```lean
¬ GoldenZeroSectorFactorPacket
```

Mathematically, it is simply the negation of existence of a factor packet.

The dedicated name `GoldenZeroSectorFactorExclusion`, however, makes the architectural meaning explicit: this is the exclusion interface for the zero-sector factorization pipeline.

## Redundancy and duplication

There is essentially no code-level redundancy.

It could equivalently be written as

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  ¬ GoldenZeroSectorFactorPacket
```

because `¬ P` is `P → False`.

The current arrow form has one practical advantage: later usage as

```lean
hFactor packet
```

is visually immediate.

The dedicated abbreviation could also be omitted entirely and later theorems could take an argument of type

```lean
GoldenZeroSectorFactorPacket → False
```

directly. Naming the contract, however, clarifies the module boundary and the proof responsibility, so this is API design rather than accidental duplication.

## Optimization candidates

There is almost nothing to optimize locally.

One possible stylistic change would be

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  ¬ GoldenZeroSectorFactorPacket
```

if emphasizing negation were considered clearer.

If the subsequent code treats the contract operationally as “take a packet and produce contradiction,” the present arrow form is arguably clearer.

Another theoretical option would be to wrap exclusion evidence in a `structure` or `class`, but that would be over-engineering because the contract contains only one proposition. The current `abbrev` is minimal and natural.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` imports

```lean
import Mathlib
```

as a whole.

This declaration itself uses no Mathlib theorem or tactic. It only requires Lean core notions:

- `Prop`,
- `False`,
- implication / function types,
- `abbrev`,

plus the project declaration `GoldenZeroSectorFactorPacket`.

Therefore this declaration alone does not justify importing all of `Mathlib`.

Actual import minimization should be performed at the module level, using the dependency graph needed to provide `GoldenZeroSectorFactorPacket` and the signed golden factorization layer.

The exact minimal Mathlib import set has not been confirmed because no Lean build is being run here, so no specific module list is asserted.

## Suitability for a Comparator challenge

**Possible, but trivial in isolation.**

A bare exercise such as

```lean
abbrev Challenge : Prop :=
  GoldenZeroSectorFactorPacket → False
```

would test only understanding of `abbrev` and negation types.

A more useful Comparator challenge combines 0344 with this contract:

```lean
variable
  (hExists : Nonempty GoldenZeroSectorFactorPacket)
  (hExclude : GoldenZeroSectorFactorExclusion)

example : False := by
  -- fill here
```

The solver must extract a packet witness from `Nonempty` and apply `hExclude` to it. This directly tests whether the connection between the factorization layer and the exclusion contract is understood.

## Next declaration to read

The next declaration is

```lean
/-- The raw arithmetic contract, repeated here to preserve the acyclic dependency
 direction from inversion to factorization. -/
abbrev GoldenZeroSectorFactorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    ...
```

Its declaration kind is **`abbrev`**.

Where 0345 is the compressed exclusion contract whose input is a certified factor packet, the next declaration defines the **raw arithmetic exclusion contract** directly in terms of the original integer and natural-number data and their arithmetic hypotheses.

The Lean source then proceeds to

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

which connects these two contracts.

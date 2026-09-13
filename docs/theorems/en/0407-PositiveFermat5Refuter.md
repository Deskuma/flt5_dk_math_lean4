# 0407 `PositiveFermat5Refuter`

## Declaration kind

`abbrev`

## Lean type

```lean
/-- A primitive-packet refuter is sufficient for all positive Fermat-five data. -/
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

## Mathematical meaning

`PositiveFermat5Refuter` is not itself a theorem. It is an `abbrev` giving a name to the final refutation proposition for positive natural-number FLT5 data.

Expanded, it states

$$
\forall x,y,z\in\mathbb N,
\quad
x>0\to y>0\to z>0\to
\neg\bigl(x^5+y^5=z^5\bigr).
$$

Here `Fermat5Equation x y z` is defined by

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

so `PositiveFermat5Refuter` expresses exactly the positive-natural-number exponent-five statement

$$
x,y,z\in\mathbb N_{>0}
\Longrightarrow
x^5+y^5\ne z^5.
$$

The declaration does not yet provide a proof. It fixes, as a named interface, the type that a proof excluding all positive FLT5 solutions must inhabit.

## Role in the whole proof

The immediately preceding declaration, 0406 `exists_counterexamplePack_of_positive_fermat5`, shows that every positive solution

$$
x^5+y^5=z^5
$$

can be normalized by the gcd to a primitive packet

$$
\mathrm{CounterexamplePack}(x',y',z').
$$

Earlier closure declarations construct `CounterexamplePackRefuter`, whose content is

$$
\forall x',y',z',
\quad
\mathrm{CounterexamplePack}(x',y',z')\to\bot.
$$

`PositiveFermat5Refuter` is the **public positive-solution closure type** reached after connecting those two layers.

The next theorem makes this explicit:

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

Thus the large-scale proof architecture is

$$
\text{positive solution}
\longrightarrow
\text{primitive normalization}
\longrightarrow
\text{CounterexamplePack}
\longrightarrow
\bot.
$$

`PositiveFermat5Refuter` names the final function type of that pipeline.

There is also a later declaration in `Main.lean`,

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

with the same logical shape. Hence `PositiveFermat5Refuter` can be read as the internal closure API between `SignedGoldenClosure.lean` and the final public FLT5 target.

## Direct dependencies

### `Fermat5Equation`

This is the only DkMath-specific definition directly referenced by the abbreviation.

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

Therefore

```lean
¬ Fermat5Equation x y z
```

expands mathematically to

$$
x^5+y^5\ne z^5.
$$

### `ℕ`

The domain is the natural numbers. This is not a signed-integer theorem and not a general theorem over arbitrary rings.

### Positivity hypotheses

```lean
0 < x → 0 < y → 0 < z →
```

are stated outside `Fermat5Equation` because positivity is deliberately not built into the equation definition itself. These hypotheses exclude zero-valued trivialities and restrict the target to positive natural numbers.

### Negation

In Lean,

```lean
¬ P
```

is definitionally

```lean
P → False.
```

Consequently, an inhabitant of `PositiveFermat5Refuter` can be used as a function taking positive `x y z` and a hypothesis `hEq : Fermat5Equation x y z`, then returning `False`.

The abbreviation itself does not directly depend on 0406 `exists_counterexamplePack_of_positive_fermat5` or on `CounterexamplePackRefuter`; those are dependencies of the theorem that constructs an inhabitant of this interface.

## Construction flow

Because this is an `abbrev`, there is no proof script. The structure is entirely in the type.

### 1. Quantify over three natural numbers

```lean
∀ x y z : ℕ,
```

Unlike `CounterexamplePackRefuter`, these binders are explicit rather than implicit.

That makes the final API natural to apply as

```lean
flt5Target x y z hx hy hz
```

with the three numerical arguments given explicitly.

### 2. Require positivity

```lean
0 < x → 0 < y → 0 < z →
```

Only positive solutions at exponent five are in scope.

### 3. Refute the equation

```lean
¬ Fermat5Equation x y z
```

Thus, once

```lean
hEq : Fermat5Equation x y z
```

is supplied, the refuter must derive `False`.

As a dependent function type, the declaration can be viewed schematically as

$$
\prod_{x,y,z:\mathbb N}
\bigl(x>0\bigr)\to
\bigl(y>0\bigr)\to
\bigl(z>0\bigr)\to
\bigl(\mathrm{Fermat5Equation}(x,y,z)\to\bot\bigr).
$$

## Lean-specific details

### Reducibility of `abbrev`

The declaration uses `abbrev` rather than `def`. This makes it convenient for the elaborator to unfold the name to its function type when needed.

That is why the following theorem can begin directly with

```lean
(hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
```

without an explicit `unfold PositiveFermat5Refuter`.

For this purpose, a reducible interface alias is a natural design choice.

### `¬ P` as `P → False`

The next proof can introduce `hEq` because the final target

```lean
¬ Fermat5Equation x y z
```

is itself a function type ending in `False`.

### Explicit binders

`CounterexamplePackRefuter` uses

```lean
∀ {x y z : ℕ}, ...
```

with implicit indices, whereas this declaration uses

```lean
∀ x y z : ℕ, ...
```

with explicit arguments.

This is appropriate for a user-facing theorem API, where the values `x`, `y`, and `z` are normally supplied directly, as in `fermatFive_no_positive_solution x y z ...`.

### Curried positivity hypotheses

The positivity conditions are written as separate implications rather than bundled as

```lean
0 < x ∧ 0 < y ∧ 0 < z.
```

This supports direct applications of the form

```lean
h x y z hx hy hz
```

and matches the style of the final target theorem.

## Redundancy and overlap

The clearest duplication is with the later `FLT5Target` declaration in `Main.lean`:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

The right-hand sides of `PositiveFermat5Refuter` and `FLT5Target` are effectively identical, so as proposition types

$$
\mathrm{PositiveFermat5Refuter}
\equiv
\mathrm{FLT5Target}.
$$

This is not necessarily harmful duplication. The two names mark different module boundaries:

- `PositiveFermat5Refuter` is the internal closure boundary in `SignedGoldenClosure.lean`;
- `FLT5Target` is the final public target in `Main.lean`.

The same design pattern also appears in 0403 `CounterexamplePackRefuter`: a proof capability is first exposed as a named `Prop`, then inhabited by subsequent theorems.

## Optimization candidates

### 1. Alias `FLT5Target` to `PositiveFermat5Refuter`

To reduce textual duplication, one could write

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

later in `Main.lean`.

That would centralize the target shape in one place. The tradeoff is that the final module would no longer display the full mathematical statement locally, reducing its self-contained readability.

Given that the duplication is only a few lines, retaining both explicit declarations is also a reasonable design choice.

### 2. Bundle positivity data

A structure such as

```lean
structure PositiveTriple where
  x y z : ℕ
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
```

could package the repeated positivity hypotheses.

However, most surrounding theorems already use the curried `x y z hx hy hz` style, so bundling would likely add projections and repackaging without simplifying the closure proof.

### 3. Standardize `¬` versus `→ False`

`CounterexamplePackRefuter` is written as

```lean
CounterexamplePack x y z → False
```

whereas this declaration uses

```lean
¬ Fermat5Equation x y z.
```

These are logically identical in Lean. The current difference is useful stylistically: the former reads as an explicit refuter function, while the latter reads naturally as the mathematical statement that the equation does not hold. There is little reason to force a uniform spelling.

## Required Mathlib imports

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

for the generated development as a whole.

This declaration itself needs very little directly:

- `ℕ`;
- `<`;
- `Prop`;
- negation;
- universal quantification and function types;
- the preceding DkMath definition `Fermat5Equation`.

`Fermat5Equation` comes from `DkMath/FLT/Five/Basic.lean`, so in the modular source the conceptual direct dependency is the Basic module.

### Import optimization candidate

`import Mathlib` is certainly broader than this abbreviation alone requires.

The exact minimal Mathlib submodule set, however, must be determined together with the dependencies of `Basic.lean`. No Lean build is performed in this documentation run, so the precise minimal import list has not been verified.

What can be stated confidently is:

- the standalone artifact imports `Mathlib`;
- 0407 itself uses no advanced Mathlib theorem or tactic;
- a narrower import should be possible, but its exact minimal form is unverified here.

## Comparator challenge suitability

**Possible, but extremely weak as a standalone challenge.**

Since the declaration is only an `abbrev`, a challenge such as

```lean
example : PositiveFermat5Refuter ↔
    (∀ x y z : ℕ,
      0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z) := by
  rfl
```

mainly tests reducibility, not mathematical proof search.

A better Comparator challenge combines 0407 with the following theorem `positiveFermat5Refuter_of_counterexamplePackRefuter`. Then the solver must recognize the closure architecture:

1. assume a positive FLT5 solution;
2. invoke 0406 to obtain a primitive `CounterexamplePack`;
3. apply `CounterexamplePackRefuter` to obtain a contradiction.

Accordingly:

- definitional-equality challenge: suitable;
- substantial proof-search challenge: poor;
- interface for a normalization/closure challenge: important.

## Next declaration to read

The next declaration is

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

0407 defines only the **type** of a proof excluding positive FLT5 solutions.

The next theorem actually constructs an inhabitant of that type by composing the normalization theorem 0406 with the primitive refuter developed earlier.

Its logical route is

$$
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter},
$$

or, expanded,

$$
\text{positive FLT5 solution}
\Longrightarrow
\text{primitive packet}
\Longrightarrow
\bot.
$$

This is the final normalization-closure bridge from the primitive proof back to the unrestricted positive target.

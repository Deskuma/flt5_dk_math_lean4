# 0371 `goldenUnitClassesModFifth`

## Declaration kind

`theorem`

## Lean code

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

## Lean type

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

Here `GoldenUnitClassesModFifth` is an abbreviation for the downstream contract

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Thus, after unfolding the type, the theorem states that for every golden integer `epsilon`, if it is a unit, then

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Mathematically, every golden unit $\varepsilon$ admits a representation

$$
\varepsilon=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

## Mathematical meaning

This theorem does not strengthen the classification proved in 0370 `goldenUnitFifthClass_of_unit`.

The previous theorem gives the pointwise statement

```lean
GoldenUnit x → GoldenUnitFifthClass x
```

for an individual `x`. The present theorem packages that result as the universally quantified public contract

```lean
∀ epsilon, GoldenUnit epsilon → ...
```

required by downstream modules.

Because the exponent representative is `Fin 5`, the sector index is restricted exactly to

$$
0,1,2,3,4.
$$

There is no separate negative-sign sector because the sign can be absorbed into the fifth-power witness:

$$
(-\delta)^5=-\delta^5.
$$

Hence this declaration exposes the result that the infinite collection of golden units collapses, modulo fifth powers, to five finite sectors.

## Role in the whole proof

This theorem is the public exit point of `GoldenUnitClassification.lean`.

Up to 0370, the development constructed the classification using a coordinate measure, four measure-one terminal units, strict descent, and sector transport by multiplication with `φ` and `φ⁻¹`.

The present theorem converts the internal pointwise predicate

```lean
GoldenUnitFifthClass epsilon
```

into the downstream-facing contract

```lean
GoldenUnitClassesModFifth
```

used by later modules.

In particular, the contract is consumed by

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses
```

which reduces the arbitrary unit factor arising from a stripped packet to one of the five sectors.

It also feeds receiver theorems such as

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
flt5Target_of_unitClasses_of_zeroArithmetic
```

and thereby connects unit classification to the final FLT5 refutation chain.

Thus, if 0370 is the mathematical core of the classification, 0371 is the API boundary that exposes it to the rest of the proof architecture.

## Direct dependencies

### `GoldenUnitClassesModFifth`

The `abbrev` expressing the conclusion of the present theorem:

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

It is the global statement that every unit has a five-sector representation.

### `GoldenUnitFifthClass`

The pointwise predicate used as the conclusion of 0370:

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

For a fixed `epsilon`, its witness shape is effectively the same as the conclusion appearing inside `GoldenUnitClassesModFifth`.

### `goldenUnitFifthClass_of_unit`

The only substantial theorem dependency:

```lean
theorem goldenUnitFifthClass_of_unit
    (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x
```

All of the descent machinery is already encapsulated here. The present theorem merely applies it to an arbitrary `epsilon`.

## Proof flow

The proof has only two steps.

### 1. Introduce the contract arguments

```lean
intro epsilon hepsilon
```

After unfolding `GoldenUnitClassesModFifth`, this introduces the arbitrary golden unit `epsilon` and the proof `hepsilon : GoldenUnit epsilon`.

Mathematically this is simply: fix an arbitrary golden unit $\varepsilon$.

### 2. Apply theorem 0370 directly

```lean
exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

After unfolding `GoldenUnitFifthClass epsilon`, theorem 0370 provides exactly the current goal

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

so the proof closes immediately.

Almost all mathematical work behind this line resides in 0370.

## Lean-specific processing

### Transparency of `abbrev`

A major reason this theorem can be written so compactly is that `GoldenUnitClassesModFifth` is an `abbrev`.

Lean can transparently expose its quantified function shape, allowing

```lean
intro epsilon hepsilon
```

without an explicit `unfold` or `change`. Likewise, the witness shape of `GoldenUnitFifthClass epsilon` is definitionally compatible with the current conclusion, so `exact` succeeds without an explicit

```lean
simpa [GoldenUnitClassesModFifth, GoldenUnitFifthClass]
```

step.

### `intro`

This merely introduces the universal quantifier and implication encoded by the contract. No algebraic tactic is used.

### `exact`

As a proof term, the theorem is essentially

```lean
fun epsilon hepsilon =>
  goldenUnitFifthClass_of_unit epsilon hepsilon
```

The proof is therefore about reusing an existing theorem with a compatible type rather than performing any new arithmetic.

## Redundancy and duplication

There is essentially no redundancy in the proof body itself.

```lean
by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

is already close to minimal.

At the type-design level, however, `GoldenUnitFifthClass` and `GoldenUnitClassesModFifth` repeat the same existential witness shape.

This duplication appears intentional. The former is a local predicate about one unit `x`; the latter is a global downstream contract asserting that every unit is classifiable. Keeping the two concepts separate makes the architectural boundary explicit.

## Optimization candidates

### 1. Reduce the theorem to term style

It may be possible to write

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth :=
  goldenUnitFifthClass_of_unit
```

if elaboration unfolds the relevant definitions exactly as expected.

This has not been checked by a Lean build in this task, so it remains a candidate rather than a confirmed simplification. The existing `intro` plus `exact` version is clearer about the intended type transition.

### 2. Define the contract through the pointwise predicate

One could instead define

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon → GoldenUnitFifthClass epsilon
```

which would remove duplication of the existential witness shape.

The current definition, however, has the advantage that the downstream contract can be read independently without following another definition. This is therefore an API-design choice, not an identified defect.

### 3. Clarify public API intent

Because `goldenUnitFifthClass_of_unit` and `goldenUnitClassesModFifth` are semantically very close, keeping their documentation explicit about the former being the implementation theorem and the latter being the receiver-facing contract improves discoverability.

## Required Mathlib imports and import optimization candidates

The standalone source uses

```lean
import Mathlib
```

For this theorem body itself, the required ingredients are almost entirely declarations from the same development:

- `GoldenInt`
- `GoldenUnit`
- `GoldenUnitFifthClass`
- `GoldenUnitClassesModFifth`
- `goldenUnitFifthClass_of_unit`

The body uses only `intro` and `exact`; it invokes no advanced Mathlib tactic directly.

`Fin 5`, natural numbers, and basic logic are required by the definitions underneath the contract, but this wrapper theorem adds no substantial import burden of its own.

Therefore `import Mathlib` is almost certainly broader than necessary for this declaration in isolation. The exact minimal import set has not been verified because no Lean build is performed in this task.

## Comparator challenge suitability

**Suitable, but only as a very small micro challenge when isolated.**

A challenge can provide

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop := ...
abbrev GoldenUnitClassesModFifth : Prop := ...

theorem goldenUnitFifthClass_of_unit
    (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := ...
```

and ask for

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  ...
```

The interesting Lean skills are transparency of `abbrev`, introduction of a quantified contract, theorem reuse, and recognition of a definitionally compatible goal.

For a more meaningful Comparator challenge, 0370 and 0371 should be paired: prove the strong-induction classification and then expose it as the public contract.

## Technical significance

The importance of this theorem is architectural rather than proportional to its code length.

It compresses the large descent proof completed in 0370 into one named assumption

```lean
GoldenUnitClassesModFifth
```

that downstream modules can depend on without knowing how the classification was established.

In other words, this theorem realizes the abstraction boundary

$$
\text{unit descent implementation}
\longrightarrow
\text{five-sector public contract}.
$$

After this boundary, zero-sector arithmetic and packet refutation can depend only on the fact that units fall into five classes, not on the internal coordinate-descent mechanism that proved it.

## Next declaration to read

This theorem closes `GoldenUnitClassification.lean` in the repository source. The next step in dependency order is therefore to enter the following module, `SignedGoldenZeroSectorDescent.lean`, and select its first declaration that has not yet been documented.

The exact next declaration and its sequence number should be determined again from the repository source at the beginning of the next run rather than assumed from conversation history.

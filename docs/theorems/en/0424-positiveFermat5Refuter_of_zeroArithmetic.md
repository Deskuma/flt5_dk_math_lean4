# 0424 `positiveFermat5Refuter_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
/-- The zero-sector arithmetic proposition refutes every positive solution. -/
theorem positiveFermat5Refuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## Mathematical statement and meaning

0424 states that once the zero-sector arithmetic exclusion proposition

```lean
GoldenZeroSectorArithmeticExclusion
```

is available, every positive-natural-number candidate for an FLT5 solution can be refuted.

The conclusion `PositiveFermat5Refuter` is defined by

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

so the mathematical content of 0424 is

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\forall x,y,z\in\mathbb N,
\quad x>0\to y>0\to z>0\to
x^5+y^5\ne z^5.
$$

However, 0424 itself does not redo the Diophantine analysis of the zero sector or the primitive reduction. It simply applies the more general receiver

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

to the already proved unit-classification theorem

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

thereby discharging the unit-classification assumption.

In this sense, 0424 specializes

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{PositiveFermat5Refuter}
$$

to the public receiver

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{PositiveFermat5Refuter}.
$$

## Role in the full proof

0424 is the last facade theorem in `Main` exposing the internal closure API of the FLT5 proof architecture.

Conceptually, the proof flows as

$$
\text{positive solution}
\Longrightarrow
\text{primitive packet}
\Longrightarrow
\text{signed gap orientation}
\Longrightarrow
\text{golden unit} \times \text{fifth power}
\Longrightarrow
\text{five unit sectors}
\Longrightarrow
\text{sector exclusions}
\Longrightarrow
\text{zero-sector arithmetic}
\Longrightarrow
\bot.
$$

Inside `SignedGoldenClosure.lean`, the development first constructs a

```lean
CounterexamplePackRefuter
```

for primitive packets, then lifts that refuter through gcd normalization to arbitrary positive solutions, producing

```lean
PositiveFermat5Refuter.
```

0424 reduces the assumptions required at the public entry point of that positive-solution closure to the single zero-sector arithmetic proposition.

`Main` already contains 0419

```lean
flt5Target_of_zeroArithmetic
```

which also takes `GoldenZeroSectorArithmeticExclusion` and returns `FLT5Target`. Therefore, if one only looks at proposition shape, 0419 and 0424 expose almost the same boundary.

Their API roles differ:

- `FLT5Target` is the final public statement.
- `PositiveFermat5Refuter` represents the internal closure architecture.
- 0419 is the receiver on the public-target side.
- 0424 is the receiver on the internal-refuter side.

This duplication gives stable entry points both to users of the final theorem and to readers who want to audit or reuse the proof architecture.

## Direct dependencies

### `GoldenZeroSectorArithmeticExclusion`

This is the final arithmetic contract for the zero sector.

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

It is the only external assumption accepted by 0424.

### `PositiveFermat5Refuter`

This proposition refutes all positive-natural-number candidates for FLT5.

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

The conclusion of 0424 is exactly this proposition.

### `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

This is the general receiver called directly by 0424.

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

The actual composition is therefore

$$
\text{unit classes} + \text{zero arithmetic}
\Longrightarrow
\text{primitive refuter}
\Longrightarrow
\text{positive refuter}.
$$

### `goldenUnitClassesModFifth`

This is the unconditional provider of the unit classification.

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

0424 passes this proof object as the first argument and thereby removes the `GoldenUnitClassesModFifth` assumption.

## Proof / construction flow

The proof term of 0424 is only

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

### 1. Obtain the general receiver

The existing theorem has type

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
PositiveFermat5Refuter
```

### 2. Supply the unit classification

The unconditional theorem

```lean
goldenUnitClassesModFifth
```

is supplied as the first argument.

Lean can therefore partially apply the receiver, conceptually leaving

```lean
GoldenZeroSectorArithmeticExclusion → PositiveFermat5Refuter
```

### 3. Supply the zero-sector arithmetic assumption

Passing `hArithmetic` as the second argument yields a proof object of

```lean
PositiveFermat5Refuter.
```

There are no local uses of `intro`, `rw`, `ring`, `omega`, case analysis, gcd calculations, or descent in 0424 itself. All of that arithmetic has already been discharged by its dependencies.

## Lean-specific processing

### Curry–Howard composition of proof objects

0424 applies a theorem exactly like an ordinary curried function:

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

A proof term of type

```lean
A → B → C
```

is given a proof of `A` and a proof of `B`, producing a proof of `C`.

### Transparency of `abbrev`

`PositiveFermat5Refuter` is an `abbrev : Prop`, so Lean may unfold it definitionally to

```lean
∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

when needed.

Likewise, `FLT5Target` in `Main` is an `abbrev` with the same proposition shape. This definitional transparency is what makes the closure layer and the public-target layer connect through very thin wrappers.

### Tactic-free term-style proof

0424 places a complete proof term directly on the right-hand side of `:=`; it never opens a tactic state. This reflects the fact that the dependency structure has already isolated and solved every mathematical subproblem below this facade.

## Redundancy and duplication

0424 proves no new arithmetic fact.

In particular, 0419

```lean
flt5Target_of_zeroArithmetic
```

and 0424 both accept `GoldenZeroSectorArithmeticExclusion` and return the negation of positive-natural-number FLT5 solutions. Moreover, `FLT5Target` and `PositiveFermat5Refuter` have the same underlying proposition shape.

Thus, if minimizing code size were the only goal, 0424 could be removed and callers could invoke the general receiver directly.

The duplication is nevertheless naturally interpreted as an intentional facade. Keeping 0424 lets clients use the closure boundary

```lean
GoldenZeroSectorArithmeticExclusion → PositiveFermat5Refuter
```

without knowing the implementation details of unit classification.

## Optimization candidates

### 1. Make the alias relation between 0419 and 0424 explicit

Because `FLT5Target` and `PositiveFermat5Refuter` have the same proposition shape, a future API cleanup could define one in terms of the other.

Conceptually, one could write something like

```lean
abbrev FLT5Target := PositiveFermat5Refuter
```

which would make their relationship even more explicit. This is only a design candidate: public API stability and module dependency direction may justify retaining the current two names.

### 2. Keep or remove the facade theorem

0424 is a one-line wrapper and is removable from a code-minimization perspective. As a named architectural boundary, however, it improves readability, auditability, and reuse. Given the role of `Main`, retaining it is reasonable.

### 3. The proof term is already essentially minimal

The body

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

has almost no meaningful syntactic or logical compression left.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

0424 itself invokes no Mathlib tactic or theorem directly. Its immediate dependencies are project-level declarations:

- `GoldenZeroSectorArithmeticExclusion`
- `PositiveFermat5Refuter`
- `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`
- `goldenUnitClassesModFifth`

Therefore, in modular source form, the direct imports needed by 0424 should be limited to project modules exposing the closure theorem and the unit-classification provider.

The repository's standalone artifact concatenates the module graph into one generated file and centralizes external dependencies behind `import Mathlib`. No Lean build was run in this documentation pass, so the exact minimal decomposition of `Mathlib` into narrower imports has not been verified and should not be asserted.

## Comparator challenge suitability

0424 by itself is **too easy** to make a useful Comparator challenge.

If the inputs are

```lean
hGeneral : GoldenUnitClassesModFifth →
  GoldenZeroSectorArithmeticExclusion →
  PositiveFermat5Refuter
hClasses : GoldenUnitClassesModFifth
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

then the solution is just

```lean
exact hGeneral hClasses hArithmetic
```

so the isolated theorem measures almost no substantial Lean reasoning.

A meaningful challenge would hide the packaged dependency and require reconstruction of the composition behind 0424:

1. build `CounterexamplePackRefuter` from unit classification and zero-sector arithmetic;
2. normalize an arbitrary positive solution to a primitive packet;
3. lift the primitive refuter to `PositiveFermat5Refuter`.

That version would test understanding of the proof architecture and would make a medium-or-harder Comparator challenge.

## Next declaration to read

**None.**

`positiveFermat5Refuter_of_zeroArithmetic` is the final declaration in the generated `DkMath/FLT/Five/Main.lean` section of the canonical standalone source `Flt5DkMath/FLT5StandAlone.lean`. It is immediately followed by

```lean
end DkMath.FLT.Five

/-! ===== END GENERATED SOURCE: DkMath/FLT/Five/Main.lean ===== -/
```

Therefore 0424 is the **final declaration** in the FLT5 standalone source followed by this theorem museum in dependency order.

The unconditional mathematical endpoint had already been reached at 0420 `flt5Target` and exposed in ordinary-argument form at 0421 `fermatFive_no_positive_solution`. Declarations 0422–0424 are the final `Main` facades exposing important internal endpoints of the proof architecture, and 0424 closes that sequence.

# 0417 `FLT5Target`

## Declaration kind

`abbrev`

## Lean type

```lean
/-- No positive natural numbers satisfy `x^5 + y^5 = z^5`. -/
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

## Mathematical statement and meaning of the declaration

`FLT5Target` is not a theorem. It is an `abbrev` that gives a name to the final proposition asserting that the exponent-five Fermat equation has no positive natural-number solution.

Since `Fermat5Equation` is defined by

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

expanding `FLT5Target` gives

$$
\forall x,y,z\in\mathbb N,
\quad
x>0\to y>0\to z>0\to
x^5+y^5\ne z^5.
$$

Equivalently, in ordinary mathematical notation,

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5.
$$

Thus this proposition is exactly the positive-natural-number Fermat statement at exponent five.

The declaration itself does not prove that proposition. `abbrev FLT5Target : Prop := ...` merely names the proposition that the development is intended to prove. An inhabitant of that proposition is supplied later by the theorem `flt5Target`.

The scope is deliberately narrow: positive natural numbers and exponent five. It is not a general-exponent FLT statement, not a theorem over arbitrary signed integers, and not a statement over a general ring.

## Role in the whole proof

`FLT5Target` is the entry point of the public endpoint layer in `Main.lean`.

Immediately before this layer, the closure development uses the internal proposition

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

which has exactly the same logical shape. Declaration 0417 presents that shape again under the public final-target name `FLT5Target`.

The following declarations then form the final pipeline.

First,

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

constructs the target conditionally from unit-class classification and zero-sector arithmetic exclusion.

Next,

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

fills in the already-proved unit classification.

Finally,

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

supplies the proved zero-sector exclusion as well.

So the terminal proof architecture can be read as

$$
\text{golden unit classification}
+
\text{zero-sector exclusion}
\Longrightarrow
\text{PositiveFermat5Refuter}
\Longrightarrow
\text{FLT5Target}.
$$

Declaration 0417 is therefore the **public target interface** at the end of the proof.

## Direct dependencies

### `Fermat5Equation`

The only DkMath-specific definition directly referenced in the declaration is `Fermat5Equation`:

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

Hence

```lean
¬ Fermat5Equation x y z
```

expands to

$$
x^5+y^5\ne z^5.
$$

### Positivity hypotheses

The conditions

```lean
0 < x →
0 < y →
0 < z →
```

are placed in the target rather than inside `Fermat5Equation`.

This keeps `Fermat5Equation` as a reusable bare equation while the final FLT5 statement excludes zero explicitly.

### `PositiveFermat5Refuter`

The text of 0417 does not directly mention `PositiveFermat5Refuter`. Nevertheless, the proposition on the right-hand side is the same proposition, which is why the theorem immediately following 0417 can return an existing `PositiveFermat5Refuter` directly as a proof of `FLT5Target`.

This is a module-boundary bridge that relies on transparency of the two `abbrev` declarations.

## Construction flow

Because this is an `abbrev`, there is no proof script. The type can be read in three steps.

### 1. Quantify over three natural numbers

```lean
∀ x y z : ℕ,
```

The binders are explicit, as expected for the final public API.

### 2. Assume positivity

```lean
0 < x → 0 < y → 0 < z →
```

This restricts the scope to $\mathbb N_{>0}$.

### 3. Refute the Fermat equation

```lean
¬ Fermat5Equation x y z
```

In Lean, `¬ P` is definitionally `P → False`, so the expanded target is effectively

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z →
  Fermat5Equation x y z → False
```

which matches the functional shape of the whole proof: accept a positive candidate solution, normalize it to primitive data, pass through the golden-order factorization and unit-class analysis, close the zero sector, and return a contradiction.

## Lean-specific processing

### Reducibility of `abbrev`

`FLT5Target` is an `abbrev`, not an opaque `def`. Lean can therefore unfold it readily during type checking.

This is why the next theorem can simply write

```lean
: FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

without an explicit `change`, `unfold FLT5Target`, or `simpa [FLT5Target, PositiveFermat5Refuter]`.

The result type of the closure theorem and the public target are definitionally compatible.

### Negation as a function type

Lean defines

```lean
¬ P
```

as

```lean
P → False
```

so a proof of `flt5Target` can ultimately be applied as

```lean
flt5Target x y z hx hy hz hEq
```

to obtain `False` from a hypothetical Fermat equation.

The later wrapper

```lean
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz
```

uses this curried shape directly.

### Separating a proposition alias from its proof object

Lean allows

```lean
abbrev FLT5Target : Prop := ...
```

and

```lean
theorem flt5Target : FLT5Target := ...
```

to be separate declarations.

The former is the specification; the latter is a proof object inhabiting that specification. This separation also lets all conditional receivers expose exactly the same target type.

## Redundancy and duplication

The clearest duplication is with 0407 `PositiveFermat5Refuter`, whose right-hand side is the same proposition.

Logically,

$$
\mathrm{PositiveFermat5Refuter}
\equiv
\mathrm{FLT5Target}.
$$

From a code-size perspective this is duplicate structure, but the names serve different architectural roles:

- `PositiveFermat5Refuter` is the internal closure interface of `SignedGoldenClosure.lean`;
- `FLT5Target` is the final public statement exposed by `Main.lean`.

Thus the duplication can be understood as intentional naming at two module boundaries.

There is also mathematical overlap between `FLT5Target` and the later `fermatFive_no_positive_solution`. The former is a proposition alias; the latter is an ordinary theorem wrapper convenient for direct application. This is another API-level duplication rather than a duplicate proof.

## Optimization candidates

### 1. Alias `FLT5Target` to `PositiveFermat5Refuter`

The most direct reduction in duplication would be

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

which would centralize the proposition shape in one place.

The trade-off is that a reader opening only `Main.lean` would no longer see the final equation

$$
x^5+y^5\ne z^5
$$

spelled out locally. For a public endpoint, the current self-contained definition has clear readability value.

### 2. Introduce a common lower-level alias

One could instead place a common alias such as `PositiveFermat5EquationRefuter` in the basic layer and let both closure and main modules refer to it.

That would reduce textual duplication, but it would also introduce another abstraction layer. At this scale, the extra indirection may cost more readability than it saves.

### 3. Merge the target alias with the ordinary wrapper

Another possible design is to define only

```lean
theorem flt5Target
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z := ...
```

However, keeping `FLT5Target` as a separate proposition is useful because every conditional receiver can share exactly the same result type. The present arrangement exposes the proof pipeline more clearly.

## Required Mathlib import

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

but declaration 0417 itself depends only on very basic Lean / Mathlib material:

- `ℕ`;
- `<`;
- `Prop`;
- `¬`;
- universal quantification and implication;
- the earlier definition `Fermat5Equation`.

No advanced algebra, number theory, valuation machinery, or tactics are used by this declaration itself.

At the split-module level, the essential dependency is the Basic layer that provides `Fermat5Equation`.

### Import optimization candidate

There is no reason for this `abbrev` alone to require all of `import Mathlib`.

However, the exact smallest Mathlib module after accounting for the import closure of the Basic layer has not been checked here, because this run does not perform a Lean build. Therefore a concrete minimal-import replacement is unverified.

What can be stated safely is that 0417 itself requires no tactic-specific or valuation-specific import; its substantive dependency is the provider of `Fermat5Equation`.

## Comparator challenge suitability

**It can be made into a standalone challenge, but the difficulty is extremely low.**

Because `FLT5Target` is only a proposition alias, a challenge such as

```lean
example : FLT5Target ↔
    (∀ x y z : ℕ,
      0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z) := by
  rfl
```

is almost entirely a check of definitional equality.

A more useful Comparator challenge would combine 0417 with 0418 and ask the solver to construct `FLT5Target` from

```lean
(hClasses : GoldenUnitClassesModFifth)
(hArithmetic : GoldenZeroSectorArithmeticExclusion)
```

because that requires recognizing the connection between the internal closure theorem and the public target.

For greater difficulty, the challenge could cover the whole final composition from the conditional receivers to the unconditional `flt5Target`.

## Next declaration to read

The next declaration is 0418:

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

Declaration 0417 defines the **type** of the final target; 0418 is its first **inhabitant constructor**.

It establishes the Main-layer conditional endpoint

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

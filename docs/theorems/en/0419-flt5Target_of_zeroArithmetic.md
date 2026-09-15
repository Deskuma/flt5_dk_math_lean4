# 0419 `flt5Target_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
/-- Conditional receiver after the proved unit classification is supplied. -/
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## Mathematical statement and meaning of the declaration

This theorem states that the public exponent-five Fermat target follows from only one remaining assumption: the arithmetic contract excluding the Diophantine candidates left in the zero sector,

```lean
GoldenZeroSectorArithmeticExclusion.
```

Its type can be read schematically as

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}.
$$

Expanding declaration 0417 `FLT5Target`, the conclusion is

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5.
$$

The preceding declaration 0418,

```lean
flt5Target_of_unitClasses_of_zeroArithmetic,
```

had the two-input shape

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}.
$$

Declaration 0419 removes the first external assumption by supplying the already-proved theorem

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

as the first argument.

Thus 0419 performs no new number-theoretic calculation or case analysis. It is a specialization theorem recording in the Main layer that the modulo-fifth-power classification of golden units is no longer an unresolved input.

## Role in the whole proof

The final Main-layer closure discharges assumptions one by one.

Declaration 0418 exposes

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

Declaration 0419 fills the unit-class input with the proved provider

```lean
goldenUnitClassesModFifth,
```

so the only remaining boundary is

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

The next declaration, 0420 `flt5Target`, then supplies the unconditional theorem

```lean
goldenZeroSectorArithmeticExclusion : GoldenZeroSectorArithmeticExclusion
```

already established at 0412, thereby closing the final target without assumptions.

The last three Main-layer stages can therefore be read as the dependency-discharge chain

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
+\mathrm{GoldenZeroSectorArithmeticExclusion}
\to \mathrm{FLT5Target},\\
&\mathrm{GoldenZeroSectorArithmeticExclusion}
\to \mathrm{FLT5Target},\\
&\mathrm{FLT5Target}.
\end{aligned}
$$

Declaration 0419 is the middle step, eliminating the conditional boundary corresponding to unit classification.

## Direct dependencies

### `flt5Target_of_unitClasses_of_zeroArithmetic`

This is the conditional Main-layer receiver explained in declaration 0418:

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

It is the theorem directly invoked by 0419.

### `goldenUnitClassesModFifth`

This theorem supplies the golden-unit classification unconditionally:

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

Because this theorem already inhabits `GoldenUnitClassesModFifth`, the first argument of 0418 no longer needs to remain an external hypothesis.

Mathematically, it is the provider certifying that every golden unit belongs, modulo fifth powers, to one of the five representative classes.

### `GoldenZeroSectorArithmeticExclusion`

This is the sole assumption retained by 0419.

It is the arithmetic contract excluding the integral-parameter Diophantine configurations produced in the zero sector. Declaration 0419 does not inspect its internal structure; it forwards the completed proposition `hArithmetic` directly to declaration 0418.

### `FLT5Target`

The public target introduced in declaration 0417:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

This is the conclusion type of 0419.

## Proof or construction flow

The proof consists of one theorem application:

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

### 1. Receive zero-sector arithmetic

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

This is the only external input required by 0419.

### 2. Fix the unit classification to the proved theorem

```lean
goldenUnitClassesModFifth
```

has type

```lean
GoldenUnitClassesModFifth,
```

so it can be passed directly as the first argument of 0418.

### 3. Specialize declaration 0418

Applying

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

fills both arguments of 0418 and returns

```lean
FLT5Target.
```

No rewriting, case split, or arithmetic tactic is required.

## Lean-specific processing

### Passing a theorem as a value

In Lean, a theorem of a proposition is a proof term inhabiting that proposition.

Therefore

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

can be passed directly as the concrete value required by the parameter

```lean
hClasses : GoldenUnitClassesModFifth.
```

This is a particularly transparent instance of the Curry–Howard correspondence in the source code.

### Partial specialization

Declaration 0418 is a curried theorem of the form

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
FLT5Target.
```

Declaration 0419 specializes the first argument to `goldenUnitClassesModFifth`.

Conceptually it is equivalent to

```lean
fun hArithmetic =>
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

but the explicit parameter `hArithmetic` means no lambda expression needs to be written.

### Term proof rather than a tactic block

The declaration is written as

```lean
:=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

rather than with a `by` block.

That concise term accurately reflects the architecture: no new proof search is happening; an already-proved dependency is simply being supplied to an existing receiver theorem.

## Redundancy and duplication

Mathematically, 0419 is only a specialization of 0418 and introduces no new number-theoretic lemma.

If minimizing source size were the sole goal, declaration 0420 `flt5Target` could directly write

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

and declaration 0419 could be omitted.

Keeping 0419, however, makes an important proof boundary explicit:

- unit classification is fully solved;
- only zero-sector arithmetic remains as a replaceable receiver input;
- the final endpoint merely injects the unconditional provider for that input.

This separation is useful for dependency auditing and for substituting an alternative proof route in the future.

Declarations 0418, 0419, and 0420 form a sequence of thin wrappers, but the duplication is architectural rather than accidental: each named theorem records one more discharged conditional assumption.

## Optimization candidates

### 1. Remove 0419 and inject both providers directly in 0420

This is possible if shortest source code is the only objective:

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

would construct the final target in one step.

The trade-off is losing the useful intermediate API

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}.
$$

That would reduce auditability and reuse.

### 2. Bypass `flt5Target_of_unitClasses_of_zeroArithmetic`

Declaration 0419 could theoretically return

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

directly.

That would make the Main layer depend directly on the internal closure-layer API, however. The current route through 0418 keeps the module boundary clearer.

### 3. Generalize provider injection

The pattern “fix one argument of a conditional theorem to an already-proved provider” could be abstracted into a generic combinator. For a one-line specialization of this size, such an abstraction would likely cost more readability than it saves.

The current explicit application is appropriate.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

but the body of 0419 itself only performs theorem application. It does not directly invoke Mathlib arithmetic tactics, ring APIs, valuation machinery, or other specialized facilities.

Its substantive dependencies are the DkMath declarations providing

- `FLT5Target`;
- `GoldenZeroSectorArithmeticExclusion`;
- `goldenUnitClassesModFifth`;
- `flt5Target_of_unitClasses_of_zeroArithmetic`.

In the standalone ordered source manifest, unit classification corresponds to `GoldenUnitClassification.lean`, zero-sector finalization to `SignedGoldenZeroSectorFinal.lean`, and the public receiver to `Main.lean`.

### Import optimization candidate

There is little reason for declaration 0419 alone to require all of `import Mathlib`. In split-source form, the imports supplying the DkMath declarations above should likely be sufficient.

However, this run does not perform a Lean build, and the exact minimal Mathlib import closure was not experimentally verified. Therefore no specific minimal replacement module is asserted.

## Comparator challenge suitability

 **Suitable, with low difficulty.**

A basic challenge can be stated as

```lean
theorem challenge
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target := by
  ?_
```

with

```lean
goldenUnitClassesModFifth
flt5Target_of_unitClasses_of_zeroArithmetic
```

available. This tests whether the solver recognizes that the unresolved first input can be filled by an already-proved provider and that the resulting theorem specializes to the desired target.

For a harder version, declaration 0418 could be hidden and the solver asked to work directly from

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic.
```

That would additionally require understanding the definitional equality between `PositiveFermat5Refuter` and `FLT5Target`.

Combined with declaration 0420, the task becomes a compact dependency-resolution challenge in which two conditional inputs are discharged sequentially by proved providers.

## Next declaration to read

The next declaration is 0420 `flt5Target`, of kind `theorem`:

```lean
/--
The unconditional exponent-five target for positive natural numbers. It denies
`Fermat5Equation x y z`, namely `x^5 + y^5 = z^5`, for every positive
`x`, `y`, and `z`. This is not a general-exponent or signed-integer theorem.
-/
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

Declaration 0419 establishes

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}.
$$

Declaration 0420 then supplies the already-proved unconditional provider

```lean
goldenZeroSectorArithmeticExclusion
```

and obtains

$$
\mathrm{FLT5Target}
$$

with no assumptions.

Thus 0420 closes the conditional receiver chain and becomes the public unconditional endpoint before the ordinary-argument wrapper that follows.
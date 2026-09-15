# 0409 `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

This theorem takes the golden-integer unit-class classification

```lean
hClasses : GoldenUnitClassesModFifth
```

and the zero-sector arithmetic exclusion

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

and returns a refuter of every positive-natural-number FLT5 counterexample:

```lean
PositiveFermat5Refuter
```

Expanding 0407 `PositiveFermat5Refuter`, the conclusion is

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

## Mathematical statement

Mathematically, this is a closure theorem saying that two local inputs suffice to exclude every positive-integer solution of the exponent-five Fermat equation:

1. the units appearing in the golden-integer fifth-power decomposition are classified into the required finite set of unit classes;
2. the remaining zero sector is arithmetically impossible.

From these inputs, every primitive counterexample is refuted; primitive reduction then excludes every positive solution.

The logical route is

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter}.
$$

Ultimately, for arbitrary $x,y,z\in\mathbb N$, if

$$
0<x,\qquad 0<y,\qquad 0<z,
$$

then

$$
x^5+y^5\ne z^5.
$$

The theorem itself does not reprove the unit-class classification or the infinite descent in the zero sector. Those arguments are already hidden behind earlier theorems; 0409 only connects the two proved layers to the full positive target.

## Role in the overall proof

0409 is a high-level receiver theorem at the end of `SignedGoldenClosure`.

The preceding proof architecture can be divided into three stages.

1. On the golden-integer and unit-fifth-power side, the unit classes and the zero-sector exclusion are used to rule out primitive packets.
2. 0405 `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` packages that result as `CounterexamplePackRefuter`.
3. 0408 `positiveFermat5Refuter_of_counterexamplePackRefuter` lifts a primitive refuter to a refuter of arbitrary positive-natural-number solutions.

0409 composes stages 2 and 3 in a single theorem application.

Thus, in the architecture of the proof it exposes the dependency boundary

$$
\text{golden arithmetic boundary}
\Longrightarrow
\text{primitive FLT5 closure}
\Longrightarrow
\text{positive FLT5 closure}.
$$

The important point is that the conclusion is already `PositiveFermat5Refuter`. Consequently, the later `Main.lean` layer can connect this receiver to the public FLT5 target without knowing the internal details of the golden-integer argument.

## Direct dependencies

### `GoldenUnitClassesModFifth`

This is the type of `hClasses`.

It is the receiver proposition expressing the finite classification of golden units modulo fifth powers.

0409 does not unfold its internal structure; it passes the value directly to 0405.

### `GoldenZeroSectorArithmeticExclusion`

This is the type of `hArithmetic`.

It is the public receiver proposition asserting that the arithmetic conditions arising in the zero sector lead to contradiction.

Again, 0409 does not unpack the proposition and simply passes it to 0405.

### `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

This is theorem 0405.

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter
```

It constructs a refuter of every primitive `CounterexamplePack` from the two golden-side inputs.

The inner application in 0409,

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

is exactly this stage.

### `positiveFermat5Refuter_of_counterexamplePackRefuter`

This is theorem 0408.

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) :
    PositiveFermat5Refuter
```

It lifts a refuter of primitive packets to a refuter of arbitrary positive-natural-number FLT5 solutions.

The outer application in 0409 is this stage.

### `PositiveFermat5Refuter`

This is the `abbrev` from 0407.

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

It is the conclusion type of 0409.

## Proof flow

The proof term of 0409 consists of one nested function application.

### 1. Build the primitive refuter from unit classification and zero-sector arithmetic

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

This expression has type

```lean
CounterexamplePackRefuter
```

so at this stage every primitive `CounterexamplePack` can be sent to `False`.

### 2. Lift the primitive refuter to the positive refuter

The resulting value is passed to 0408:

```lean
positiveFermat5Refuter_of_counterexamplePackRefuter
  (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    hClasses hArithmetic)
```

If a positive solution existed, 0408 would use the gcd normalization from 0406 to convert it into a primitive packet and then contradict the primitive refuter.

Therefore the entire expression has type

```lean
PositiveFermat5Refuter
```

which is exactly the goal of 0409.

## Lean-specific processing

### Tactic-free term-style proof

0409 is a pure term proof:

```lean
:=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (...)
```

No `by`, `intro`, `exact`, or rewriting tactic is needed. Lean only checks that the result type of the inner theorem application matches the input type of the outer theorem and that the final result type matches the goal.

### Type-directed dependency routing

The inner result is

```lean
CounterexamplePackRefuter
```

and the outer theorem requires precisely

```lean
CounterexamplePackRefuter
```

as its argument. The proof is therefore ordinary function composition both mathematically and at the Lean type level.

Conceptually its shape is

```lean
A → B → C
C → D
----------------
A → B → D
```

### Transparency of `abbrev`

The final type `PositiveFermat5Refuter` and the intermediate type `CounterexamplePackRefuter` are both defined with `abbrev`.

0409 does not need to `unfold` either one. Lean treats these abbreviations as reducible and can unfold them when necessary for definitional type checking.

### No explicit concrete-number arguments

No concrete `x y z` appear in 0409.

They are hidden inside the binders of `PositiveFermat5Refuter` and `CounterexamplePackRefuter`. This theorem connects proposition-level interfaces rather than manipulating individual number-theoretic data, which keeps the proof term extremely small.

## Redundancy and duplication

There is essentially no computational duplication in the body of 0409.

One could formally avoid 0405 and 0408 by expanding their proofs into a single large theorem. That would, however, destroy the separation between

- primitive closure,
- positive normalization, and
- the golden arithmetic boundary,

so it would be a clear architectural regression.

Because 0409 is only a composition of two existing theorems, it may look like a redundant wrapper if judged purely by line count. Nevertheless, the named theorem presents exactly two external assumptions,

```lean
GoldenUnitClassesModFifth
GoldenZeroSectorArithmeticExclusion
```

and directly returns `PositiveFermat5Refuter`. This is a useful API boundary because later `Main.lean` code need not mention the primitive layer at all.

## Optimization candidates

### 1. Keep the present term proof

The implementation is already essentially minimal:

```lean
positiveFermat5Refuter_of_counterexamplePackRefuter
  (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

Further shortening would not improve readability or dependency structure. Therefore **keeping the current form is the most natural choice**.

### 2. An explanatory form with an intermediate `have`

For teaching purposes one could write

```lean
by
  have hPrimitive : CounterexamplePackRefuter :=
    counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
  exact positiveFermat5Refuter_of_counterexamplePackRefuter hPrimitive
```

This makes the two dependency stages visually explicit.

For production code, however, the existing term-style proof is more concise. This is a readability tradeoff rather than a genuine optimization.

### 3. No need for a generic composition helper

Abstractly the theorem is just function composition, so a generic helper could be introduced. Lean's ordinary function application already performs that job.

Adding another abstraction would hide the FLT5-specific dependency names and make the route harder to audit.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The proof body of 0409 does not directly invoke an individual Mathlib number-theory theorem or tactic. It only applies previously defined FLT5 propositions and theorems.

Conceptually, its direct requirements are a module context exposing

- `GoldenUnitClassesModFifth`,
- `GoldenZeroSectorArithmeticExclusion`,
- `CounterexamplePackRefuter`,
- `PositiveFermat5Refuter`,
- `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`, and
- `positiveFermat5Refuter_of_counterexamplePackRefuter`.

### Import optimization candidate

For this theorem alone, `import Mathlib` is much broader than the proof term itself needs, since the body calls no arithmetic Mathlib API directly.

In the split source layout, importing the internal module that exposes the preceding declarations is likely sufficient.

No Lean build is performed in this documentation task, so the exact minimal module set has not been verified. Accordingly, a specific minimal import list should not be asserted as established fact.

## Comparator challenge suitability

**Suitable, but low difficulty.**

0409 is not a substantial arithmetic challenge. It is useful as a small type-directed theorem-composition challenge.

For example, one could provide the context

```lean
axiom counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter

axiom positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) :
    PositiveFermat5Refuter
```

and ask for the proof hole of 0409 to be filled.

The evaluation targets are

- reading theorem input and output types,
- recognizing `CounterexamplePackRefuter` as the intermediate type,
- composing theorems by nested application, and
- treating `abbrev` declarations as interfaces without manually expanding them.

If the dependency theorem names are supplied exactly, the challenge is very easy. It becomes more meaningful for Comparator if a larger candidate theorem set is provided and dependency selection must also be inferred.

## Next declaration to read

The next declaration is at the beginning of `SignedGoldenZeroSectorFinal.lean`:

```lean
theorem goldenZeroSectorFactorExclusion : GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

After 0409 completes the conditional closure interface in `SignedGoldenClosure`, source order moves to the stage that closes the zero-sector receiver unconditionally.

`goldenZeroSectorFactorExclusion` takes the inversion source retained by a factor packet, extracts its `GoldenZeroSectorCandidate`, and feeds it to 0399 `goldenZeroSectorCandidate_false`, thereby excluding every certified factor branch.

The next step is therefore the finalization layer that supplies, from the already-proved infinite descent, the zero-sector arithmetic exclusion that had previously been exposed as a receiver.
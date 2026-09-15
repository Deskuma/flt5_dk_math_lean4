# 0418 `flt5Target_of_unitClasses_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
/-- Conditional receiver exposing both unit classification and zero-sector arithmetic. -/
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

## Mathematical statement and meaning of the declaration

This theorem says that the public exponent-five Fermat target follows once two final inputs from the golden-integer side are available:

1. `GoldenUnitClassesModFifth` — classification of golden units modulo fifth powers;
2. `GoldenZeroSectorArithmeticExclusion` — arithmetic exclusion of the Diophantine candidates remaining in the zero unit class.

Its type can be read schematically as

$$
\mathrm{GoldenUnitClassesModFifth}
\to
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

The theorem performs no new number-theoretic calculation. It simply connects the already-proved closure theorem

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

to the public target exposed by the Main layer.

## Role in the whole proof

Declaration 0417 introduced the final specification

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

and 0418 is the first theorem that returns this type. It is therefore the first conditional endpoint in the Main layer.

The closure layer has already established declaration 0409:

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

`PositiveFermat5Refuter` and `FLT5Target` are both transparent `abbrev` declarations with the same proposition body,

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

so 0418 can return the closure theorem's proof object directly, with no explicit conversion.

Architecturally, this is the final module-boundary adapter in the longer route

$$
\text{unit classification}
+
\text{zero-sector arithmetic}
\Longrightarrow
\text{primitive closure}
\Longrightarrow
\text{positive Fermat refuter}
\Longrightarrow
\text{public FLT5 target}.
$$

The following declarations then discharge the remaining assumptions one by one.

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

fills in `GoldenUnitClassesModFifth` with the already-proved theorem `goldenUnitClassesModFifth`, and then

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

fills in the zero-sector arithmetic exclusion as well.

Thus 0418 is the first stage of the final three-stage composition.

## Direct dependencies

### `GoldenUnitClassesModFifth`

The canonical source defines

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

This is the contract saying that, modulo fifth powers, every golden unit belongs to one of the five classes represented by

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4.
$$

Declaration 0418 does not inspect the proof of that classification; it only receives the completed contract as `hClasses`.

### `GoldenZeroSectorArithmeticExclusion`

This is the arithmetic contract excluding the integral-parameter candidates that remain in the zero sector. In the canonical source it is exposed as an `abbrev ... : Prop := ∀ (r s : ℤ) (a b : ℕ), ...`, encoding the Diophantine configuration produced by the certified primitive and tenth-power splits.

Again, 0418 does not inspect that proof. It simply forwards the contract as `hArithmetic` to the closure theorem.

### `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

This is the only DkMath theorem directly invoked by the body of 0418:

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter := ...
```

It has already absorbed primitive normalization, signed golden factorization, unit-class elimination, and zero-sector closure. The Main layer therefore only needs to reuse its result.

### `FLT5Target`

The public target introduced in 0417:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

It is the conclusion type of 0418.

## Proof flow

The proof is a one-line term-style proof:

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

Expanded conceptually, it proceeds as follows.

### 1. Receive the unit classification

```lean
hClasses : GoldenUnitClassesModFifth
```

This supplies the closure theorem with the modulo-fifth-power classification of golden units.

### 2. Receive the zero-sector exclusion

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

This supplies the arithmetic contract eliminating the zero sector left after the unit-class analysis.

### 3. Apply the closure theorem

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

The resulting type is `PositiveFermat5Refuter`.

### 4. Accept the result as `FLT5Target`

Because `PositiveFermat5Refuter` and `FLT5Target` unfold to the same proposition, Lean accepts that proof object directly as an inhabitant of `FLT5Target` by definitional equality.

No explicit `exact`, `simpa`, `change`, or `unfold` is required.

## Lean-specific processing

### Definitional equality between two `abbrev` declarations

The most important Lean-specific feature is that the named result type of the invoked theorem differs from the named result type requested by 0418, yet no conversion code appears.

Conceptually the body returns

```lean
PositiveFermat5Refuter
```

while the declaration asks for

```lean
FLT5Target.
```

Both are transparent `abbrev` declarations with the same unfolded proposition, so Lean's type checker identifies them definitionally.

If one of the interfaces were opaque or had only a propositionally equivalent, rather than definitionally identical, body, an explicit `change`, rewriting step, or equivalence theorem could be required.

### Curried theorem application

The assumptions

```lean
(hClasses : ...)
(hArithmetic : ...)
```

are curried arguments, so the proof body is ordinary function application:

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

### Term proof rather than a tactic block

The declaration uses

```lean
:=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

rather than a `by` block.

This accurately reflects the architecture: the theorem is not carrying out a new derivation; it is transporting an existing theorem into the public API layer.

## Redundancy and duplication

Logically, 0418 is very close to declaration 0409.

Declaration 0409 returns

```lean
... : PositiveFermat5Refuter
```

whereas 0418 returns

```lean
... : FLT5Target.
```

Since the proposition bodies are identical, 0418 adds no new mathematical content.

This duplication is nevertheless architectural rather than accidental:

- 0409 is the internal closure-layer API;
- 0418 is the public Main-layer endpoint.

The same proof object is deliberately given an internal and a public interface name.

There is also deliberate thin-wrapper duplication between 0418 and 0419 `flt5Target_of_zeroArithmetic`. Declaration 0418 leaves both unit classification and zero-sector arithmetic as external inputs; 0419 fixes the unit-class input to its already-proved provider. The sequence makes the dependency cuts explicit.

## Optimization candidates

### 1. Omit 0418 and construct 0419 directly

If minimizing source size were the only objective, 0419 could directly return

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

and 0418 could be removed.

The cost would be losing a named theorem recording the important dependency cut

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

For auditability and Comparator challenge design, retaining the receiver theorem is useful.

### 2. Define `FLT5Target` as an alias of `PositiveFermat5Refuter`

As noted for 0417, one could write

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

which would make the relationship between the internal and public interfaces even more explicit.

The trade-off is reduced self-documentation when reading only the Main layer.

### 3. Abstract a generic receiver combinator

A wrapper that merely exposes the same proposition under a public alias could be generalized, but introducing a generic combinator for this single occurrence would likely add more abstraction cost than value.

The current one-line theorem is clearer.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

but 0418 itself uses almost no Mathlib-specific machinery beyond ordinary theorem application and type checking. It does not invoke number-theory tactics, ring tactics, or valuation APIs.

Its substantive dependencies are the DkMath declarations providing

- `FLT5Target`;
- `GoldenUnitClassesModFifth`;
- `GoldenZeroSectorArithmeticExclusion`;
- `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`.

The standalone manifest places the relevant material along the ordered module chain containing `GoldenUnitClassification.lean`, `SignedGoldenClosure.lean`, `SignedGoldenZeroSectorFinal.lean`, and `Main.lean`.

### Import optimization candidate

There is little reason for 0418 alone to require all of `import Mathlib`. In a split-source setting, imports that provide the four DkMath declarations above should likely suffice.

However, this run does not perform a Lean build, and the exact minimal Mathlib import closure of the split Main module was not experimentally verified here. Therefore no specific minimal replacement import is asserted.

## Comparator challenge suitability

**Suitable, with low-to-medium difficulty.**

Although the finished theorem is only one line, a challenge can test whether the solver recognizes the architecture connecting

- `GoldenUnitClassesModFifth`;
- `GoldenZeroSectorArithmeticExclusion`;
- `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`;
- the definitional equality of `PositiveFermat5Refuter` and `FLT5Target`.

A basic challenge could be

```lean
theorem challenge
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target := by
  ?_
```

and ask the solver to discover and apply the closure theorem.

For greater difficulty, declaration 0409 could be withheld, forcing reconstruction from `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` and `positiveFermat5Refuter_of_counterexamplePackRefuter`. That tests understanding of the two-stage closure architecture rather than simple theorem lookup.

A still larger challenge could include declarations 0419 through the final `flt5Target`, testing the complete process of discharging conditional assumptions with already-proved providers.

## Next declaration to read

The next declaration is 0419:

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

Declaration 0418 establishes

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

Declaration 0419 substitutes the proved theorem

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

and removes the unit-class assumption, leaving

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

The following unconditional `goldenZeroSectorArithmeticExclusion` can then be substituted to obtain `flt5Target : FLT5Target`, so 0419 is the receiver immediately before the final endpoint.

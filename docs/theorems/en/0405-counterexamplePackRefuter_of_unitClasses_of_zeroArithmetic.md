# 0405 `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
/-- Unit classification and zero-sector arithmetic suffice for all primitive packets. -/
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

## Mathematical statement and meaning

This theorem shows that two golden-order inputs are sufficient to refute every primitive FLT5 counterexample packet:

1. the classification of units modulo fifth powers, `GoldenUnitClassesModFifth`;
2. the arithmetic exclusion of the zero sector, `GoldenZeroSectorArithmeticExclusion`.

Its type is

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{CounterexamplePackRefuter}.
$$

In 0400, `GoldenZeroSectorArithmeticExclusion` was introduced as a raw arithmetic receiver. In 0401 it was converted into

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{SignedGoldenZeroSectorExclusion}.
$$

A preceding unit-class closure theorem gives

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{SignedGoldenZeroSectorExclusion}
\Longrightarrow
\mathrm{SignedGoldenUnitFifthPowerExclusion}.
$$

Then 0404 gives

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}.
$$

Thus 0405 is exactly the composition of these previously established maps.

The full logical circuit is

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
\quad+
\mathrm{GoldenZeroSectorArithmeticExclusion}\\
&\qquad\Downarrow\\
&\mathrm{GoldenUnitClassesModFifth}
\quad+
\mathrm{SignedGoldenZeroSectorExclusion}\\
&\qquad\Downarrow\\
&\mathrm{SignedGoldenUnitFifthPowerExclusion}\\
&\qquad\Downarrow\\
&\mathrm{CounterexamplePackRefuter}.
\end{aligned}
$$

In other words, the theorem glues together the arithmetic contradiction obtained from zero-sector descent and the finite classification of the nonzero unit classes, then carries the result all the way to primitive FLT5 closure.

## Role in the whole proof

0405 is an important composition point in the `SignedGoldenClosure` layer.

Up to this point, responsibilities are deliberately separated:

- unit-class classification is represented by `GoldenUnitClassesModFifth`;
- the difficult zero-sector descent is represented by `GoldenZeroSectorArithmeticExclusion`;
- conversion from raw arithmetic to the signed zero-sector receiver is handled by 0401;
- integration of unit classes with the zero sector is handled by `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`;
- routing closure from unit-times-fifth-power exclusion to all primitive packets is handled by 0404.

0405 packages all of these into one public theorem.

Therefore this theorem proves no new number-theoretic calculation of its own. It introduces no new congruence, valuation argument, golden-integer computation, or descent-measure estimate. Its purpose is to compose existing receiver theorems in the correct order.

This design lets downstream results depend only on unit classification and zero-sector arithmetic, without manually rebuilding either `SignedGoldenZeroSectorExclusion` or `SignedGoldenUnitFifthPowerExclusion`.

## Direct dependencies

### `GoldenUnitClassesModFifth`

This is the type of the first argument `hClasses`.

It is the receiver contract used to classify golden units into finitely many classes modulo fifth powers.

0405 does not inspect the classification internally. It passes `hClasses` directly to

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

which consumes that interface.

### `GoldenZeroSectorArithmeticExclusion`

This is the type of the second argument `hArithmetic`, introduced as an `abbrev` in 0400.

It packages the raw integer-arithmetic conditions required to exclude the zero sector.

0405 does not apply it directly to primitive packets. It first converts it through 0401 into the signed zero-sector receiver.

### `signedGoldenZeroSectorExclusion_of_arithmetic`

This is theorem 0401.

The application

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

produces

```lean
SignedGoldenZeroSectorExclusion
```

and mathematically implements

$$
\mathrm{raw\ zero\ arithmetic}
\Longrightarrow
\mathrm{signed\ zero\ sector\ exclusion}.
$$

### `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`

This preceding theorem combines unit-class classification with zero-sector exclusion.

Conceptually its type is

```lean
GoldenUnitClassesModFifth →
SignedGoldenZeroSectorExclusion →
SignedGoldenUnitFifthPowerExclusion
```

and the inner application

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
  (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic)
```

produces a `SignedGoldenUnitFifthPowerExclusion`.

At this stage the nonzero unit classes are eliminated by finite classification, while the zero class is eliminated by the zero-sector theorem.

### `counterexamplePackRefuter_of_unitFifthPowerExclusion`

This is theorem 0404.

Its type is

```lean
SignedGoldenUnitFifthPowerExclusion → CounterexamplePackRefuter
```

and internally it uses the orientation theorem from 0402 together with `CounterexamplePack.swap` to route either left-gap orientation into the same Branch B refuter.

0405 uses this theorem as its outermost map.

### `CounterexamplePackRefuter`

This is the `abbrev` introduced in 0403:

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

Hence the conclusion of 0405 is exactly that every primitive FLT5 packet leads to contradiction.

## Proof/construction flow

The proof term uses no tactic block. It is written as a three-stage functional composition.

### 1. Convert zero-sector arithmetic into the signed receiver

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

This yields

```lean
SignedGoldenZeroSectorExclusion
```

### 2. Combine unit classes with the zero sector

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
  (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic)
```

This yields

```lean
SignedGoldenUnitFifthPowerExclusion
```

At this point every unit class in a unit-times-fifth-power representation has been excluded.

### 3. Close all primitive packets

```lean
counterexamplePackRefuter_of_unitFifthPowerExclusion
  (...)
```

Passing the previous exclusion into 0404 gives

```lean
CounterexamplePackRefuter
```

Thus the proof is essentially the composition of existing maps of the shape

$$
A\to B,
\qquad
(C,B)\to D,
\qquad
D\to E,
$$

into

$$
(C,A)\to E.
$$

## Lean-specific processing

### Tactic-free term proof

The declaration ends with

```lean
:=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (...)
```

rather than a `by` block.

Curried function application completely determines the proof term, so no `intro`, `exact`, or `simpa` is needed.

### Nested function application

Lean elaborates the innermost term

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

first and uses its result type to fill the second argument of

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

The resulting `SignedGoldenUnitFifthPowerExclusion` then exactly matches the input expected by 0404.

Because the receiver boundaries are explicitly typed, no additional type annotation is required.

### Transparency of the `abbrev` conclusion

The final conclusion `CounterexamplePackRefuter` is an `abbrev`, but this proof does not need to unfold it.

The result of 0404 already has exactly that named proposition type, so it matches directly.

### Hiding dependent indices behind public interfaces

The primitive packet indices `{x y z}`, the indices of golden packets, and the unit-class data are all hidden behind the preceding receiver theorems.

As a result, 0405 requires no explicit dependent-index arguments and no rewriting. This is a good example of the closure API successfully isolating lower-level dependent structure.

## Redundancy and duplication

There is almost no redundancy in the proof term itself.

One could instead name the intermediate results explicitly:

```lean
by
  have hZero := signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
  have hExclude :=
    signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses hZero
  exact counterexamplePackRefuter_of_unitFifthPowerExclusion hExclude
```

but the current nested term has only three stages and the types are clear, so it provides a good balance between brevity and readability.

The closure layer contains several thin adapters such as 0401, 0404, and 0405, but this is not merely accidental duplication. Each marks a distinct boundary:

- raw arithmetic boundary;
- unit-times-fifth-power boundary;
- primitive-packet boundary.

Keeping these boundaries explicit makes it easier to replace or audit one component independently of the others.

## Optimization candidates

### Keeping the current form is the strongest candidate

0405 already composes the public APIs directly and is close to minimal as a proof term.

Compressing it further would not produce a meaningful simplification and could make the relationship among the theorem names less readable.

### General composition helper

If the same receiver-chain pattern appeared in many other exponents, one could introduce a generic composition combinator.

However, ordinary Lean function application already serves that purpose, so introducing a special helper solely for 0405 would add more abstraction than value.

### Consolidating intermediate adapters

A possible future API could expose a direct theorem of type

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
SignedGoldenUnitFifthPowerExclusion
```

However, explicitly retaining the 0401 boundary has the advantage that the transition from raw arithmetic to the signed zero-sector theorem remains independently inspectable.

For this part of the development, preserving the receiver architecture is more valuable than reducing the number of lines.

## Required Mathlib import

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The body of 0405 itself uses no tactics and consists only of applications of previously defined DkMath theorems. Therefore the theorem has very little direct Mathlib dependency of its own.

Most dependencies come from the preceding DkMath declarations that define:

- `GoldenUnitClassesModFifth`;
- `GoldenZeroSectorArithmeticExclusion`;
- `SignedGoldenZeroSectorExclusion`;
- `SignedGoldenUnitFifthPowerExclusion`;
- `CounterexamplePackRefuter`;
- the adapter theorems connecting them.

According to the standalone manifest, this declaration belongs to `DkMath/FLT/Five/SignedGoldenClosure.lean`.

### Import-optimization candidate

There is no reason for 0405 alone to require the entirety of `import Mathlib`.

In the modular development, it should be sufficient to import the DkMath modules exposing the receiver types and adapter theorems above, plus whatever minimal Mathlib modules those dependencies themselves require.

No Lean build was run in this pass, so the exact minimal Mathlib import set has not been verified. Any future import slimming should be confirmed with `lake build` at the module level.

## Comparator challenge suitability

As a standalone proof-synthesis challenge, this theorem is **easy**.

If all required theorems are placed in the context, the target is almost forced by the types.

A challenge can expose only

```lean
hClasses : GoldenUnitClassesModFifth
hArithmetic : GoldenZeroSectorArithmeticExclusion

signedGoldenZeroSectorExclusion_of_arithmetic :
  GoldenZeroSectorArithmeticExclusion → SignedGoldenZeroSectorExclusion

signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector :
  GoldenUnitClassesModFifth →
  SignedGoldenZeroSectorExclusion →
  SignedGoldenUnitFifthPowerExclusion

counterexamplePackRefuter_of_unitFifthPowerExclusion :
  SignedGoldenUnitFifthPowerExclusion → CounterexamplePackRefuter
```

with target

```lean
CounterexamplePackRefuter
```

This tests API composition and theorem selection more than number theory.

For a more substantial Comparator challenge, one would hide 0401 or the unit-class integration theorem and require reconstruction of `SignedGoldenUnitFifthPowerExclusion` from lower-level packet lemmas.

## Next declaration to read

The next declaration in the canonical source is

```lean
/-- Arbitrary positive solutions can be reduced to a primitive counterexample packet. -/
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x₀ y₀ z₀ : ℕ, CounterexamplePack x₀ y₀ z₀ := by
  ...
```

Up through 0405, the development has closed

$$
\mathrm{primitive\ CounterexamplePack}\to\bot.
$$

The next step extracts a primitive packet from an arbitrary positive FLT5 solution

$$
x^5+y^5=z^5,
\qquad x,y,z>0.
$$

Thus the proof layer now moves from

$$
\text{primitive closure}
\longrightarrow
\text{normalization of arbitrary positive solutions}.
$$

0405 is therefore the last major composition point between the golden-order closure chain and the final positive-natural-number FLT5 theorem.

# 0423 `counterexamplePackRefuter_of_zeroArithmetic`

## Declaration kind

`theorem`

## Lean type

```lean
/-- The zero-sector arithmetic proposition refutes every primitive packet. -/
theorem counterexamplePackRefuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## Mathematical statement and meaning

0423 states that, once the zero-sector arithmetic exclusion proposition is available, every primitive FLT5 counterexample packet can be refuted.

The conclusion `CounterexamplePackRefuter` is an `abbrev : Prop` defined by

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

Thus the mathematical content is

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\forall x,y,z\in\mathbb N,
\ \mathrm{CounterexamplePack}(x,y,z)\to\bot.
$$

A `CounterexamplePack x y z` packages a positive exponent-five solution candidate together with the primitive conditions required by the arithmetic core. Hence 0423 is the conditional closure theorem for the primitive layer.

The key point is that 0423 no longer assumes the unit classification. The more general receiver

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
```

has type

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
CounterexamplePackRefuter
```

but 0423 supplies the already proved theorem

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

so that the only remaining assumption is the zero-sector arithmetic exclusion.

## Role in the overall proof

0423 is the public primitive-counterexample receiver in the `Main` layer.

The FLT5 closure may be schematically viewed as

$$
\text{unit classification}
\Longrightarrow
\text{finite unit sectors}
\Longrightarrow
\text{elimination of nonzero sectors}
\Longrightarrow
\text{elimination of the zero sector}
\Longrightarrow
\text{refutation of primitive packets}
\Longrightarrow
\text{refutation of arbitrary positive solutions}.
$$

0423 exposes the boundary

$$
\text{zero-sector arithmetic exclusion}
\Longrightarrow
\text{primitive-packet refuter}.
$$

The final theorem `flt5Target` concerns all positive solutions, whereas `CounterexamplePackRefuter` is the closure endpoint of the arithmetic core before gcd normalization is used to reduce an arbitrary positive solution to a primitive packet. Therefore 0423 is a facade theorem that makes the primitive layer independently reusable and auditable.

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
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
      goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s =
      -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

0423 takes this as its only external assumption.

### `CounterexamplePackRefuter`

This is the proposition that refutes all primitive packets.

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

It is exactly the conclusion of 0423.

### `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

This is the receiver theorem called directly by 0423.

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

This theorem performs the actual composition from unit classification and zero-sector arithmetic to the primitive-packet refuter.

### `goldenUnitClassesModFifth`

This is the unconditional provider of the unit-classification contract.

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

0423 supplies it as the first argument of the general receiver, thereby discharging the unit-classification assumption.

## Proof or construction flow

The proof of 0423 itself is a single function application:

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

The flow is as follows.

### 1. Start from the two-assumption receiver

The existing theorem has type

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
CounterexamplePackRefuter
```

### 2. Supply the unconditional unit classification

Since `goldenUnitClassesModFifth` already exists as a proof object, it can be passed directly as the first argument.

After this partial application, the receiver has type

```lean
GoldenZeroSectorArithmeticExclusion → CounterexamplePackRefuter
```

### 3. Supply the zero-sector arithmetic assumption

Passing the remaining argument `hArithmetic` yields

```lean
CounterexamplePackRefuter
```

No case split, rewrite, `ring`, `omega`, or gcd computation occurs in 0423 itself. All such arithmetic work has already been encapsulated in lower-level theorems.

## Lean-specific processing

### Theorem composition via Curry–Howard

`GoldenUnitClassesModFifth`, `GoldenZeroSectorArithmeticExclusion`, and `CounterexamplePackRefuter` are all propositions, and their theorems are proof objects.

Thus 0423 is just the application of a theorem of type

```lean
A → B → C
```

to

```lean
a : A
b : B
```

in order to obtain `C`.

### Transparency of `abbrev`

`CounterexamplePackRefuter` is an `abbrev`, so Lean may unfold it definitionally to

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

when needed.

No explicit `unfold` or `simpa` is required in 0423 because the return type of the receiver already matches the target.

### Partial application

The expression

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
```

already denotes a function waiting for a proof of `GoldenZeroSectorArithmeticExclusion`. 0423 then applies that function to `hArithmetic`.

## Redundancy and duplication

0423 introduces no new number-theoretic content.

The same conclusion could be obtained at any use site by writing

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

directly. In that narrow sense, 0423 is a facade wrapper.

The duplication is nevertheless useful by design:

- it provides a short public receiver for the primitive-packet layer;
- it records at the API level that unit classification has already been discharged unconditionally;
- it makes the zero-sector arithmetic assumption the only visible remaining boundary;
- it separates auditing of the primitive target from auditing of the full positive target.

Therefore, as with 0419 and 0422, this duplication is best understood as intentional interface duplication rather than accidental proof repetition.

## Optimization candidates

### 1. Remove the wrapper

If minimizing source size were the only goal, 0423 could be deleted and callers could compose the receiver and provider directly.

That would, however, weaken the public API and make the abstraction boundary less explicit.

### 2. Proof syntax

The present term-style proof is already essentially minimal.

The equivalent

```lean
by
  exact counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

is longer without adding information.

### 3. Normalize facade naming

The `Main` layer contains closely related receivers such as

```text
flt5Target_of_zeroArithmetic
counterexamplePackRefuter_of_zeroArithmetic
positiveFermat5Refuter_of_zeroArithmetic
```

This repetition is structurally useful because each theorem marks an abstraction-level endpoint. If the facade layer is reorganized later, a fully regular conditional/unconditional naming policy could make dependency tracing even more mechanical.

## Required Mathlib imports

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

0423 itself performs only theorem application and does not directly use any specialized Mathlib tactic.

At minimum, the following FLT5 declarations must already be available in the environment:

- `GoldenZeroSectorArithmeticExclusion`
- `CounterexamplePackRefuter`
- `GoldenUnitClassesModFifth`
- `goldenUnitClassesModFifth`
- `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

Their transitive dependencies include `CounterexamplePack`, the signed-golden sector machinery, zero-sector exclusion, and unit classification.

### Import optimization candidate

From the body of 0423 alone, importing all of `Mathlib` directly is unlikely to be necessary. In the split source, the import closure containing `SignedGoldenClosure` and the unit-classification provider should plausibly be sufficient.

No Lean build is run in this task, so the minimal Mathlib module set and the exact minimal FLT5 import closure have not been measured. Specific minimal import names are therefore left unconfirmed rather than asserted.

## Comparator challenge suitability

 **Suitable. It is low difficulty, but cleanly tests provider/receiver composition and partial application.**

A minimal challenge could provide

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic :
  GoldenUnitClassesModFifth →
  GoldenZeroSectorArithmeticExclusion →
  CounterexamplePackRefuter

goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

and ask for

```lean
theorem challenge
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter := by
  ?_
```

The solver succeeds once it discovers

```lean
exact counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

A more valuable challenge would hide `goldenUnitClassesModFifth` and require reconstructing `GoldenUnitClassesModFifth` from lower-level unit-classification results. An even harder variant would hide `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` itself and require rebuilding the three-stage composition

```text
signedGoldenZeroSectorExclusion_of_arithmetic
→ signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
→ counterexamplePackRefuter_of_unitFifthPowerExclusion
```

which would test dependency selection much more substantially.

## Next declaration to read

The next declaration is 0424 `positiveFermat5Refuter_of_zeroArithmetic`.

```lean
/-- The zero-sector arithmetic proposition refutes every positive solution. -/
theorem positiveFermat5Refuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

Whereas 0423 closes the primitive-packet layer, 0424 exposes the corresponding receiver at the full positive-solution layer, including the normalization bridge from arbitrary positive solutions to primitive packets.

The abstraction-level progression is therefore

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter}.
$$
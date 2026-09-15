# 0421 `fermatFive_no_positive_solution`

## Declaration kind

`theorem`

## Lean type

```lean
/--
Ordinary-argument wrapper around `flt5Target`: for positive natural numbers
`x`, `y`, and `z`, it proves the negation of `Fermat5Equation x y z`, i.e.
`x^5 + y^5 = z^5`. It does not expose a general-exponent theorem or a theorem
about arbitrary signed integers.
-/
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz
```

## Mathematical statement and meaning

This theorem exposes the unconditional exponent-five Fermat result in the ordinary argument form that is most convenient for direct use.

The proposition `Fermat5Equation x y z` means

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

so the whole type says mathematically

$$
\forall x,y,z\in\mathbb N,
\qquad
x>0\to y>0\to z>0\to x^5+y^5\ne z^5.
$$

Where 0420 `flt5Target` returned a proof of the single proposition

```lean
FLT5Target
```

as a whole, 0421 takes `x`, `y`, `z` and the three positivity assumptions explicitly and returns

```lean
¬ Fermat5Equation x y z
```

for those arguments.

Its mathematical content is therefore the same as 0420. It adds no new number-theoretic lemma. Its purpose is to **expand the unconditional closure into an external-use API**.

As the canonical source docstring states, the scope is positive natural numbers and exponent five only. This is not a statement of the general-exponent Fermat theorem and not a theorem about arbitrary signed integers.

## Role in the overall proof

0421 is the public wrapper around the completed FLT5 proof.

By 0420, the dependency chain has already been closed unconditionally, ultimately producing

```lean
flt5Target : FLT5Target
```

from the zero-sector arithmetic exclusion.

The definition from 0417 is

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

so `flt5Target` can in fact be treated as a function-like proof term taking the six arguments

```lean
x y z hx hy hz
```

in sequence.

0421 merely gives that application a named theorem.

At the public endpoint layer, the architecture is therefore:

1. 0417 defines the final specification.
2. 0418–0419 expose conditional endpoints.
3. 0420 discharges the last hypothesis and obtains the unconditional endpoint.
4. 0421 expands that endpoint into the ordinary-argument theorem form.

Thus 0421 sits at the outermost public layer of the proof.

## Direct dependencies

### `Fermat5Equation`

This is the central proposition defined in 0001.

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

The conclusion

```lean
¬ Fermat5Equation x y z
```

is exactly the negation of this equation.

### `FLT5Target`

This is the `abbrev : Prop` introduced in 0417.

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

The arguments and conclusion of 0421 are precisely the result of applying this proposition one binder at a time.

### `flt5Target`

This is the unconditional theorem from 0420.

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

It is the only theorem directly invoked by the body of 0421.

## Proof or construction flow

The proof body is only one line:

```lean
flt5Target x y z hx hy hz
```

### 1. Obtain `flt5Target`

From 0420 we have

```lean
flt5Target : FLT5Target
```

with no assumptions.

### 2. Expand `FLT5Target` as a function type

Because `FLT5Target` is an `abbrev`, its body is transparently

```lean
∀ x y z : ℕ,
  0 < x →
  0 < y →
  0 < z →
  ¬ Fermat5Equation x y z
```

Lean may therefore apply `flt5Target` first to `x`, `y`, `z`, then to proofs `hx`, `hy`, and `hz`.

### 3. Obtain the concrete negation

After the six applications, the result is

```lean
¬ Fermat5Equation x y z
```

which is exactly the target of 0421.

No rewrite, case split, arithmetic tactic, valuation argument, or descent argument is needed at this stage.

## Lean-specific processing

### Definitional transparency of `abbrev`

The most important Lean-specific point is that `FLT5Target` was defined as an `abbrev` rather than an opaque interface.

Lean can transparently treat

```lean
flt5Target : FLT5Target
```

as a proof of

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

when application requires it.

That is why the direct term

```lean
flt5Target x y z hx hy hz
```

works without an explicit unfold step.

### Curry–Howard correspondence

Universal quantification and implication are represented as function types in Lean.

A proof of

```lean
∀ x : ℕ, P x
```

is a function taking `x` and returning a proof of `P x`, while a proof of

```lean
A → B
```

is a function taking a proof of `A` and returning a proof of `B`.

0421 uses exactly this mechanism.

### Term-style proof

The theorem contains no tactic block:

```lean
:=
  flt5Target x y z hx hy hz
```

This is the clearest possible form for a public wrapper whose dependencies have already been fully discharged.

## Redundancy and duplication

Mathematically, 0421 carries the same information as 0420 in a different API shape, so in a strict information-theoretic sense it is redundant.

Even without 0421, a user could write

```lean
exact flt5Target x y z hx hy hz
```

directly.

However, as a public API, the name

```lean
fermatFive_no_positive_solution
```

communicates its use immediately and does not require users to know the specification alias `FLT5Target`.

Its theorem statement also exposes `x y z` and the positivity hypotheses directly, which improves discoverability, completion behavior, and pedagogical value.

The duplication is therefore best understood as **intentional API-facade duplication**, not wasted proof content.

## Optimization candidates

### 1. Remove the wrapper

If the only goal were to minimize code, 0421 could be deleted and callers could use

```lean
flt5Target x y z hx hy hz
```

directly.

That would preserve the mathematics but make the public interface less descriptive, so keeping the wrapper is reasonable.

### 2. Do not add `simpa` or `exact`

The same proof could be written as

```lean
by
  exact flt5Target x y z hx hy hz
```

but that is longer than the current term-style proof.

Likewise, an explicit

```lean
simpa [FLT5Target] using ...
```

would be unnecessary. The present implementation correctly relies on `abbrev` transparency.

### 3. Naming

`fermatFive_no_positive_solution` describes the theorem in a natural-language style and cleanly distinguishes the public theorem from the specification alias `FLT5Target`. No strong naming optimization is apparent.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

However, the body of 0421 directly uses only theorem application together with the natural-number types and inequalities already present in the surrounding development. It does not invoke any specialized tactic or Mathlib API itself.

Operationally, the theorem only requires that the following declarations already be available:

- `Fermat5Equation`
- `FLT5Target`
- `flt5Target`

In the split source tree, this means the transitive import closure of the FLT5 modules providing these declarations.

### Import optimization candidate

It is very likely unnecessary to import all of `Mathlib` directly for 0421 alone. The transitive dependencies of `Main.lean` and the FLT5 modules should suffice.

This run does not execute a Lean build, so the exact minimal import closure has not been measured. Therefore no specific minimal set of Mathlib module names is asserted here.

## Comparator challenge suitability

 **Suitable, but very low difficulty in isolation.**

A basic challenge could be

```lean
theorem challenge
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z := by
  ?_
```

with

```lean
flt5Target : FLT5Target
```

available.

The solver then has to recognize the transparent expansion of `FLT5Target` and apply its six arguments.

This tests Lean API understanding rather than mathematical search, especially:

- `abbrev` transparency,
- dependent/function application,
- propositions as functions,
- use of a public endpoint.

To increase the difficulty, hide `flt5Target` and expose only 0419 `flt5Target_of_zeroArithmetic` together with `goldenZeroSectorArithmeticExclusion`. The solver must first construct `FLT5Target` and then apply it to the concrete arguments.

Going back one level further to 0418 can also require resolving the unit-class provider, turning the exercise into a multi-stage dependency challenge.

## Next declaration to read

The next declaration is 0422 `signedGoldenFiniteUnitSectorCore`, of kind `theorem`.

```lean
/-- Every stripped golden packet is unconditionally reduced to the five sectors. -/
theorem signedGoldenFiniteUnitSectorCore : SignedGoldenFiniteUnitSectorCore :=
  signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

0421 completes the final ordinary-argument public wrapper for the FLT5 statement itself, but `Main.lean` continues with facade theorems exposing internal proof structures.

0422 applies the already-proved provider `goldenUnitClassesModFifth` to `signedGoldenFiniteUnitSectorCore_of_unitClasses`, yielding the unconditional core proposition that every stripped golden packet is reduced to one of the five unit sectors.

Therefore 0421 is a natural endpoint for the FLT5 statement API, but it is not yet the end of the declaration sequence to be documented.
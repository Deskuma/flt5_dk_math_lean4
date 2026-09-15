# 0420 `flt5Target`

## Declaration kind

`theorem`

## Lean type

```lean
/--
The unconditional exponent-five target for positive natural numbers. It denies
`Fermat5Equation x y z`, namely `x^5 + y^5 = z^5`, for every positive
`x`, `y`, and `z`. This is not a general-exponent or signed-integer theorem.
-/
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

## Mathematical statement and meaning of the declaration

This theorem proves the unconditional public target of the development for Fermat's equation at exponent five.

Expanding declaration 0417 `FLT5Target`, its type is

```lean
∀ x y z : ℕ,
  0 < x →
  0 < y →
  0 < z →
  ¬ Fermat5Equation x y z
```

where `Fermat5Equation` denotes

```lean
x ^ 5 + y ^ 5 = z ^ 5.
```

Thus, mathematically, it states

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5.
$$

The crucial point is that 0420 has no remaining hypothesis parameter. Declarations 0418 and 0419 exposed proof boundaries as conditional receivers; declaration 0420 fills the final remaining input

```lean
GoldenZeroSectorArithmeticExclusion
```

with the already-proved theorem

```lean
goldenZeroSectorArithmeticExclusion.
```

This single application closes the FLT5 dependency chain at an unconditional endpoint.

As the canonical docstring explicitly states, the scope is exponent five over positive natural numbers. It does not assert Fermat's Last Theorem for arbitrary exponents, nor a theorem over arbitrary signed integers.

## Role in the whole proof

Declaration 0420 is the central unconditional endpoint in `Main.lean`.

The preceding declaration 0419 provides the receiver

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target},
$$

namely

```lean
flt5Target_of_zeroArithmetic.
```

Meanwhile declaration 0412 `goldenZeroSectorArithmeticExclusion`, after the full zero-sector construction including certified strict infinite descent, proves unconditionally

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

Declaration 0420 composes these two pieces:

$$
\bigl(
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
\bigr)
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}.
$$

No new number-theoretic argument, case split, descent, or valuation calculation occurs here. All local proof obligations have already been solved in the dependency graph; 0420 is the closure point that connects those completed components into a proof term of the final proposition.

Looking only at the Main-layer dependency discharge, the final stages are

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target},\\
&\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target},\\
&\mathrm{FLT5Target}.
\end{aligned}
$$

Declaration 0420 is the last line, where the final conditional input disappears.

## Direct dependencies

### `FLT5Target`

This is the `abbrev : Prop` introduced in declaration 0417:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

It is the result type of 0420.

### `flt5Target_of_zeroArithmetic`

This is the conditional receiver explained in declaration 0419:

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

Declaration 0420 fills its sole argument.

### `goldenZeroSectorArithmeticExclusion`

This is the unconditional provider established in declaration 0412:

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

Behind it lies the entire zero-sector chain through candidates, inversion packets, factor packets, descent packets, and strict infinite descent. Declaration 0420 does not reopen that internal proof; it consumes the completed proposition as a proof term.

## Proof or construction flow

The complete proof body is

```lean
flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

### 1. Take the conditional endpoint

From declaration 0419 we have

```lean
flt5Target_of_zeroArithmetic :
  GoldenZeroSectorArithmeticExclusion → FLT5Target.
```

### 2. Supply the unconditional provider for the final input

Declaration 0412 provides

```lean
goldenZeroSectorArithmeticExclusion :
  GoldenZeroSectorArithmeticExclusion.
```

### 3. Obtain `FLT5Target`

Function application returns a proof term of

```lean
FLT5Target.
```

No additional `by` block, rewrite, `simp`, `omega`, `norm_num`, or `ring` is needed.

## Lean-specific processing

### Connecting a proposition to its proof term

In Lean,

```lean
GoldenZeroSectorArithmeticExclusion
```

is a proposition, and

```lean
goldenZeroSectorArithmeticExclusion
```

is a term inhabiting that proposition.

Therefore the theorem can be passed directly as the proposition-valued argument required by

```lean
flt5Target_of_zeroArithmetic.
```

Declaration 0420 is a particularly clean appearance of Curry–Howard correspondence at the final closure boundary.

### Term-style proof

The declaration is a complete term proof:

```lean
:=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

Its one-line size does not indicate that the underlying proof is shallow. Rather, all proof search and arithmetic difficulty has already been discharged in dependencies, so the final layer has been engineered to close by type-correct composition alone.

### Transparency of `abbrev`

The conclusion `FLT5Target` is an `abbrev`, so later declarations can transparently use its body

```lean
∀ x y z : ℕ, ...
```

when needed. This is why the next theorem `fermatFive_no_positive_solution` can apply

```lean
flt5Target x y z hx hy hz
```

directly as if `flt5Target` were an ordinary multi-argument theorem.

## Redundancy and duplication

Declaration 0420 is a direct composition of declarations 0419 and 0412 and introduces no new number-theoretic fact beyond that composition.

If shortest source were the only objective, one could bypass 0419 and write

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

directly. One could even design the public endpoint to connect to an internal closure theorem without the intermediate Main-layer wrappers.

The existing architecture instead keeps three named stages:

- 0418: receiver exposing both unit classification and zero-sector arithmetic;
- 0419: receiver after unit classification has been discharged;
- 0420: unconditional endpoint after zero-sector arithmetic has also been discharged.

That sequence improves proof-boundary auditing, dependency substitution, and comparison with possible alternative proof routes. The thin wrappers are therefore architectural duplication rather than accidental redundancy.

## Optimization candidates

### 1. Compress the Main-layer wrappers

If reducing line count were the primary goal, declaration 0419 could be removed and 0420 could pass both proved providers directly to 0418.

The cost would be losing the useful intermediate API

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}.
$$

For proof architecture and auditability, the current structure is clearer.

### 2. Merge endpoint naming

`FLT5Target` and `PositiveFermat5Refuter` have corresponding proposition shapes, so an alternative design could return the public endpoint directly from the internal closure layer. Keeping the internal refuter and public target separately named, however, makes their layer roles explicit.

### 3. Local proof-term optimization

The current one-line term is already essentially minimal. Introducing `exact`, `simpa`, or an explicit `by` block would only add syntactic overhead.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

but the body of 0420 itself only performs theorem application. It does not directly use any Mathlib tactic or arithmetic API.

Its substantive requirements are simply that the following DkMath declarations are available:

- `FLT5Target`;
- `flt5Target_of_zeroArithmetic`;
- `goldenZeroSectorArithmeticExclusion`.

In the ordered standalone source modules, `SignedGoldenZeroSectorFinal.lean` supplies the unconditional zero-sector provider and `Main.lean` constructs the public endpoint.

### Import optimization candidate

In split-source form, the transitive closure of the DkMath module imports providing the declarations above should likely be sufficient; there is little reason for declaration 0420 alone to require a direct import of all of `Mathlib`.

This run does not perform a Lean build, so the exact minimal import closure was not experimentally checked. No specific minimal set of Mathlib modules is therefore asserted.

## Comparator challenge suitability

 **Suitable. The difficulty is low, but it is a very clear proof-dependency-resolution exercise.**

A basic challenge can be stated as

```lean
theorem challenge : FLT5Target := by
  ?_
```

with

```lean
flt5Target_of_zeroArithmetic
goldenZeroSectorArithmeticExclusion
```

available. The solver must recognize the composable pair

```lean
GoldenZeroSectorArithmeticExclusion → FLT5Target
```

and

```lean
GoldenZeroSectorArithmeticExclusion.
```

For a harder variant, hide declaration 0419 and require construction from 0418 plus the two proved providers. Hiding the receiver layer as well would turn the task into tracing the definitional correspondence between the closure-layer `PositiveFermat5Refuter` and the public `FLT5Target`.

Thus 0420 is not primarily a mathematical-search challenge. Its value is as a compact test of recognizing the final proof-term composition in a large dependency graph.

## Next declaration to read

The next declaration is 0421 `fermatFive_no_positive_solution`, of kind `theorem`:

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

Declaration 0420 returns the unconditional endpoint as one proposition. Declaration 0421 unfolds that endpoint into an ordinary theorem taking explicit arguments `x y z hx hy hz`, making the result easier for downstream users to apply directly.

Thus the unconditional mathematical closure is complete at 0420, but the declaration sequence continues with a public wrapper and additional facade theorems that follow it.
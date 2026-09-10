# 0372 `goldenZeroSectorLift`

## Declaration kind

`def`

## Lean code

```lean
/--
The quadratic re-entry map used in the golden-order exponent-five descent.  Its
norm is the quartic occurring in the second coordinate of a golden fifth
power, while its second coordinate is a square.
-/
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

## Lean type

```lean
goldenZeroSectorLift : GoldenInt → GoldenInt
```

If an input `x : GoldenInt` has coordinates

```lean
x.fst : ℤ
x.snd : ℤ
```

then the output is

```lean
⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2,
  x.snd ^ 2⟩
```

Writing $x=(r,s)$ mathematically, this defines the quadratic map

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr).
$$

## Mathematical meaning of the declaration

This is not a theorem proving a proposition. It is the **definition of the re-entry map itself** used throughout the zero-sector descent.

It combines the first coordinate

$$
r^2+rs+s^2
$$

with the second coordinate

$$
s^2
$$

to form a new golden integer.

The reason for this particular shape becomes explicit in the following theorem

```lean
goldenZeroSectorLift_norm
```

which proves

$$
\operatorname{Norm}(T(r,s))
=
H(r,s),
$$

where $H(r,s)$ is the quartic factor `goldenFifthSndFactor r s` appearing in the second coordinate of a golden fifth power.

Thus the map implements the **algebraic re-entry** that converts a quartic condition on integer coordinates back into a norm condition in the golden order.

## Role in the full proof

Up through 0371 `goldenUnitClassesModFifth`, the development has finished classifying every golden unit into one of five sectors modulo fifth powers.

With `goldenZeroSectorLift`, the proof enters `SignedGoldenZeroSectorDescent.lean` and begins the strict descent used to eliminate the zero sector.

For a zero-sector packet with base coordinates $x=(r,s)$, the first step is to construct

$$
T(r,s)=\bigl(r^2+rs+s^2,s^2\bigr)
$$

as a golden integer. Subsequent results prove

$$
\operatorname{Norm}(T(r,s))
=
\texttt{goldenFifthSndFactor}(r,s),
$$

and, when that norm is a fifth power, use relative-prime factorization to recover a fifth root

$$
T(r,s)=\gamma^5.
$$

That root is then used to build a new descent packet whose visible measure is strictly smaller.

Accordingly, this definition is the entry point of the recursive circuit

$$
\text{zero-sector arithmetic}
\longrightarrow
\text{golden norm factorization}
\longrightarrow
\text{new fifth-power root}
\longrightarrow
\text{strict descent}.
$$

## Direct dependencies

### `GoldenInt`

This is the input and output type of the definition. The code shows that it has two coordinates accessible through `fst` and `snd`.

The definition constructs a new value directly with constructor notation

```lean
⟨..., ...⟩.
```

### Integer addition, multiplication, and powers

The coordinate expressions

```lean
x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2
x.snd ^ 2
```

use `+`, `*`, and natural-number exponentiation over `ℤ`.

The `def` itself invokes no other FLT5-specific theorem.

### Immediate downstream users

The first declaration that unfolds this definition is

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

followed by

```lean
theorem goldenZeroSectorLift_norm
```

which identifies its norm with the quartic factor.

These are not dependencies of the definition; they are its first users.

## Construction flow

The body is only one line, but its structure is precise.

### 1. Build the first coordinate

```lean
x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2
```

which is mathematically

$$
r^2+rs+s^2.
$$

### 2. Square the second coordinate

```lean
x.snd ^ 2
```

which is

$$
s^2.
$$

### 3. Assemble a `GoldenInt`

```lean
⟨..., ...⟩
```

constructs the new golden integer from the two integer coordinates.

No proof tactic is involved; this is a completely computational definition.

## Lean-specific processing

### Projections `fst` / `snd`

`x.fst` and `x.snd` directly extract the two coordinates of `GoldenInt`.

### Anonymous constructor notation

```lean
⟨a, b⟩
```

uses the expected type `GoldenInt` to infer the appropriate constructor.

### `^ 2`

This is exponentiation by a natural-number exponent. Since the coordinates live in `ℤ`, these are squares in the integer ring.

### Definitional equality

The immediately following theorem

```lean
goldenZeroSectorLift_snd
```

is proved by `rfl` alone because the second coordinate is literally defined as `x.snd ^ 2`.

This is an important API design property: downstream code can expose the coordinate through a named rewrite theorem while preserving definitional simplicity.

## Redundancy and duplication

There is essentially no redundancy in the definition itself.

Mathematically, however, the first-coordinate form

$$
r^2+rs+s^2
$$

is a natural quadratic form in the golden-order development and may occur elsewhere. If the repository already contains an exact helper definition for this form, reusing it could reduce duplication.

The standalone excerpt inspected here is not enough to establish whether such an exact helper already exists, so this remains only an optimization candidate.

## Optimization candidates

### 1. Name the coordinate quadratic form

One possible refactoring would be

```lean
def goldenQuadraticForm (r s : ℤ) : ℤ :=
  r ^ 2 + r * s + s ^ 2
```

and then

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨goldenQuadraticForm x.fst x.snd, x.snd ^ 2⟩.
```

This is worthwhile only if the same quadratic form is reused enough elsewhere. If it is local to the descent, the current inline expression is easier to trace.

### 2. Add a first-coordinate API theorem

Since `goldenZeroSectorLift_snd` is provided immediately afterwards, one could also add

```lean
theorem goldenZeroSectorLift_fst ...
```

if the first coordinate is frequently rewritten directly.

If downstream arguments mostly use `goldenZeroSectorLift_norm`, however, such a lemma would add API surface without much benefit.

### 3. Avoid inappropriate homomorphism abstraction

This transformation is quadratic, not additive or multiplicative. It therefore should not be forced into a ring-homomorphism abstraction.

Keeping it as a named descent-specific transformation is structurally appropriate.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

but the body of this `def` itself only needs

- the definition of `GoldenInt`,
- the integer type `ℤ`,
- basic addition and multiplication,
- natural-number exponentiation.

No advanced Mathlib tactic is used by this declaration.

Therefore `import Mathlib` is much broader than necessary for this declaration in isolation.

In the real module, however, the relevant minimal imports are determined by the DkMath module that defines `GoldenInt` together with all the theorems and tactics used elsewhere in `SignedGoldenZeroSectorDescent.lean`. The exact minimal import set has not been verified here because no Lean build was run.

Import reduction should therefore be performed at module granularity rather than from this one definition alone.

## Comparator challenge suitability

**Yes, but by itself it is only a very small construction challenge.**

Given the two-coordinate `GoldenInt` structure, a challenge could ask for

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ?_
```

implementing

$$
(r,s)\mapsto(r^2+rs+s^2,s^2).
$$

That tests almost no proof search.

A better Comparator challenge would group declarations 0372 through 0374:

1. define `goldenZeroSectorLift`,
2. prove its second-coordinate theorem by `rfl`,
3. prove `goldenZeroSectorLift_norm` by expansion and `ring`.

That combination tests structure construction, definitional equality, unfolding, and polynomial normalization in one compact problem.

## Technical significance

This definition is one of the algebraic-geometric cores of the zero-sector descent.

It sends

$$
(r,s)
\longmapsto
\bigl(r^2+rs+s^2,s^2\bigr)
$$

so that a quartic factor arising in fifth-power coordinates can be reinterpreted as the norm of a golden integer.

It is therefore not merely a substitution of auxiliary variables; it is a recoding between

$$
\text{quartic integer expression}
\longleftrightarrow
\text{quadratic-order norm}.
$$

That recoding allows the proof to reuse unit classification and coprime factorization, return the zero-sector problem to a fifth-power form of the same kind, and then decrease the descent measure.

Within the DkMath FLT5 architecture, this is where the completed unit-classification phase hands control to the recursive geometry of the zero-sector descent.

## Next declaration to read

The next declaration is **`goldenZeroSectorLift_snd`**.

Its declaration kind is `theorem`.

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

It exposes the second coordinate of the new definition as a public rewrite fact and is later used in five-divisibility and norm-difference calculations.
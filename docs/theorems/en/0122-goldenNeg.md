# 0122 — `goldenNeg`

## Lean type

```lean
def goldenNeg (x : GoldenInt) : GoldenInt := ⟨-x.fst, -x.snd⟩
```

`goldenNeg` is a unary operation on `GoldenInt`, introduced in 0118, that negates each of its two integer coordinates.

If `GoldenInt` is read as

$$
x=a+b\varphi,
$$

then the definition corresponds to

$$
goldenNeg(x)=(-a)+(-b)\varphi.
$$

## Mathematical statement

This declaration is a definition rather than a theorem. It defines the additive inverse candidate in golden-integer coordinates by

$$
-(a,b)=(-a,-b).
$$

At this point the standard `Neg GoldenInt` instance has not yet been introduced. Later the source registers

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

so that the notation `-x` refers to `goldenNeg x`.

## Role in the overall proof

Where 0121 `goldenAdd` fixes addition, 0122 `goldenNeg` fixes the inverse operation for that addition.

The immediately following declaration

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

directly reuses this definition, so subtraction is implemented through the usual ring identity

$$
x-y=x+(-y).
$$

Later, the construction of `AddCommGroup GoldenInt` reduces the inverse laws to the corresponding integer laws in each coordinate. Thus `goldenNeg` is one of the primitive operations that turns `GoldenInt` from a bare coordinate carrier into an additive group.

It does not directly mention the FLT5 five-adic branches or the golden norm, but the later commutative-ring, conjugation, divisibility, Euclidean-domain, unit-classification, and fifth-power-factorization layers all rely on this additive structure.

## Direct dependencies

The direct dependency surface is small.

- `GoldenInt` — input and output type.
- `GoldenInt.fst`, `GoldenInt.snd` — projections to the two integer coordinates.
- Unary negation on `ℤ`.
- The `GoldenInt` constructor used by `⟨..., ...⟩`.

It does not directly depend on any theorem, five-adic lemma, or golden-norm lemma.

Its principal direct consumers are `goldenSub`, the `Neg GoldenInt` instance, `AddCommGroup GoldenInt`, and the coordinate simp lemmas for negation.

## Proof / construction flow

There is no proof script. The definition itself is the computation rule.

1. Negate `x.fst` as an integer.
2. Negate `x.snd` as an integer.
3. Pass the two results to the `GoldenInt` constructor.

Thus unfolding

```lean
goldenNeg x
```

reduces definitionally to

```lean
⟨-x.fst, -x.snd⟩.
```

After the `Neg GoldenInt` instance is installed, projection lemmas for negation are therefore designed to close essentially by `rfl`.

## Lean-specific processing

### Structure projections

`x.fst` and `x.snd` are projected directly and manipulated in `ℤ`; no quotient or coercion layer is involved.

### Constructor inference from the expected type

Because the return type is known to be `GoldenInt`,

```lean
⟨-x.fst, -x.snd⟩
```

is elaborated as `GoldenInt.mk (-x.fst) (-x.snd)`.

### Overloaded negation

The expressions `-x.fst` and `-x.snd` are interpreted as integer negation. No `Neg GoldenInt` instance is needed yet, so no circular definition arises.

### Definitional equality

`goldenNeg` is a definition, not an opaque theorem. After unfolding, coordinate computations are available by definitional equality, which keeps the later simp API lightweight.

### Separation of raw and typeclass operations

The source first defines the explicit operation `goldenNeg` and only later registers it as `Neg GoldenInt`. This follows the same design pattern as 0119 `goldenZero`, 0120 `goldenOne`, and 0121 `goldenAdd`.

## Redundancy and duplication

The body itself contains no internal redundancy.

At the API level, however, the later

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

means that both the raw API `goldenNeg x` and standard notation `-x` refer to the same operation.

This is intentional rather than logically redundant: it separates an auditable explicit coordinate layer from Mathlib's typeclass layer.

Also, `goldenSub` is defined as `goldenAdd x (goldenNeg y)` rather than re-expanding subtraction coordinates as

```lean
⟨x.fst - y.fst, x.snd - y.snd⟩,
```

which is itself a useful avoidance of duplication.

## Optimization candidates

### 1. Inline directly into the `Neg` instance

One could write

```lean
instance : Neg GoldenInt :=
  ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
```

and remove one named declaration. This would shorten the file, but it would weaken the explicit primitive coordinate API and make early reuse by declarations such as `goldenSub` more dependent on typeclass setup.

### 2. Define `goldenSub` directly by coordinates

Subtraction could instead be defined as

```lean
⟨x.fst - y.fst, x.snd - y.snd⟩.
```

That is shorter locally, but it hides the algebraic dependency `x-y=x+(-y)` from the source. The present compositional definition is structurally cleaner.

### 3. Introduce a coordinatewise unary helper

For example,

```lean
def goldenMapCoords (f : ℤ → ℤ) (x : GoldenInt) : GoldenInt :=
  ⟨f x.fst, f x.snd⟩
```

could express negation through a generic helper. For a one-line operation, however, the abstraction cost is likely larger than the gain.

### 4. Construct the additive structure in one step

Another design could define `AddCommGroup GoldenInt` directly instead of exposing separate raw definitions for `Zero`, `Add`, and `Neg`. The current design is more transparent for auditing and keeps the primitive computation rules available by `rfl`.

## Required Mathlib imports and import optimization

The standalone source begins with

```lean
import Mathlib
```

for the generated file as a whole.

`goldenNeg` itself directly needs only `GoldenInt` and integer negation. It does not use `ring`, `omega`, `norm_num`, Euclidean-domain APIs, or number-field APIs.

Therefore importing all of `Mathlib` is clearly excessive for this declaration alone; a much smaller import providing integers and basic algebraic operations should suffice.

The complete `GoldenOrder.lean` module, however, later constructs `AddCommGroup`, `CommRing`, `Zsqrtd 5`, domain structure, and uses several tactics. The exact minimal module-level import set has not been checked by a Lean build here, so this remains an optimization candidate rather than a verified replacement.

## Comparator challenge suitability

**Suitable.** This is primarily an API-design comparison rather than a difficult proof-search problem.

Useful variants to compare are:

- define raw `goldenNeg` first and register `Neg` later, as in the current source;
- define `Neg GoldenInt` directly;
- route through a generic coordinatewise unary helper;
- construct `AddCommGroup GoldenInt` in one bundled step.

Evaluation criteria include transparency of definitional reduction, ease of `rfl`-based simp lemmas, clarity of dependency order, reliance on typeclass elaboration, and readability of the following `goldenSub` definition.

## Sources and explicit uncertainty

The formal source of truth is the `GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch.

The existing Japanese and English PDFs are treated as supporting narrative material, but the precise PDF page or section corresponding to `goldenNeg` was not directly checked for this article. No PDF-specific page number or wording is therefore inferred.

The import-minimization and helper-abstraction proposals are design candidates only; no Lean build was performed to validate them.

## Next declaration to read

The next declaration is

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

which composes 0121 addition with 0122 additive negation and defines golden-integer subtraction through

$$
x-y=x+(-y).
$$

In dependency order, 0123 `goldenSub` is the natural next article.

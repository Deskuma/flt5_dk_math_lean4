# 0127 — `instance : Zero GoldenInt`

## Lean type

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

This is not a named theorem but an anonymous instance that equips `GoldenInt` with Lean's standard `Zero` typeclass.

Article 0119 already defined

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

The present declaration connects that raw definition to Lean's standard notation

```lean
(0 : GoldenInt)
```

## Mathematical statement

`GoldenInt` represents a golden integer in coordinates

$$
x=a+b\varphi.
$$

Its zero element is

$$
0=0+0\varphi,
$$

so its coordinate pair is

$$
(0,0).
$$

The instance itself proves no new mathematical proposition. It registers the element already chosen by 0119 `goldenZero` as the carrier of the algebraic typeclass `Zero GoldenInt`.

Thus its mathematical content is exactly the definitional choice that the zero of the golden integer order has coordinates $(0,0)$.

## Role in the overall proof

Articles 0120–0125 constructed the raw API `goldenOne`, `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`. Article 0126 `GoldenInt.ext` prepared coordinatewise decomposition of equality proofs.

From here, those raw operations are connected one by one to the standard algebraic API understood by Lean and Mathlib.

Once this instance is available, writing

```lean
0
```

in a context expecting `GoldenInt` refers to `goldenZero`. It is immediately followed by

```lean
instance : One GoldenInt := ⟨goldenOne⟩
instance : Add GoldenInt := ⟨goldenAdd⟩
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩
```

and later by `AddCommGroup GoldenInt`, `CommRing GoldenInt`, and `IsDomain GoldenInt`.

Therefore this declaration is the first adapter that begins lifting the coordinate model `GoldenInt` into Mathlib's ordinary algebraic hierarchy.

## Direct dependencies

The direct dependency set is very small.

1. `GoldenInt`
2. `goldenZero`
3. Lean / Mathlib's `Zero` typeclass

In particular, it does not logically depend on 0126 `GoldenInt.ext`, `goldenAdd`, or `goldenMul`. The source order instead follows a design in which the raw API is completed first and typeclass registration begins afterward.

## Proof flow

There is no tactic proof. The declaration body

```lean
⟨goldenZero⟩
```

is passed directly to the constructor of the `Zero GoldenInt` structure.

Conceptually there is only one step:

1. provide `goldenZero : GoldenInt`;
2. store it in the `zero : GoldenInt` field required by `Zero GoldenInt`.

Lean's notation resolution can then interpret

```lean
(0 : GoldenInt)
```

as `goldenZero` through `Zero.zero`.

## Lean-specific processing

### 1. Typeclass instance registration

Because the declaration is registered with `instance`, typeclass synthesis automatically finds `Zero GoldenInt`; callers do not need to pass it explicitly.

From this point onward, `0` can be used whenever the expected type is `GoldenInt`.

### 2. Constructor notation `⟨goldenZero⟩`

`Zero α` is a small typeclass structure containing a zero element. Since the expected type is already known to be `Zero GoldenInt`, Lean elaborates

```lean
⟨goldenZero⟩
```

as the constructor expression filling its principal field.

### 3. Definitional equality

The instance stores `goldenZero` directly, so the later lemmas

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

close by `rfl`.

This is an important design advantage: no theorem-level rewrite is inserted between standard `0` and the raw coordinate zero; kernel reduction alone exposes the coordinates.

### 4. Notation resolution

The literal `0` is polymorphic, and its interpretation depends on the expected type and the corresponding numeral/zero machinery. Here this instance provides the foundational interpretation of zero for `GoldenInt`.

## Redundancy and duplication

Article 0119 `goldenZero` and the present instance appear to encode the same information twice:

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

Technically the instance could instead be written directly as

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

However, the current design separates the raw API from the standard typeclass API. Later standalone calculations can refer explicitly to `goldenZero`, while Mathlib's algebraic hierarchy can use `0`. This is therefore intentional API-layer duplication rather than mere waste.

## Optimization candidates

### Candidate A — keep the current design

This is the clearest option. The boundary between the raw coordinate definition and standard algebra notation is visible in one line.

### Candidate B — inline into the instance

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

and remove `goldenZero`.

This reduces code size, but loses the explicit `goldenZero` API and the symmetry of the raw primitive definitions.

### Candidate C — bundle the standard algebraic structure earlier

Instead of registering `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` individually, one could provide them as part of a larger `AddCommGroup` or `CommRing` construction.

The current staged design, however, makes definitional equalities for each primitive operation easy to audit and is especially transparent for theorem-museum reading.

### Candidate D — use a named instance

Giving the anonymous instance an explicit name would improve source navigation and explicit reference in debugging or comparisons. Ordinary typeclass synthesis does not require this, so it is optional rather than necessary.

## Required Mathlib import and import optimization candidates

The standalone source uses

```lean
import Mathlib
```

for the entire generated file.

This declaration by itself needs only `GoldenInt`, `goldenZero`, the `Zero` typeclass, and basic instance machinery. It is therefore unlikely that the whole of `Mathlib` is required solely for this line.

At the file level, however, the immediately following source builds `One`, `Add`, `Neg`, `Sub`, `Mul`, `AddCommGroup`, and `CommRing`, so the minimum import set for the modular file cannot be inferred from this one declaration alone.

The exact smallest module import has not been verified by a Lean build in this article, so no specific fine-grained import is asserted.

## Comparator challenge suitability

 **Suitable, but best as a small design challenge.**

Possible variants include:

1. raw `goldenZero` plus a separate `Zero` instance;
2. inline coordinates in the instance;
3. a named instance;
4. bundling primitive instances as part of a `CommRing` construction.

Evaluation criteria include definitional equality, source readability, separation between raw and typeclass APIs, transparency of typeclass synthesis, brevity of later `rfl` lemmas, and import footprint.

A particularly useful comparison is which design keeps `(0 : GoldenInt).fst = 0` provable by `rfl`.

## Correspondence with existing material

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` as existing narrative material.

This article did not directly analyze the exact PDF page or section corresponding to the anonymous `Zero GoldenInt` instance. Therefore no PDF-specific explanation, page number, or section number is guessed.

The formal source of truth is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The immediately following declaration is

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

Article 0127 connects the raw zero to standard `0`. The next step is to connect 0120 `goldenOne` to standard `1`, then continue through the additive, negation, subtraction, and multiplication instances.
# 0128 — `instance : One GoldenInt`

## Lean type

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

This anonymous instance gives `GoldenInt` the standard Lean / Mathlib `One` typeclass. Article 0120 already defined `goldenOne : GoldenInt := ⟨1, 0⟩`, so this declaration connects that raw coordinate value to the standard notation `(1 : GoldenInt)`.

## Mathematical statement

`GoldenInt` represents a golden integer as

$$
x=a+b\varphi,
$$

with

$$
\varphi^2=\varphi+1.
$$

The multiplicative identity is

$$
1=1+0\varphi,
$$

so its coordinates are $(1,0)$. The instance proves no new proposition; it registers the already defined `goldenOne` as the `one` field of `One GoldenInt`.

## Role in the full proof

Article 0127 connected `goldenZero` to standard `0`; this declaration symmetrically connects `goldenOne` to standard `1`. The source immediately continues with the `Add`, `Neg`, `Sub`, and `Mul` instances, and later builds `AddCommGroup GoldenInt`, `CommRing GoldenInt`, and the divisibility and Euclidean-domain layers.

The source also proves

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

so this adapter preserves direct coordinate reduction. It also complements 0125 `goldenPow`, whose zero-exponent case uses the raw `goldenOne`; after the standard algebra API is installed, raw and standard unit notation agree definitionally.

## Direct dependencies

1. `GoldenInt`
2. `goldenOne`
3. Lean / Mathlib's `One` typeclass

It does not logically depend on `goldenZero`, `goldenAdd`, `goldenMul`, or `GoldenInt.ext`.

## Proof flow

There is no proof script. The expression

```lean
⟨goldenOne⟩
```

constructs `One GoldenInt` by placing `goldenOne : GoldenInt` in its `one : GoldenInt` field. In a context expecting `GoldenInt`, the notation `1` is then resolved to this value by typeclass synthesis.

## Lean-specific processing

### 1. Typeclass registration

Because this is an `instance`, later code can use `1` at type `GoldenInt` without passing a `One GoldenInt` value explicitly.

### 2. Constructor elaboration

The expected type is known to be `One GoldenInt`, so `⟨goldenOne⟩` is elaborated as the structure constructor filling the `one` field.

### 3. Overloaded numeral `1`

The numeral `1` is polymorphic. Once this instance exists, `1` in a `GoldenInt` context denotes the coordinate value $(1,0)$.

### 4. Definitional equality

Because the instance stores `goldenOne` directly, `(1 : GoldenInt).fst` reduces to `1` and `(1 : GoldenInt).snd` reduces to `0`. The later projection lemmas therefore close by `rfl` rather than by theorem-level rewriting.

### 5. Raw API and standard API

`goldenOne` is the explicitly named raw coordinate value. This instance exposes the same value through standard algebraic notation. The two layers are connected definitionally.

## Redundancy and duplication

The pair

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

contains the same mathematical data in two API layers. It could be shortened to an inline coordinate instance, but the current design lets `goldenPow` use `goldenOne` before the standard typeclass registrations are introduced. The duplication therefore supports the chosen bootstrap order.

The declaration is also structurally parallel to 0127 `Zero GoldenInt`, which makes the two basic constants easy to audit.

## Optimization candidates

### Candidate A — keep the current design

This keeps the raw/standard boundary explicit, preserves the bootstrap order, and retains the later `rfl` coordinate lemmas.

### Candidate B — inline the coordinates

```lean
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
```

This removes one named definition, but a separate raw base value would still be needed if `goldenPow` remains earlier in the source.

### Candidate C — introduce an integer embedding helper

A helper such as

```lean
def goldenOfInt (n : ℤ) : GoldenInt := ⟨n, 0⟩
```

could generate both zero and one. This may be attractive if the integer embedding becomes an important downstream API.

### Candidate D — bundle primitive instances later

`Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` could be introduced together with a larger algebra structure. The current staged construction is more transparent for coordinate-level auditing.

### Candidate E — use a named instance

A named instance could help explicit source navigation and import diagnostics, although ordinary typeclass use does not require it.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

for the whole generated file. This declaration itself requires only `GoldenInt`, `goldenOne`, `One`, and basic instance machinery, so the whole umbrella import is not justified by this line alone.

The surrounding `GoldenOrder` section soon builds `AddCommGroup`, `CommRing`, and `IsDomain`, so the true file-level minimum cannot be inferred from this declaration alone. No Lean build is run in this museum pass; exact minimal module names remain unverified.

## Comparator challenge suitability

 **Suitable for a small API-design comparison.**

Possible variants include a separate raw definition plus instance, inlining coordinates, using an integer embedding helper, bundling primitive operations later, and anonymous versus named instances. Evaluation criteria include definitional equality of coordinate projections, bootstrap simplicity for `goldenPow`, readability of the raw/standard boundary, typeclass behavior, and import footprint.

## Correspondence with existing material

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

In this pass, retrieval of the PDF bodies did not expose their contents, so no PDF page number or PDF-specific wording is guessed. The formal source of truth for this article is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The immediately following declaration is

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

Articles 0127 and 0128 have now installed the standard constants `0` and `1`. The next step is to connect 0121 `goldenAdd` to standard addition `x + y`.
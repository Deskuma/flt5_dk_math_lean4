# 0129 — `instance : Add GoldenInt`

## Lean type

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

This is not a theorem but an anonymous instance giving `GoldenInt` the standard Lean / Mathlib binary-addition typeclass `Add`.

Article 0121 already defined

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

and this declaration connects that raw coordinate operation to the standard notation

```lean
x + y
```

## Mathematical statement

Read

$$
x=a+b\varphi,
$$

$$
y=c+d\varphi,
$$

with

$$
\varphi^2=\varphi+1.
$$

Then addition is

$$
x+y=(a+c)+(b+d)\varphi,
$$

so in coordinates

$$
(a,b)+(c,d)=(a+c,b+d).
$$

The instance proves no new equality. It registers the coordinate addition already defined by 0121 `goldenAdd` as the `add` field of `Add GoldenInt`, identifying it with Lean's standard `+` notation.

## Role in the full proof

After Articles 0127 and 0128 introduced standard `0` and `1`, this declaration installs the first standard binary operation on `GoldenInt`.

The source immediately continues with

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩
```

so the raw arithmetic API is connected piece by piece to Lean's algebra hierarchy.

The source then gives

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

These close by `rfl` precisely because the instance stores `goldenAdd` directly in the `add` field.

Later,

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

builds the additive commutative-group structure. This declaration is the earlier boundary that fixes the meaning of standard `+` to be the raw coordinate addition.

Across the FLT5 development, standard addition is needed before moving into conjugation, norm, divisibility, Euclidean-domain structure, and fifth-power factorization. Thus this tiny declaration is a foundational API boundary for the algebraic hierarchy that follows.

## Direct dependencies

The direct dependencies are only:

1. `GoldenInt`
2. `goldenAdd`
3. Lean / Mathlib's `Add` typeclass

It does not logically depend on `goldenZero`, `goldenOne`, `goldenNeg`, `goldenSub`, `goldenMul`, or `GoldenInt.ext`.

At the source-organization level, however, the carrier, raw zero/one/add/neg/sub/mul/pow operations, and extensionality theorem are defined first, after which the standard typeclass instances are registered together.

## Proof flow

There is no proof script. The body

```lean
⟨goldenAdd⟩
```

constructs `Add GoldenInt` directly.

Conceptually there is one step:

1. Put `goldenAdd : GoldenInt → GoldenInt → GoldenInt` into the `add` field of `Add GoldenInt`.

After that, in a `GoldenInt` context,

```lean
x + y
```

is resolved by typeclass synthesis to `goldenAdd x y`.

## Lean-specific processing

### 1. Typeclass registration

Because this is an `instance`, later code can use `x + y` without passing an explicit `Add GoldenInt`. Lean's typeclass synthesis resolves this declaration automatically.

### 2. Constructor notation `⟨goldenAdd⟩`

`Add α` is a typeclass structure containing the binary operation

```lean
add : α → α → α
```

Since the expected type is known to be `Add GoldenInt`, Lean elaborates `⟨goldenAdd⟩` as the constructor expression filling its single field.

### 3. Overloaded notation `+`

`+` is polymorphic and type-directed. After this instance is available,

```lean
x + y
```

at type `GoldenInt` means `goldenAdd x y`.

### 4. Definitional equality

Because `goldenAdd` is registered directly,

```lean
(x + y).fst
```

kernel-reduces to

```lean
x.fst + y.fst
```

and similarly `.snd` reduces to `x.snd + y.snd`.

Hence

```lean
@[simp] theorem golden_fst_add ... := rfl
@[simp] theorem golden_snd_add ... := rfl
```

need no theorem-level rewrite.

### 5. Raw API versus standard API

`goldenAdd` is the explicitly named raw coordinate operation; the `+` introduced here is the standard Mathlib-facing API. Their definitional identification keeps both low-level coordinate calculations and high-level algebraic structure simple.

### 6. Instance construction order

`Add GoldenInt` is registered before `AddCommGroup GoldenInt`. This allows the source to use standard `+` in projection lemmas and subsequent structure-law proofs at an early stage.

The later `goldenAddCommGroup` still refers explicitly to raw `goldenAdd`, which suggests that definitional transparency during bootstrap is being preferred over a fully bundled construction from the beginning.

## Redundancy and duplication

Article 0121 and this declaration encode the same mathematical operation in two API layers:

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt := ...
instance : Add GoldenInt := ⟨goldenAdd⟩
```

Technically the coordinate formula could be inlined into the instance:

```lean
instance : Add GoldenInt :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
```

The present separation, however, has concrete advantages:

- raw arithmetic can be bootstrapped before the typeclass hierarchy;
- `goldenAdd` remains explicitly reusable;
- the correspondence between standard `+` and the raw operation is easy to audit;
- coordinate projection lemmas remain definitionally transparent.

Articles 0127 `Zero`, 0128 `One`, this 0129 `Add`, and the following `Neg` / `Sub` / `Mul` instances repeat the same adapter pattern. This is syntactic duplication, but it also exposes a useful one-to-one mapping from raw operations to standard typeclasses.

## Optimization candidates

### Candidate A — keep the current design

This is the most auditable version. The correspondence between `goldenAdd` and `+` is visible in one line, and the projection lemmas remain `rfl`.

### Candidate B — inline the operation in the instance

Eliminate `goldenAdd` and place the coordinate formula directly in the `Add` instance.

This reduces declaration count but disrupts the current bootstrap design in which raw operations exist before the standard typeclass layer. Any downstream explicit uses of `goldenAdd` would also need rewriting.

### Candidate C — introduce a primitive-operation bundle

Zero, one, add, neg, sub, and mul could be grouped into a custom structure from which standard instances are generated.

At the current scale, however, the abstraction cost may exceed the benefit.

### Candidate D — obtain `Add` from `AddCommGroup`

One could construct `AddCommGroup GoldenInt` first and obtain `Add` as part of that bundle.

This can complicate bootstrap dependencies when standard `+` is useful while proving the additive-group laws themselves. The staged registration used here avoids that circularity cleanly.

### Candidate E — use a named instance

A named instance can help Comparator experiments, import debugging, and explicit `#synth` investigations, although normal use through typeclass synthesis does not require it.

### Candidate F — generate projection simp lemmas

`golden_fst_add` and `golden_snd_add` are definitionally trivial. A small generation pattern for projection simp lemmas over the raw operation family could reduce repetition, although handwritten lemmas remain easier to inspect at this scale.

## Required Mathlib imports and import optimization

The target standalone artifact uses

```lean
import Mathlib
```

for the complete generated file.

This declaration itself only needs `GoldenInt`, `goldenAdd`, the `Add` typeclass, and basic instance machinery. The umbrella `Mathlib` import is therefore not justified by this line alone.

The surrounding `GoldenOrder` section soon constructs `AddCommGroup`, `CommRing`, and `IsDomain`, so the true file-level minimal import set cannot be determined from this declaration in isolation.

No Lean build is performed in this museum pass, so exact minimal Mathlib module names remain unverified rather than being guessed.

A sensible import Comparator experiment would isolate `GoldenOrder`, remove the umbrella import, and add only the modules required by failed names or instances until the section closes again.

## Comparator challenge suitability

 **Suitable as a small but meaningful bootstrap/API-design challenge.**

Possible variants include:

1. raw `goldenAdd` plus a separate `Add` instance;
2. coordinate formula inlined into the instance;
3. obtaining `Add` from an early `AddCommGroup` bundle;
4. generating instances from a custom primitive-operation bundle;
5. anonymous versus named instance.

Evaluation criteria include:

- whether `(x + y).fst` and `.snd` still reduce by `rfl` to the expected coordinates;
- whether bootstrap dependencies remain acyclic;
- whether `goldenAdd` can still be reused explicitly;
- whether the raw/standard correspondence remains easy to audit;
- typeclass-synthesis stability;
- import footprint.

In particular, deciding when to introduce standard `+` while keeping bootstrap dependencies minimal is a useful formal-library design comparison.

## Correspondence with existing material

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

Their existence was verified in GitHub during this pass. The specific PDF page or section corresponding to `Add GoldenInt` was not directly inspected, so no page number or PDF-specific wording is guessed.

The formal source of truth for this article is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The immediately following declaration is

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

With standard addition `+` now available, the next step is to connect Article 0122 `goldenNeg` to standard unary negation `-x`, installing the standard API for additive inverses.
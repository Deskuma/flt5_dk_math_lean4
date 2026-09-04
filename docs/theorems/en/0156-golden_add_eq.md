# 0156 — `golden_add_eq`

## Lean type

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

This is a `theorem` exposing the definitional identity between the raw operation `goldenAdd` and the standard notation `x + y` obtained through the `Add GoldenInt` instance. The theorem is also registered with `@[simp]`.

## Mathematical statement and meaning of the declaration

Read

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

The upstream raw operation `goldenAdd` implements coordinatewise addition,

$$
goldenAdd(x,y)=(a+c)+(b+d)\varphi.
$$

On the other hand, standard notation `x + y` is interpreted through the previously registered instance

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

and therefore refers to the very same function.

Thus this theorem does not establish a new algebraic identity. It exposes

$$
\texttt{goldenAdd x y}=x+y
$$

as a named reusable rewrite rule connecting the raw API to the standard algebra API.

## Role in the overall proof

By 0155, `GoldenInt` has entered Mathlib's standard algebra hierarchy through `CommRing`, `NoZeroDivisors`, `Nontrivial`, and `IsDomain`. Starting with 0156, the development turns to cleaning up the boundary between that abstract interface and the explicit coordinate API used during construction.

This bridge means that downstream code written using `goldenAdd` can be normalized by simp to standard `+` notation. Conversely, the formalization may retain the raw operation for auditability while allowing later generic algebraic arguments to use the conventional interface.

In the source, this theorem is immediately followed by `golden_neg_eq`, `golden_sub_eq`, `golden_mul_eq`, and `golden_pow_eq`. Therefore 0156 is the first member of a consecutive raw-operation equivalence block covering addition, negation, subtraction, multiplication, and powers.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- Lean's standard `Add` notation
- reflexivity `rfl`

Mathematically the statement depends on the coordinate addition definition, but the proof term itself is only `rfl`. No associativity, commutativity, or other additive-group theorem is needed directly because `x + y` is definitionally implemented by `goldenAdd x y`.

## Proof / construction flow

The proof closes in one step:

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

Lean expands the right-hand side `x + y` through the `Add GoldenInt` instance. Since the operation stored in that instance is `goldenAdd`, the two sides become definitionally identical and reflexivity closes the theorem.

Conceptually, the theorem fixes a named identity

$$
\text{raw function}
\longleftrightarrow
\text{typeclass notation}.
$$

## Lean-specific processing

The important Lean feature is the combination of definitional equality and the `@[simp]` attribute.

Because the equality is definitional, the theorem could be omitted and individual proofs could use unfolding or `dsimp`. Registering it as a simp theorem instead gives the simplifier an explicit normalization rule from

```lean
goldenAdd x y
```

to

```lean
x + y.
```

The rewrite direction matters: raw implementation syntax is normalized toward standard notation. This keeps downstream algebraic simplification in Mathlib's conventional language and makes the dedicated golden-coordinate API easier to treat as an implementation layer.

## Redundancy and duplication

From the perspective of pure logical information, the theorem is redundant: the equality already follows by unfolding the instance.

Nevertheless it has a genuine API role:

- it bridges the raw operation name to standard notation;
- it explicitly chooses a simp normalization direction;
- it reduces the need for downstream proofs to unfold the internals of an instance;
- it can serve as a compatibility boundary if the implementation of the standard operation is later reorganized.

Thus the declaration is mathematically redundant but API-useful.

## Optimization candidates

Possible alternatives are:

1. Keep the present `@[simp] theorem ... := rfl` design.
2. Remove the theorem and unfold the `Add` instance where necessary.
3. Hide the raw operation after structure construction and use only standard notation downstream.
4. Group `golden_add_eq` through `golden_pow_eq` explicitly as an API-bridge section.

Because this formalization deliberately keeps an auditable explicit-coordinate layer, options 1 or 4 are the most natural. Saving one line is less valuable than preserving a visible boundary between the raw layer and the standard algebra layer.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself uses no advanced Mathlib result; directly it needs `GoldenInt`, `goldenAdd`, the `Add GoldenInt` instance, the `@[simp]` attribute, and ordinary equality machinery.

Therefore it is unlikely that all of `Mathlib` is required solely for 0156. The true minimum import set is governed by the entire `GoldenOrder` module, which also uses algebra typeclasses, `ring`, `omega`, `norm_num`, `Zsqrtd`, and related infrastructure.

No Lean build is run in this museum pass, so the exact minimum import set remains unverified and should be treated as an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. The comparison would concern API normalization strategy rather than a mathematical algorithm.

Candidate designs include:

- the current explicit `@[simp]` bridge theorem;
- unfolding the raw operation or instance at every use site;
- hiding the raw API and using only standard notation after structure construction.

Useful metrics are simp stability, proof-script size, robustness under definition changes, readability of errors, auditability of the explicit coordinate layer, and notation consistency in downstream theorems.

This makes a small but clear Comparator challenge for measuring the value of retaining an `rfl`-provable bridge theorem.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, `golden_add_eq` appears immediately after 0155 `IsDomain GoldenInt` and begins a consecutive group of raw-operation equivalence theorems.

The standalone artifact lists `DkMath/FLT/Five/GoldenOrder.lean` among its ordered source modules and uses `import Mathlib` globally.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The concrete PDF page or section corresponding to this small API theorem was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

Where 0156 connects raw addition to standard addition, 0157 will expose the same definitional agreement between raw negation `goldenNeg` and the standard unary minus `-x`.
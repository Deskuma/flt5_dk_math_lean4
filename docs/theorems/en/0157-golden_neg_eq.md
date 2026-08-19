# 0157 — `golden_neg_eq`

## Lean type

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

This is a `theorem` exposing the definitional identity between the raw operation `goldenNeg` and the standard unary minus `-x` obtained through the `Neg GoldenInt` instance. It is registered as a `@[simp]` theorem.

## Mathematical statement and meaning of the declaration

Read an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

The upstream raw operation `goldenNeg` implements coordinatewise additive negation,

$$
goldenNeg(x)=(-a)+(-b)\varphi.
$$

On the other hand, the standard notation `-x` is interpreted through the already registered instance

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

and therefore refers to exactly the same function.

Thus this theorem proves no new algebraic law. It exposes the agreement

$$
\texttt{goldenNeg x}=-x
$$

between the raw API and the standard algebra API as a named simp rewrite rule.

## Role in the overall proof

By 0155, `GoldenInt` has entered Mathlib's standard algebra hierarchy through `IsDomain`. Starting with 0156, the development enters a block that cleans up the boundary between the raw coordinate API and standard notation. This theorem is the second member of that block, following 0156 `golden_add_eq`, and normalizes raw negation to the standard `Neg.neg` notation.

The bridge allows the explicit bootstrap operation `goldenNeg` to remain visible for auditability while downstream proofs can use the generic additive-group and ring API centered on `-x`. Since `goldenSub` was itself defined using `goldenAdd x (goldenNeg y)`, this theorem also leads naturally into the next bridge `golden_sub_eq`.

In source order, `golden_add_eq`, `golden_neg_eq`, `golden_sub_eq`, `golden_mul_eq`, and `golden_pow_eq` form a consecutive raw-operation bridge block. The present theorem is the negation member of that sequence.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- Lean's standard `Neg` notation
- reflexivity `rfl`

The raw definition `goldenNeg` negates each integer coordinate of `GoldenInt`. The proof term of this theorem is only `rfl`; additive-group results such as cancellation laws are not needed directly.

## Proof / construction flow

The proof closes in one step:

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

Lean elaborates the right-hand side `-x` using the `Neg GoldenInt` instance. Since that instance stores `goldenNeg` as its operation, unfolding the right-hand side produces exactly `goldenNeg x`. The two sides are therefore definitionally equal, and reflexivity closes the theorem.

Conceptually this is the API normalization

$$
\text{raw coordinate negation}
\longrightarrow
\text{standard unary minus}.
$$

## Lean-specific processing

The important Lean mechanisms are typeclass resolution, definitional equality, and the `@[simp]` attribute.

The syntax `-x` is elaborated by finding a `Neg` instance for the type `GoldenInt`. Because the registered instance is `⟨goldenNeg⟩`, the expressions `goldenNeg x` and `-x` are definitionally equal even before any theorem rewrite is applied.

Nevertheless, registering an explicit simp theorem gives the simplifier a chosen normalization direction from

```lean
goldenNeg x
```

to

```lean
-x.
```

This is the same design used by 0156: raw implementation syntax is normalized toward standard algebra notation.

## Redundancy and duplication

From the viewpoint of logical information, the theorem is redundant because unfolding the instance already makes the equality reflexive. It is nevertheless useful as an API declaration.

- It preserves the raw operation name for auditability.
- It gives downstream simp normalization a standard-notation target.
- It reduces the need for callers to unfold the implementation of the `Neg` instance.
- It keeps a consistent API across the 0156–0160 bridge theorem family.

Thus it is mathematically trivial but meaningful as an interface theorem.

## Optimization candidates

Possible designs include:

1. Keep the current `@[simp] theorem ... := rfl` bridge.
2. Remove the theorem and unfold `goldenNeg` or the `Neg` instance at use sites.
3. Hide the raw operation after the algebra structures are complete and expose only standard notation downstream.
4. Group `golden_add_eq` through `golden_pow_eq` explicitly into an API-bridge section with a source comment documenting the intended normalization boundary.

Because this formalization deliberately preserves a visible raw coordinate layer, options 1 or 4 are the most natural. A few fewer lines are less valuable than a readable boundary between the bootstrap layer and the standard algebra interface.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib` globally. This theorem itself invokes no advanced Mathlib lemma; directly it requires `GoldenInt`, `goldenNeg`, the `Neg GoldenInt` instance, ordinary equality machinery, and the `@[simp]` attribute.

Therefore all of `Mathlib` is unlikely to be required solely for 0157. The actual `GoldenOrder` module also constructs `CommRing`, uses tactics and infrastructure such as `ring`, `omega`, `norm_num`, and `Zsqrtd`, so its true minimal import set is governed by the module as a whole.

No Lean build is performed in this museum pass, so a more granular minimum import set remains unverified and is explicitly only an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. The comparison concerns Lean API normalization strategy rather than a mathematical algorithm.

Candidate approaches are the current explicit `@[simp]` bridge theorem, repeated unfolding of raw definitions or instances, and hiding the raw API after structure construction in favor of standard notation only.

Useful metrics include simp stability, downstream proof size, robustness under implementation changes, frequency with which raw implementation details appear in errors, auditability of the coordinate layer, and interoperability with generic algebra theorems.

In particular, this provides a small clean experiment for measuring the value of retaining a named theorem whose proof is merely `rfl`.

## Relation to the PDFs and Lean source

The formal basis is the `GoldenOrder` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch, together with the source dependency order recorded by the preceding 0156 document. The source reading for 0156 confirms that this theorem is followed by `golden_sub_eq`, `golden_mul_eq`, and `golden_pow_eq`.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The specific PDF page or section corresponding to this small API bridge theorem was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

Where 0156 bridges addition and 0157 bridges negation from the raw API to standard notation, 0158 will expose the same definitional agreement for raw subtraction `goldenSub`, which was constructed from those two operations, and the standard notation `x - y`.
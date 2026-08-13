# 0130 — `instance : Neg GoldenInt`

## Lean type

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

This anonymous instance registers the raw function `goldenNeg` from 0122 as the standard unary-minus operation for `GoldenInt`.

## Mathematical statement

For $x=a+b\varphi$,

$$
-x=(-a)+(-b)\varphi.
$$

Thus the coordinatewise minus operation becomes available as the standard notation `-x`. This declaration is an interface registration, not a new algebraic theorem.

## Role in the full proof

The source first defines raw coordinate arithmetic and then exposes it through Lean's standard algebra interfaces. This declaration bridges `goldenNeg` to ordinary notation used later when building `AddCommGroup GoldenInt` and `CommRing GoldenInt`.

## Direct dependencies

It depends directly on `GoldenInt`, `goldenNeg`, and the standard `Neg` interface. It does not directly require `GoldenInt.ext`, `goldenAdd`, or `goldenMul`.

## Proof flow

There is no tactic proof. From the expected type `Neg GoldenInt`, Lean infers that `⟨goldenNeg⟩` supplies a function `GoldenInt → GoldenInt`. Typeclass search then uses this instance whenever `-x` is elaborated.

## Lean-specific processing

The key mechanisms are expected-type elaboration, typeclass resolution, and definitional equality. Because the raw function itself is registered, standard notation and the coordinate implementation stay definitionally aligned, making coordinate projection lemmas natural `rfl` candidates.

## Redundancy and duplication

`goldenNeg x` and `-x` expose the same computation at two API layers. The duplication is intentional: the raw name supports staged construction, while the standard notation supports later algebraic proofs.

## Optimization candidates

Alternatives include inlining the coordinate formula directly into the instance, bundling the additive structure earlier, or using a product carrier such as `ℤ × ℤ`. The current staged design makes dependency order especially transparent.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself conceptually needs only the local `GoldenInt` / `goldenNeg` definitions, the `Neg` interface, and integer arithmetic. The exact minimal import set is unverified because no Lean build was run.

## Comparator challenge suitability

Suitability is **high**. Compare the current raw-function-then-instance design with direct inlining and product-carrier reuse. Useful metrics are definitional equality, `rfl` / `simp` cost, dependency order, later group/ring construction, and readability.

## Relation to the existing PDFs

The branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. Their presence was confirmed, but the exact page or section for this anonymous instance was not inspected, so no PDF-specific page number is guessed. The formal source of truth is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

It connects the raw subtraction function from 0123 to Lean's standard `x - y` notation and is the natural next article.

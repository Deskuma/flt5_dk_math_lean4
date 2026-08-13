# 0131 — `instance : Sub GoldenInt`

## Lean type

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

This is not a theorem but an anonymous instance registering the raw operation `goldenSub`, defined in 0123, as the standard Lean / Mathlib subtraction interface `Sub` for `GoldenInt`.

## Mathematical statement

Reading `GoldenInt` elements as

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

0123 `goldenSub` represents

$$
x-y=(a-c)+(b-d)\varphi.
$$

The implementation does not duplicate the coordinate subtraction formula. Instead it is defined by

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

that is,

$$
x-y=x+(-y).
$$

The present instance connects that raw operation to the standard notation `x - y`.

## Role in the full proof

The `GoldenOrder` layer first defines raw coordinate operations—`goldenZero`, `goldenOne`, `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`—and then registers them with Lean's standard algebra typeclasses. This declaration is the subtraction boundary following the `Zero`, `One`, `Add`, and `Neg` registrations.

It allows later constructions such as `AddCommGroup GoldenInt`, `CommRing GoldenInt`, and golden-integer identities to use ordinary `x - y` notation without exposing the raw name `goldenSub x y`.

## Direct dependencies

The declaration directly depends on `GoldenInt`, `goldenSub`, and Lean's standard `Sub` typeclass. Since `goldenSub` itself depends on 0121 `goldenAdd` and 0122 `goldenNeg`, the dependency chain is

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}.
$$

No new mathematical lemma is required by the instance itself.

## Proof / construction flow

There is no proof script. The declaration simply supplies `goldenSub` as the subtraction function required by `Sub GoldenInt`:

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

Conceptually this is a one-step interface registration from raw coordinate subtraction to standard Lean subtraction notation.

## Lean-specific processing

In `⟨goldenSub⟩`, the expected type `Sub GoldenInt` determines the structure constructor. After registration, the notation `x - y` is resolved through typeclass inference to this instance and unfolds definitionally to `goldenSub x y`.

Consequently, later coordinate-projection lemmas can often reduce by `rfl` or light `simp`, depending on their exact formulation. The key point is that notation and the raw function are connected definitionally rather than by an additional rewrite theorem.

## Redundancy and duplication

At the level of meaning, `goldenSub` and `Sub GoldenInt` expose the same subtraction in two layers, so there is API-level duplication. Their roles are nevertheless distinct: `goldenSub` is a raw bootstrap operation usable before algebraic typeclass construction, while `Sub GoldenInt` exposes that operation through Mathlib's standard algebra API and notation.

Moreover, `goldenSub` already avoids mathematical duplication by being defined as `goldenAdd x (goldenNeg y)` instead of restating the coordinate formula.

## Optimization candidates

Three designs are worth comparing:

1. remove `goldenSub` and register `fun x y => goldenAdd x (goldenNeg y)` directly as the `Sub` instance;
2. after `Add` and `Neg` are available, define the instance using only standard notation as `fun x y => x + (-y)`;
3. keep the current raw-operation layer and use the instance only as the public algebra boundary.

The current design is one layer longer but makes the bootstrap order explicit, avoids dependency cycles, and cleanly separates the raw coordinate layer from the standard algebra interface. Optimization should therefore be evaluated by preservation of definitional transparency rather than line count alone.

## Required Mathlib import and import optimization

The standalone source imports `Mathlib` globally. This declaration itself uses no advanced Mathlib theorem; directly it needs only `GoldenInt`, `goldenSub`, and the standard `Sub` interface.

Thus a modular source should not require the whole of `Mathlib` merely for this instance. The true minimal import set is governed by the upstream `GoldenOrder` definitions. Because no Lean build is performed in this run, the exact minimal import set is unverified and should be treated as an optimization hypothesis rather than a confirmed result.

## Comparator challenge suitability

Yes. A useful comparator could implement the same downstream API in three ways: raw `goldenSub` plus a `Sub` instance; direct registration of `x + (-y)`; or direct coordinate subtraction `⟨x.fst-y.fst, x.snd-y.snd⟩`.

Evaluation criteria include the number of lemmas closing by `rfl`, simp normal forms, dependency-cycle behavior, readability of unfolding, and proof burden when constructing `AddCommGroup`. Although tiny, this declaration makes a good challenge about where definitional equality should live in a Lean algebra implementation.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch. The existing Japanese and English PDFs provide narrative context, but the exact PDF page corresponding to this anonymous instance was not directly checked in this run; therefore no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

By 0131 the standard additive, negation, and subtraction APIs are in place. The next step connects 0124 `goldenMul` to ordinary multiplication `x * y`, allowing the multiplication encoding $\varphi^2=\varphi+1$ to enter Mathlib's ring interface.

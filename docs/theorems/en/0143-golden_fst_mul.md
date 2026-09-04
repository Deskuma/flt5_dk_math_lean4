# 0143 — `golden_fst_mul`

## Lean type

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl
```

This is a `@[simp]` theorem reducing the first coordinate `fst` of the standard multiplication `x * y` on `GoldenInt` to an explicit expression in integer coordinates.

## Mathematical statement and meaning of the declaration

Write elements of `GoldenInt` as

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

with the generator satisfying

$$
\varphi^2=\varphi+1.
$$

Expanding the product gives

$$
(a+b\varphi)(c+d\varphi)=ac+(ad+bc)\varphi+bd\varphi^2.
$$

Using the quadratic relation yields

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi.
$$

Therefore the first coordinate, namely the coefficient of the basis element `1`, is

$$
\operatorname{fst}(xy)=ac+bd.
$$

The theorem exposes exactly this identity in Lean as

```lean
(x * y).fst = x.fst * y.fst + x.snd * y.snd
```

Unlike the subtraction projections 0141–0142, this is no longer merely a coordinatewise operation: the golden-integer-specific quadratic relation compiled into `goldenMul` is now visible in the coordinate formula.

## Role in the overall proof

This theorem is the first half of the multiplication projection API that reduces abstract standard multiplication on `GoldenInt` to integer arithmetic. Together with the following 0144 `golden_snd_mul`, it allows equalities involving golden-integer products to be decomposed completely into polynomial identities on the two integer coordinates.

This role is important immediately afterward in the construction of `goldenCommRing : CommRing GoldenInt`. The source proves the ring-law goals in a pattern essentially of the form

```lean
intros <;> ext <;>
simp <;> ring
```

After `GoldenInt.ext` splits an equality into coordinate goals, `simp` uses this theorem together with `golden_snd_mul` to turn `GoldenInt` multiplication into integer polynomial expressions, and `ring` closes the resulting identities.

Thus this theorem is not merely presentational: it is part of the rewrite interface used to construct the actual commutative-ring structure on the golden integers.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenMul`
- the `Mul GoldenInt` instance

The upstream raw multiplication is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

and standard multiplication is registered by

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

so the right-hand side of the present theorem is literally the first coordinate of `goldenMul`.

Mathematically the background relation is $\varphi^2=\varphi+1$, but the theorem does not invoke a separate lemma for that relation. The reduction has already been compiled into the definition of `goldenMul`.

The next theorem 0144 `golden_snd_mul` is its companion projection, but the proof of the present theorem does not depend on 0144.

## Proof / construction flow

The proof is only

```lean
:= rfl
```

When Lean unfolds `(x * y).fst`, the conceptual reduction is

```text
x * y
→ goldenMul x y
→ ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

and taking the first projection gives exactly

```lean
x.fst * y.fst + x.snd * y.snd
```

so both sides are definitionally identical and the theorem closes by `rfl`.

The important design point is that the quadratic algebra is not reproved inside this theorem. That complexity is handled once in the definition of `goldenMul`; the theorem serves purely as a definitional bridge between standard notation and the coordinate formula.

## Lean-specific processing

The central combination is `@[simp]` with `rfl`.

Because `rfl` succeeds, the route from standard multiplication notation `x * y` to raw `goldenMul x y` and then to the first coordinate expression is completely definitionally transparent.

The `@[simp]` attribute means that later goals containing

```lean
(x * y).fst
```

are automatically normalized to

```lean
x.fst * y.fst + x.snd * y.snd
```

This eliminates the `GoldenInt`-specific multiplication early and hands the resulting goal to ordinary integer simplification and the `ring` tactic.

In particular, the compact `ext <;> simp <;> ring` pattern used in the construction of `goldenCommRing` depends on this family of projection simp theorems.

## Redundancy and duplication

The statement repeats the first-coordinate formula already present in the definition of `goldenMul`, so there is definitional duplication. Together with 0144 `golden_snd_mul`, it also contributes the usual two-coordinate boilerplate.

However, always unfolding the raw definition would make downstream proofs depend directly on the implementation of `goldenMul`. A dedicated `@[simp]` theorem instead creates a small stable rewrite API between the raw representation and later proofs.

This duplication is therefore best viewed as deliberate API-level duplication serving simp control and proof auditability.

## Optimization candidates

Possible designs include:

1. retain the current individual `fst` / `snd` multiplication projection theorems;
2. introduce a single pair-level theorem of the form `x * y = ⟨..., ...⟩` and derive both projections from it;
3. remove the projection theorems and use `simp [goldenMul]` at every call site;
4. abstract coordinate multiplication for a general quadratic relation $\theta^2=p\theta+q$ and obtain this formula as the specialization $p=q=1$;
5. move toward existing Mathlib infrastructure such as `AdjoinRoot` or quadratic algebra and delegate part of the coordinate API to generic theory.

The strength of the current design is that it preserves `rfl` and a very simple simp normal form. Abstraction may reduce code duplication, but if it makes downstream proofs such as `goldenCommRing` more complicated, it introduces a trade-off against the auditability goals of the FLT5 development.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This theorem itself invokes no advanced Mathlib result. Directly it needs `GoldenInt`, `goldenMul`, `Mul GoldenInt`, integer addition and multiplication, and standard simp infrastructure.

The complete `GoldenOrder` module, however, immediately constructs `AddCommGroup` and `CommRing`, uses the `ring` tactic, and later interacts with quadratic-extension infrastructure. The practical minimal import set is therefore governed by the module as a whole rather than by this theorem in isolation.

Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified. Splitting the umbrella `Mathlib` import is therefore an optimization candidate, not a confirmed minimal configuration.

## Suitability as a Comparator challenge

Yes.

Useful implementations to compare include:

- the current dedicated `@[simp]` projection theorem;
- raw unfolding through `simp [goldenMul]`;
- projection from a pair-level multiplication theorem;
- a generic quadratic-order / `AdjoinRoot`-based implementation.

Evaluation criteria include proof size for `goldenCommRing`, the number of lemmas still closing by `rfl`, stability of simp normal forms, resilience to representation changes, generalizability, and readability of downstream FLT5 theorems.

This theorem is especially suitable because it is the first point where the golden quadratic relation becomes visible through standard multiplication projection, making the difference between a specialized coordinate implementation and a generic quadratic-order implementation easy to measure.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of this theorem is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`. In that source, `goldenMul`, the `Mul GoldenInt` instance, the present theorem, 0144 `golden_snd_mul`, and `goldenCommRing` appear as one continuous local API.

The concrete PDF page or section corresponding to this projection theorem was not directly identified in this pass. Therefore no PDF page number or narrative location is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

Where 0143 exposes the basis-`1` component $ac+bd$, 0144 exposes the $\varphi$ component $ad+bc+bd$. Once both are available, multiplication on the golden integers is fully expanded into integer coordinates and the development can proceed directly to constructing `CommRing GoldenInt`.
# 0144 — `golden_snd_mul`

## Lean type

```lean
@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd =
      x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

This is a `@[simp]` theorem reducing the second coordinate `snd` of the standard multiplication `x * y` on `GoldenInt` to an explicit expression in integer coordinates.

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

Substituting the quadratic relation yields

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi.
$$

Therefore the second coordinate, namely the coefficient of the basis element `φ`, is

$$
\operatorname{snd}(xy)=ad+bc+bd.
$$

The theorem exposes this formula in Lean as

```lean
(x * y).snd =
  x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

Where 0143 `golden_fst_mul` handles the basis-`1` component $ac+bd$, the present theorem handles the `φ` component $ad+bc+bd$. Together they make multiplication on `GoldenInt` completely visible as two integer polynomial expressions.

## Role in the overall proof

This theorem is the second half of the multiplication projection API. Together with 0143, it allows equalities involving golden-integer products to be reduced completely to integer identities in the `fst` and `snd` coordinates.

In the source, this theorem is followed by `goldenAddCommGroup`, then `goldenAddGroupWithOne`, and then `goldenCommRing : CommRing GoldenInt`. The ring-law goals in `goldenCommRing` are closed in a pattern essentially of the form

```lean
intros <;> ext <;>
simp <;> ring
```

`GoldenInt.ext` decomposes structure equality into coordinate goals, `simp` uses 0143 and the present theorem to expand golden multiplication into integer polynomial expressions, and `ring` closes the resulting commutative-ring identities.

In particular, this theorem supplies the second-coordinate bridge needed for distributivity, associativity, unit laws, and commutativity. It is therefore not merely a display lemma: it is a central rewrite interface keeping the construction of `CommRing GoldenInt` compact.

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

so the right-hand side of the present theorem is literally the second coordinate of `goldenMul`.

Mathematically the background relation is $\varphi^2=\varphi+1$, but the proof does not invoke it through a separate lemma. The quadratic reduction has already been compiled into the definition of `goldenMul`.

0143 `golden_fst_mul` is the companion first-coordinate projection, but the `rfl` proof of the present theorem does not depend on 0143.

## Proof / construction flow

The proof is only

```lean
:= rfl
```

Unfolding `(x * y).snd` conceptually gives

```text
x * y
→ goldenMul x y
→ ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

and taking the second projection `snd` yields exactly

```lean
x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

so the two sides are definitionally identical and the theorem closes by `rfl`.

Again, the quadratic algebra is not reproved inside this theorem. The mathematical complexity is fixed once in the raw multiplication definition, while the theorem serves purely as a definitional bridge between standard notation and the coordinate formula.

## Lean-specific processing

The key combination is `@[simp]` with `rfl`.

Because `rfl` succeeds, the route from standard multiplication notation `x * y` to `goldenMul x y` and then to the second-coordinate expression is fully definitionally transparent.

The `@[simp]` attribute means that a later goal containing

```lean
(x * y).snd
```

is automatically normalized to

```lean
x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

This removes the `GoldenInt`-specific operation early and leaves a goal suitable for ordinary integer `simp`, `ring`, `omega`, and related tactics.

With both 0143 and this theorem marked `[simp]`, the pattern `ext <;> simp` becomes especially effective for a two-coordinate structure. This is one of the main reasons the subsequent `goldenCommRing` construction can remain concise.

## Redundancy and duplication

The statement repeats the second-coordinate formula already present in the definition of `goldenMul`, so it contains definitional duplication. Together with 0143 it also forms the expected two-projection boilerplate of a two-coordinate structure.

However, directly unfolding raw `goldenMul` in every downstream proof would tightly couple those proofs to the implementation. A dedicated `@[simp]` theorem instead provides a small stable rewrite API between the raw representation and algebraic proofs.

The duplication is therefore deliberate API-level duplication serving simp-normal-form control, proof auditability, and tactic stability.

## Optimization candidates

Possible designs include:

1. retain the current individual `golden_fst_mul` / `golden_snd_mul` theorems;
2. introduce one pair-level theorem of the form `x * y = ⟨..., ...⟩` and derive both projection theorems from it;
3. remove the projection theorems and use `simp [goldenMul]` at call sites;
4. abstract coordinate multiplication for a general quadratic relation $\theta^2=p\theta+q$ and construct the golden case as the specialization $p=q=1$;
5. move toward existing Mathlib infrastructure such as `AdjoinRoot` or quadratic algebra and reuse more generic ring and coordinate theory.

The current design trades a small amount of boilerplate for `rfl`, a simple simp normal form, and a short `CommRing` construction. For an auditable FLT5 development, preserving this transparency can reasonably be more valuable than minimizing line count.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This theorem itself invokes no advanced Mathlib result. Directly it needs `GoldenInt`, `goldenMul`, `Mul GoldenInt`, integer addition and multiplication, and standard simp infrastructure.

The complete `GoldenOrder` module, however, immediately constructs `AddCommGroup`, `AddGroupWithOne`, and `CommRing`, uses the `ring` tactic, and later interacts with quadratic-extension APIs. The practical minimal import set is therefore governed by the module as a whole rather than this theorem in isolation.

Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified. Replacing the umbrella `Mathlib` import with more focused imports is therefore recorded only as an optimization candidate.

## Suitability as a Comparator challenge

Yes.

Useful implementations to compare include:

- the current dedicated `@[simp]` projection theorem;
- raw unfolding through `simp [goldenMul]`;
- projection from a pair-level multiplication theorem;
- a generic quadratic-order / `AdjoinRoot`-based implementation.

Evaluation criteria include proof size for `goldenCommRing`, the number of lemmas closing by `rfl`, stability of simp normal forms, resilience to changes in the raw representation, generalizability, and readability of downstream FLT5 theorems.

0144 is especially suitable because the `φ` component $ad+bc+bd$ displays the effect of the quadratic relation most explicitly, making the difference between a specialized coordinate implementation and a generic quadratic-order implementation easy to measure.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of this theorem is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`. In that source, `goldenMul`, the `Mul GoldenInt` instance, 0143 `golden_fst_mul`, the present theorem, `goldenAddCommGroup`, and `goldenCommRing` appear as one continuous local API.

The concrete PDF page or section corresponding to this small projection theorem was not directly identified in this pass. Therefore no PDF page number or narrative location is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

By 0143–0144, both multiplication projections are available, completing the coordinate simp API for zero, one, addition, negation, subtraction, and multiplication. The next stage uses these projection theorems together with `GoldenInt.ext` to prove that the explicit coordinate operations actually form an `AddCommGroup GoldenInt`.
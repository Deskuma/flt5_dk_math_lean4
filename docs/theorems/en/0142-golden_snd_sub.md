# 0142 — `golden_snd_sub`

## Lean type

```lean
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

This is a `@[simp]` theorem exposing that subtraction on `GoldenInt` acts on the second coordinate `snd` exactly as integer subtraction does.

## Mathematical statement and meaning of the declaration

Write elements of `GoldenInt` as

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

Then subtraction is

$$
x-y=(a-c)+(b-d)\varphi.
$$

Hence the second coordinate, namely the coefficient of $\varphi$, satisfies

$$
\operatorname{snd}(x-y)=b-d.
$$

The theorem expresses this coordinate identity in Lean as

```lean
(x - y).snd = x.snd - y.snd
```

Mathematically this is an elementary coordinate fact, but formally it is a public rewrite API that reduces standard subtraction notation on `GoldenInt` to arithmetic on integer coordinates.

## Role in the overall proof

Together, 0141 `golden_fst_sub` and the present 0142 `golden_snd_sub` decompose subtraction on `GoldenInt` into integer subtraction on both coordinates.

This is important when combined with `GoldenInt.ext`. After an equality of golden integers is split into first- and second-coordinate goals, `simp` can normalize subtraction into ordinary integer arithmetic, allowing additive-group and ring laws to be reduced to standard coordinate calculations.

There is also a concrete downstream use in the standalone source: later in the Euclidean-division development, when the second coordinate of `goldenRemainder` is cast to the rationals and normalized, `golden_snd_sub` appears explicitly in a `simp only` rewrite set. Thus this theorem is not merely a presentation lemma; it is directly used by the later norm-Euclidean proof infrastructure.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenNeg`
- `goldenAdd`
- `goldenSub`
- the `Sub GoldenInt` instance

Raw subtraction is defined by

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

and `goldenNeg` is coordinatewise negation. Therefore the second coordinate is definitionally

$$
x_{\mathrm{snd}}+(-y_{\mathrm{snd}})=x_{\mathrm{snd}}-y_{\mathrm{snd}}.
$$

The preceding theorem 0141 `golden_fst_sub` is the mathematical companion of this result, but the proof of the present theorem does not rewrite through 0141. Both arise independently by `rfl` from the same raw definitions.

## Proof / construction flow

The proof consists only of

```lean
:= rfl
```

When Lean unfolds the left-hand side `(x - y).snd`, the conceptual reduction is

```text
x - y
→ goldenSub x y
→ goldenAdd x (goldenNeg y)
→ ⟨x.fst + (-y.fst), x.snd + (-y.snd)⟩
```

and the second coordinate becomes `x.snd + (-y.snd)`. Over the integers this is definitionally compatible with subtraction, so it coincides with the right-hand side `x.snd - y.snd` and the theorem closes by `rfl`.

Thus the theorem does not derive a new mathematical fact so much as expose, through definitional equality, that the upstream data design agrees exactly with standard subtraction.

## Lean-specific processing

The important combination is `@[simp]` with `rfl`.

The fact that `rfl` succeeds means there is no additional proof layer between the standard notation `x - y` and the raw operation `goldenSub x y`; the implementation remains definitionally transparent all the way down to the second coordinate.

The `@[simp]` attribute allows later proofs to normalize

```lean
(x - y).snd
```

automatically to

```lean
x.snd - y.snd
```

This removes the `GoldenInt`-specific structure early and hands the goal to the standard simplifier, `ring`, and cast lemmas over `Int`.

The later Euclidean-division proof explicitly uses a rewrite set of the form `simp only [goldenRemainder, goldenMul, golden_snd_sub, Int.cast_sub, ...]`. This shows that the theorem serves not only as a convenient simp lemma but also as a controlled local rewrite contract.

## Redundancy and duplication

0141 `golden_fst_sub` and 0142 `golden_snd_sub` have almost identical shapes. This is deliberate duplication arising from the two-coordinate structure.

It would also be possible to obtain the same result by unfolding `goldenSub` directly, so in principle the theorem could be omitted. Doing so, however, would make downstream proofs depend more strongly on the internal implementations of `goldenSub`, `goldenAdd`, and `goldenNeg`.

Providing a dedicated projection theorem creates a small stable API boundary between the raw implementation and downstream proofs, giving this apparent duplication practical value.

## Optimization candidates

Possible designs include:

1. keep the current individual `fst` / `snd` projection theorems;
2. introduce a pair-level subtraction theorem and derive the projection lemmas from it;
3. remove the projection theorem and always unfold `goldenSub`;
4. generate the coordinate subtraction lemmas from a more generic product or quadratic-order abstraction.

At the present scale, the current approach is the most transparent. Each theorem closes by `rfl`, and its orientation as a simp lemma is unambiguous.

If many more structurally identical coordinate lemmas accumulate, code generation or abstraction could reduce boilerplate. However, if that abstraction weakens definitional transparency, the trade-off should be evaluated against the auditability goals of the FLT5 development.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This theorem itself invokes no advanced Mathlib theorem. Directly it needs only `GoldenInt`, its upstream subtraction definitions and instance, and ordinary integer subtraction. Therefore the entire `Mathlib` umbrella import should not be necessary solely for this theorem.

The full `GoldenOrder` module, however, later constructs `AddCommGroup`, `CommRing`, uses `ring`, and interacts with quadratic-extension infrastructure. Because no Lean build is performed in this museum pass, the exact minimal import set is unverified. Import splitting is therefore an optimization candidate rather than a confirmed minimal configuration.

## Suitability as a Comparator challenge

Yes.

A useful comparison could implement the same downstream behavior using:

- the current dedicated `@[simp]` projection theorem;
- raw unfolding via `simp [goldenSub, goldenAdd, goldenNeg]`;
- derivation from a pair-level or generic quadratic-order abstraction.

Evaluation criteria include downstream proof size, preservation of `rfl`, simp stability, resilience to implementation changes, and rewrite controllability in proofs involving casts such as the Euclidean-division argument.

In particular, proofs using tightly controlled `simp only` sets make the difference between a dedicated projection API and raw unfolding especially visible, so this small theorem forms a useful Comparator challenge.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of this theorem is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`. The same standalone source later uses `golden_snd_sub` explicitly in a `simp only` rewrite set inside the generated `GoldenEuclidean.lean` section.

The concrete PDF page or section corresponding to this small projection theorem was not directly identified in this pass. Therefore no PDF page number or narrative location is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl
```

By 0141–0142, the coordinate projections for subtraction are complete. The next stage exposes the multiplication encoded by `goldenMul`, where the relation $\varphi^2=\varphi+1$ becomes visible in the standard multiplication `x * y`. This moves the development from coordinatewise operations to the genuinely quadratic structure specific to the golden integers.
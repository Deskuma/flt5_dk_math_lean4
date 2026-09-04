# 0140 — `golden_snd_neg`

## Lean type

```lean
@[simp] theorem golden_snd_neg (x : GoldenInt) :
    (-x).snd = -x.snd := rfl
```

This is a `theorem` marked with the `@[simp]` attribute. It is the second-coordinate projection lemma for negation on `GoldenInt`.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents a golden integer

$$
a+b\varphi
$$

by an integer pair `⟨a,b⟩`. The upstream raw operation `goldenNeg` is defined coordinatewise:

```lean
def goldenNeg (x : GoldenInt) : GoldenInt :=
  ⟨-x.fst, -x.snd⟩
```

and is connected to the standard unary negation notation by

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

Hence

$$
-(a+b\varphi)=(-a)+(-b)\varphi,
$$

and this theorem exposes the second-coordinate component as a public simp API:

$$
\operatorname{snd}(-x)=-\operatorname{snd}(x).
$$

## Role in the overall proof

Declaration 0139 `golden_fst_neg` reduces the first coordinate of negation to integer negation, while this theorem handles the second coordinate. Once both are available, an equality of golden integers decomposed by `GoldenInt.ext` can normalize every occurrence of `-x` to ordinary integer negation in both coordinates.

Together with the subtraction projection lemmas immediately following it, this theorem belongs to the API that supports the later construction

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
  intros <;> ext <;> simp [add_comm, add_left_comm]
```

In particular, additive-group laws such as `neg_add_cancel` can be reduced to standard integer arithmetic rather than proved by bespoke golden-integer calculations.

This theorem is not itself a core fifth-power factorization result. Its role is infrastructural: it helps lift the explicit coordinate implementation of the golden integers into Mathlib's standard ring hierarchy, which is later used by divisibility, norm, and Euclidean-domain arguments.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- the projection `GoldenInt.snd`
- standard integer negation

Conceptually,

$$
\texttt{goldenNeg}\longrightarrow\texttt{Neg GoldenInt}\longrightarrow\texttt{golden\_snd\_neg}.
$$

Declaration 0139 `golden_fst_neg` immediately precedes this theorem and forms its API pair, but the proof of this theorem does not invoke 0139.

## Proof / construction flow

The proof is the single term `rfl`.

1. Through the `Neg GoldenInt` instance, `-x` unfolds definitionally to `goldenNeg x`.
2. By definition, the second coordinate of `goldenNeg x` is `-x.snd`.
3. Thus `(-x).snd` reduces to exactly the right-hand side, and reflexivity closes the goal.

No algebraic theorem, rewrite, or case split is needed. The proof is precisely the definitional equality maintained between the raw operation and the standard typeclass notation.

## Lean-specific processing

The fact that `rfl` closes the theorem means the two sides are definitionally equal: after elaboration and reduction they become the same Lean term, rather than requiring a separate proposition-level equality theorem.

The `@[simp]` attribute installs the simplification rule

```lean
(-x : GoldenInt).snd
```

to

```lean
-x.snd
```

in the simplifier.

Instead of globally unfolding the internal definition of `goldenNeg`, this design exposes only the coordinate projection needed by users as a stable normal form. Combined with `GoldenInt.ext` and `simp`, it provides enough computational power for coordinate proofs without unnecessarily exposing the entire internal representation.

## Redundancy and duplication

This theorem is almost perfectly symmetric to 0139 `golden_fst_neg`; only `fst` versus `snd` changes. That is deliberate API-level duplication.

There is also semantic overlap between this theorem and directly unfolding `goldenNeg`, since the latter produces the same computation. The dedicated `@[simp]` theorem nevertheless allows the simplifier to normalize the desired projection without broadly unfolding the raw implementation.

## Optimization candidates

Three implementation strategies are worth comparing.

1. Keep dedicated `@[simp]` projection theorems for both `fst` and `snd`, as in the current design.
2. Make `goldenNeg` itself a simp-unfold target and remove some of the individual projection theorems.
3. Recast `GoldenInt` through an existing product or generic quadratic-algebra representation and reuse generic negation projection lemmas.

Approaches 2 and 3 may reduce the declaration count, but the current design localizes unfolding and makes downstream simp normal forms and proof traces more predictable. For an FLT5 formalization where auditability matters, the explicit API is a reasonable design choice.

## Required Mathlib imports and import optimization

The standalone source globally uses `import Mathlib`. This theorem itself directly needs only `GoldenInt`, the `Neg` instance, structure projection, `@[simp]`, `rfl`, and integer negation; it invokes no advanced Mathlib theorem.

Therefore the entire `Mathlib` import should not be necessary solely for this theorem. The actual minimal imports of a modular source are governed by the upstream `GoldenOrder` definitions, integer infrastructure, typeclass machinery, and later ring construction.

Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified. This point is therefore an import-optimization hypothesis rather than a confirmed dependency result.

## Suitability as a Comparator challenge

Yes. A useful challenge could compare:

- the current dedicated `@[simp]` projection-theorem approach;
- an approach relying only on unfolding `goldenNeg`;
- reuse of generic simp infrastructure from a product or quadratic-algebra representation.

Metrics include downstream proof length, simplifier stability, size of unfolded terms, readability of simp traces, automation rate in `ext` proofs, API discoverability, and resilience to changes in the internal representation.

The mathematics is elementary, but the theorem makes a clear Lean-library-design challenge about how much definitional computation should be frozen into the public simp API.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In the source, the declarations occur in the order

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) : (-x).fst = -x.fst := rfl
@[simp] theorem golden_snd_neg (x : GoldenInt) : (-x).snd = -x.snd := rfl
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. No concrete PDF page or section corresponding to this small definitional projection lemma was identified in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

By 0140, the projection API for negation is complete in both coordinates. Declaration 0141 should begin the subtraction pair, reducing subtraction—constructed upstream as `goldenSub x y = goldenAdd x (goldenNeg y)`—to standard coordinate subtraction under the notation `x - y`.
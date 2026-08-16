# 0137 — `golden_fst_add`

## Lean type

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
```

This is a `theorem`, and it is also marked with the `@[simp]` attribute as a first-coordinate projection lemma for addition.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents a golden integer

$$
a+b\varphi
$$

by an integer pair `⟨a,b⟩`. The upstream raw operation `goldenAdd` implements coordinatewise addition and is registered as the `Add GoldenInt` instance. Hence

$$
(a+b\varphi)+(c+d\varphi)=(a+c)+(b+d)\varphi,
$$

and the present theorem exposes the first-coordinate component of that identity through Lean's standard `+` notation:

$$
\operatorname{fst}(x+y)=\operatorname{fst}(x)+\operatorname{fst}(y).
$$

## Role in the overall proof

Declarations 0133–0136 exposed the coordinates of `0` and `1` through the public `@[simp]` API. Starting with 0137, the development moves to projection lemmas that reduce standard binary operations to coordinate arithmetic.

Because the first coordinate of `x + y` now normalizes to integer addition, later equalities proved with `GoldenInt.ext` can reduce their first-coordinate goals automatically to ordinary integer algebra. Together with the immediately following `golden_snd_add`, this theorem begins the coordinate simp infrastructure that continues through negation, subtraction, and multiplication.

This infrastructure is important for the later construction of `AddCommGroup GoldenInt` and `CommRing GoldenInt`. The source is deliberately arranged so that their laws can be reduced by `ext <;> simp` and standard normalization over the integer coordinates.

## Direct dependencies

The declaration directly depends on:

- `GoldenInt`
- the raw operation `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- the first-coordinate projection `GoldenInt.fst`
- standard integer addition

Conceptually, the dependency chain is

$$
\texttt{goldenAdd}
\longrightarrow
\texttt{Add GoldenInt}
\longrightarrow
\texttt{golden\_fst\_add}.
$$

No upstream algebraic lemma is needed; definitional reduction is sufficient.

## Proof / construction flow

The proof is simply

```lean
:= rfl
```

Lean unfolds `x + y` through the `Add GoldenInt` instance to `goldenAdd x y`. By definition, the first coordinate of `goldenAdd x y` is `x.fst + y.fst`, so the left-hand side `(x + y).fst` computes to exactly the right-hand side.

The substantive content is therefore not theorem-level reasoning, but the fact that the raw coordinate operation and the standard typeclass interface were connected while preserving definitional equality.

## Lean-specific processing

The fact that `rfl` closes the theorem shows that `(x + y).fst = x.fst + y.fst` is a definitional equality rather than a propositional equality derived from another theorem.

The `@[simp]` attribute additionally installs the reduction of

```lean
(x + y : GoldenInt).fst
```

to

```lean
x.fst + y.fst
```

in the simplifier.

This is particularly useful with `GoldenInt.ext`: an abstract equality over golden integers can be reduced coordinatewise, and the first-coordinate part of addition immediately becomes an equality in the integers.

## Redundancy and duplication

The immediately following `golden_snd_add` and the present theorem separately expose the two projections of the same raw operation `goldenAdd`, so they form a structurally duplicated pair.

This is intentional API-level duplication. Separate projection rules let `simp` normalize only the relevant coordinate without unnecessarily unfolding the whole representation, making downstream normal forms more predictable.

Since `goldenAdd` already defines coordinatewise addition exactly once, this theorem does not duplicate the mathematical implementation; it only publishes its definitional interface.

## Optimization candidates

Three main approaches are worth comparing.

1. Keep separate `@[simp]` theorems for the `fst` and `snd` projections, as in the current design.
2. Allow `simp` to unfold `goldenAdd` directly and reduce the number of dedicated projection theorems.
3. Recast `GoldenInt` through existing product or quadratic-algebra infrastructure and reuse more generic projection simp lemmas.

The current design increases the number of declarations, but keeps the simp surface local and explicit. In a long downstream FLT5 development, a stable public projection API may be easier to audit than unrestricted unfolding of the internal representation.

## Required Mathlib imports and import optimization

The standalone source imports `Mathlib` globally. This theorem itself requires only `GoldenInt`, the `Add` instance, structure projection, `@[simp]`, `rfl`, and integer addition; it directly invokes no advanced Mathlib theorem.

Therefore the theorem alone should not require all of `Mathlib`. The actual minimal import set is governed by the upstream module containing `GoldenInt` and `goldenAdd`. Because no Lean build is performed in this museum pass, the concrete minimal import set remains unverified and this point is explicitly an optimization hypothesis.

## Suitability as a Comparator challenge

Yes. A useful comparison could evaluate:

- the current dedicated `@[simp]` projection theorem;
- an approach relying only on unfolding `goldenAdd`;
- reuse of generic addition projection lemmas from a product or quadratic-algebra representation.

Metrics include downstream proof length, simplifier stability, amount of definitional unfolding, readability of simp traces, automation rate in `ext` proofs, and API discoverability.

The mathematics is elementary, but the declaration provides a useful Lean-library-design Comparator challenge about how much of a raw representation should be exposed through a public simp API.

## Relation to the PDFs and Lean source

The formal basis is the `GoldenOrder` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch, together with the theorem-museum documents immediately preceding this declaration. The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

However, no concrete PDF page or section corresponding to this small definitional projection lemma was identified directly in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

The present theorem exposes addition on the first coordinate; the next declaration, 0138, exposes the same definitional interface on the second coordinate.
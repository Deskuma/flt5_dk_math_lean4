# 0179 — `sqrtFiveElement`

## Lean type

```lean
/-- Short public name for the element `2φ-1`, whose square is five. -/
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

This is neither a `theorem` nor a `def`, but an `abbrev`. It gives the previously defined element `goldenSqrtFive` from 0177 the shorter public name `sqrtFiveElement` for downstream use.

## Mathematical statement and meaning of the declaration

Declaration 0177 defines

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

and a coordinate pair `⟨a,b⟩ : GoldenInt` represents $a+b\varphi$. Therefore

$$
goldenSqrtFive=-1+2\varphi=2\varphi-1.
$$

Using $\varphi=(1+\sqrt5)/2$ gives

$$
2\varphi-1=\sqrt5.
$$

Thus the present declaration does not construct a new element. It merely gives the existing ramified element `goldenSqrtFive` a short name that foregrounds its mathematical interpretation.

Because this is an `abbrev`, `sqrtFiveElement` and `goldenSqrtFive` are not merely connected by a theorem: the former is a transparently reducible alias for the latter.

## Role in the overall proof

Declarations 0177–0178 introduce the concrete distinguished elements

- `goldenSqrtFive`
- `goldenTau`

in explicit coordinates. Declaration 0179 and the immediately following `tau` declaration form an API-cleanup layer that exposes short public aliases for those elements.

The source order is

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
def goldenTau : GoldenInt := ⟨2, 1⟩
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
abbrev tau : GoldenInt := goldenTau

theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide
```

Hence this declaration does not advance the proof by proving a new mathematical fact. Its purpose is to make the ramified elements available through readable public names before the development proceeds to the identities

$$
(2\varphi-1)^2=5
$$

and

$$
N(2\varphi-1)=-5.
$$

## Direct dependencies

The direct dependencies are minimal:

- `GoldenInt`
- 0177 `goldenSqrtFive`

The declaration body is only

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

and therefore needs no additional lemma or tactic.

For its mathematical interpretation, 0161 `goldenPhi` and 0177 `goldenSqrtFive` give

$$
sqrtFiveElement=2\varphi-1.
$$

## Proof / construction flow

There is no proof script.

1. `goldenSqrtFive` has already been constructed in 0177.
2. The same value is assigned the alternative name `sqrtFiveElement`.
3. `abbrev` keeps the alias transparently unfoldable during elaboration.

No additional mathematical construction is introduced.

## Lean-specific processing

`abbrev` is normally treated as a reducible alias, more transparent than an ordinary `def`. Here `sqrtFiveElement` does not establish a separate opaque definition boundary; Lean can readily unfold it to `goldenSqrtFive` when needed.

This design provides a concise public name while allowing existing downstream theorems written with the internal name `goldenSqrtFive` to remain compatible without requiring a substantial rewrite layer.

At present, the subsequent proof core still mainly uses `goldenSqrtFive`. Thus `sqrtFiveElement` acts more like a public-facing façade than a replacement for the internal proof name.

## Redundancy and duplication

This declaration is intentionally an alias, so its value is completely redundant with 0177 `goldenSqrtFive`:

```lean
sqrtFiveElement
```

and

```lean
goldenSqrtFive
```

refer to the same `GoldenInt`.

The immediately following declaration

```lean
abbrev tau : GoldenInt := goldenTau
```

repeats the same alias pattern for the second ramified element.

This is API-level duplication, but it is reasonable if the library intentionally separates internal implementation names `goldenSqrtFive` / `goldenTau` from shorter mathematics-oriented public names `sqrtFiveElement` / `tau`.

## Optimization candidates

1. Keep the present alias layer and document clearly which names are internal and which are public.
2. Rewrite downstream theorems toward `sqrtFiveElement` so that the public name becomes the primary API.
3. If the alias is barely used, remove it and standardize on `goldenSqrtFive`.
4. Apply one consistent naming policy to both `sqrtFiveElement` and `tau`, explicitly identifying the canonical names.
5. In a more general quadratic-order abstraction, bundle the discriminant / ramified element and reduce the need for ad hoc aliases.

Since the declaration is only one line, optimization concerns API naming and interface consistency rather than proof performance.

## Required Mathlib imports and import optimization

This `abbrev` itself requires no additional Mathlib theorem or tactic once `GoldenInt` and `goldenSqrtFive` are available.

The standalone artifact uses `import Mathlib`, but this declaration alone does not justify such a broad import. The true minimal import set is governed by the upstream `GoldenOrder` module.

No Lean build is run in this museum pass, so the exact minimal module import set remains unverified and import reduction is listed only as an optimization candidate.

## Suitability as a Comparator challenge

It is small, but suitable as a Lean-library-design comparator.

Possible implementations are:

- `abbrev sqrtFiveElement := goldenSqrtFive`
- `def sqrtFiveElement := goldenSqrtFive`
- no alias, standardizing entirely on `goldenSqrtFive`
- making `sqrtFiveElement` the canonical definition and `goldenSqrtFive` the alias

Useful comparison criteria include:

- definitional transparency
- simp / unfolding behavior
- names appearing in error messages
- API discoverability
- amount of downstream rewriting
- separation of internal and public naming

This is not a challenge about mathematical correctness, but about the tradeoffs among `abbrev`, `def`, and canonical naming in Lean library design.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `GoldenOrder` source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this `abbrev` appears immediately after 0178 `goldenTau`, followed by the `tau` alias and then `goldenSqrtFive_sq`.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this alias was not identified directly, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- Short public name for the distinguished norm-five element `2+φ`. -/
abbrev tau : GoldenInt := goldenTau
```

Declaration 0179 gives a short public name to `goldenSqrtFive`; declaration 0180 does the same for 0178 `goldenTau`. After that alias layer is complete, the development returns to substantive arithmetic with `goldenSqrtFive_sq`, proving the square and norm properties of the ramified elements.
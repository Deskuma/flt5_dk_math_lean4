# 0139 — `golden_fst_neg`

## Lean type

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) :
    (-x).fst = -x.fst := rfl
```

This is a `theorem` marked with the `@[simp]` attribute. It is the first-coordinate projection lemma for negation on `GoldenInt`.

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

and is registered as the `Neg GoldenInt` instance.

Hence

$$
-(a+b\varphi)=(-a)+(-b)\varphi,
$$

and this theorem exposes the first-coordinate component through the standard unary negation notation `-x`:

$$
\operatorname{fst}(-x)=-\operatorname{fst}(x).
$$

## Role in the overall proof

After 0137 `golden_fst_add` and 0138 `golden_snd_add` complete the projection API for addition, this declaration begins the coordinate normalization API for negation.

Once 0139 `golden_fst_neg` and the next declaration 0140 `golden_snd_neg` are both available, equalities decomposed with `GoldenInt.ext` can reduce every occurrence of `-x` to ordinary integer negation in both coordinates. This is part of the infrastructure that lets the later `goldenAddCommGroup` construction discharge additive-group laws, including `neg_add_cancel`, through `ext <;> simp` and standard integer facts.

The theorem is not itself a number-theoretic core step of FLT5. Its role is infrastructural: it connects the explicit coordinate implementation of the golden integers to Lean's standard additive-group API.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- the projection `GoldenInt.fst`
- standard integer negation

Conceptually,

$$
\texttt{goldenNeg}\longrightarrow\texttt{Neg GoldenInt}\longrightarrow\texttt{golden\_fst\_neg}.
$$

The preceding declaration 0138 `golden_snd_add` is immediately prior in dependency order, but it is not a direct logical dependency of this theorem.

## Proof / construction flow

The proof consists only of `rfl`.

1. `-x` unfolds through the `Neg GoldenInt` instance to `goldenNeg x`.
2. By definition, the first coordinate of `goldenNeg x` is `-x.fst`.
3. Therefore `(-x).fst` computes to exactly the right-hand side, and reflexivity closes the goal.

No theorem-level algebraic reasoning or rewrite is required. The proof is precisely the definitional equality preserved between the raw operation and the standard typeclass notation.

## Lean-specific processing

The fact that `rfl` proves the theorem shows that the equality is definitional: after reduction, both sides are the same term rather than merely propositionally equal after using another lemma.

The `@[simp]` attribute installs the simplification rule

```lean
(-x : GoldenInt).fst
```

to

```lean
-x.fst
```

in the simplifier.

This direction allows abstract negation on `GoldenInt` to reduce to integer arithmetic without globally unfolding the entire internal representation. For later proofs of the form `ext <;> simp`, this keeps the proof surface small and predictable.

## Redundancy and duplication

The next theorem 0140 `golden_snd_neg` is almost perfectly symmetric to this one; only the projected coordinate differs. This is deliberate API-level duplication.

There is also conceptual overlap between unfolding `goldenNeg` directly and using this projection theorem. However, a dedicated `@[simp]` theorem lets the library expose only the desired coordinate normalization instead of allowing broad unfolding of the internal raw definition.

## Optimization candidates

Three main approaches can be compared.

1. Keep dedicated `@[simp]` projection theorems for `fst` and `snd`, as in the current design.
2. Make `goldenNeg` itself a simp-unfold target and remove some projection theorems.
3. Recast `GoldenInt` through an existing product or generic quadratic-algebra representation and reuse generic negation projection lemmas.

The current design increases the declaration count but localizes unfolding of the internal representation. In a long downstream development, that is likely to improve simplifier predictability and auditability.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`. This theorem itself directly needs only `GoldenInt`, the `Neg` instance, structure projection, `@[simp]`, `rfl`, and integer negation; it invokes no advanced Mathlib theorem.

Therefore the theorem alone should not require all of `Mathlib`. The actual minimal import set is governed by the upstream definitions of `GoldenOrder` and the later algebra-instance construction. Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified and this point is explicitly an optimization hypothesis.

## Suitability as a Comparator challenge

Yes. A useful comparison could test:

- the current dedicated `@[simp]` projection theorem;
- an approach relying only on unfolding `goldenNeg`;
- reuse of generic simp infrastructure from a product or quadratic-algebra representation.

Metrics include downstream proof length, simplifier stability, amount of unfolding, readability of simp traces, automation rate in `ext` proofs, and API discoverability.

The mathematics is elementary, but the declaration makes a useful Lean-library-design challenge about where internal definitional unfolding should stop and where a public simp API should begin.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this theorem appears immediately after `golden_snd_add` and is followed by `golden_snd_neg`, then the subtraction projection lemmas.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. No concrete PDF page or section corresponding to this small definitional projection lemma was identified in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_neg (x : GoldenInt) :
    (-x).snd = -x.snd := rfl
```

Declaration 0139 exposes the first-coordinate normalization rule for negation. Declaration 0140 should complete the pair by exposing the second coordinate, allowing negation on `GoldenInt` to normalize to integer negation in both coordinates.
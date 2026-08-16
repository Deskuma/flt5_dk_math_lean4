# 0138 — `golden_snd_add`

## Lean type

```lean
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

This is a `theorem` marked with the `@[simp]` attribute. It is the second-coordinate projection lemma for addition on `GoldenInt`.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents a golden integer $a+b\varphi$ by an integer pair `⟨a,b⟩`. The upstream raw operation `goldenAdd` is defined coordinatewise:

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

and is registered as the `Add GoldenInt` instance. Hence

$$
(a+b\varphi)+(c+d\varphi)=(a+c)+(b+d)\varphi,
$$

and this theorem exposes the second-coordinate component through the standard `+` notation:

$$
\operatorname{snd}(x+y)=\operatorname{snd}(x)+\operatorname{snd}(y).
$$

## Role in the overall proof

Together with 0137 `golden_fst_add`, this theorem completes the public `@[simp]` interface that decomposes addition on `GoldenInt` into ordinary addition on its two integer coordinates.

Once both projection rules are available, later equalities proved using `GoldenInt.ext` can reduce goals containing `x + y` to integer addition on both coordinates. This is used immediately in the construction of `goldenAddCommGroup`, whose laws are designed to collapse through `ext <;> simp` to standard integer facts.

The theorem is not a number-theoretic core step of FLT5 by itself. Its role is infrastructural: it makes the explicit golden-integer ring manageable by reducing abstract algebraic laws to small coordinate calculations.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- the projection `GoldenInt.snd`
- standard integer addition

Conceptually,

$$
\texttt{goldenAdd}\longrightarrow\texttt{Add GoldenInt}\longrightarrow\texttt{golden\_snd\_add}.
$$

The preceding theorem 0137 `golden_fst_add` is not a logical dependency; it is the symmetric sibling exposing the other projection of the same raw definition.

## Proof / construction flow

The proof consists only of `rfl`.

1. `x + y` unfolds through the `Add GoldenInt` instance to `goldenAdd x y`.
2. By definition, the second coordinate of `goldenAdd x y` is `x.snd + y.snd`.
3. Therefore `(x + y).snd` computes to exactly the right-hand side, and reflexivity closes the goal.

No theorem-level algebraic reasoning is required. The proof is the definitional equality preserved between the raw operation and the standard typeclass notation.

## Lean-specific processing

The fact that `rfl` proves the theorem means the equality is definitional, not merely propositional after rewriting by another lemma.

The `@[simp]` attribute also installs the normalization

```lean
(x + y : GoldenInt).snd
```

to

```lean
x.snd + y.snd
```

in the simplifier.

Combined with 0137 and `GoldenInt.ext`, both coordinate goals of an equality involving addition reduce directly to integer arithmetic. This is what makes the later `ext <;> simp` style of algebra-instance proofs possible.

## Redundancy and duplication

The theorem is nearly isomorphic to 0137 `golden_fst_add`; only the projected coordinate differs. This is deliberate API-level duplication.

A generic projection abstraction could reduce the declaration count, but separate `fst` and `snd` simp rules make normal forms explicit and predictable, and give users directly discoverable theorem names for each coordinate.

## Optimization candidates

Three main approaches can be compared.

1. Keep dedicated `@[simp]` theorems for both `fst` and `snd`, as in the current design.
2. Let `simp` unfold `goldenAdd` itself and remove some projection theorems.
3. Recast `GoldenInt` through an existing product or generic quadratic-algebra representation and reuse generic projection lemmas.

The current design increases the number of declarations but localizes unfolding of the internal representation. In a long downstream FLT5 development, this explicit simp surface is likely to improve auditability and proof stability.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`. This theorem itself directly needs only `GoldenInt`, the `Add` instance, structure projection, `@[simp]`, `rfl`, and integer addition; it invokes no advanced Mathlib theorem.

Therefore the theorem alone should not require all of `Mathlib`. The true minimal import set is governed by the upstream dependencies of `GoldenOrder`. Because no Lean build is performed in this museum pass, the concrete minimal import set remains unverified and this point is explicitly an optimization hypothesis.

## Suitability as a Comparator challenge

Yes. A useful comparison could test:

- the current dedicated `@[simp]` projection theorem;
- an approach relying only on unfolding `goldenAdd`;
- reuse of generic simp infrastructure from a product or quadratic-algebra representation.

Metrics include downstream proof length, simplifier stability, amount of unfolding, readability of simp traces, automation rate in `ext` proofs, and API discoverability. The mathematics is elementary, but the declaration is a useful Lean-library-design challenge about the boundary between representation and public simp API.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this theorem appears immediately after `golden_fst_add` and is followed by `golden_fst_neg` and `golden_snd_neg`.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. No concrete PDF page or section corresponding to this small definitional projection lemma was identified in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) :
    (-x).fst = -x.fst := rfl
```

The projection API for both coordinates of addition is now complete. Declaration 0139 therefore begins the coordinate normalization rules for negation.
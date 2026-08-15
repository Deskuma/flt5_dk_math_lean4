# 0133 — `golden_fst_zero`

## Lean type

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
```

This is a `theorem`, and it is also marked with the `@[simp]` attribute as a coordinate-projection simplification lemma.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents an element $a+b\varphi$ by an integer pair `⟨a,b⟩`. Its zero element is defined and registered by

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

Hence the first coordinate of the golden integer zero $0=0+0\varphi$ is $0$. This lemma exposes that fact for the standard notation `(0 : GoldenInt)`.

$$
\operatorname{fst}(0_{\mathbb Z[\varphi]})=0.
$$

## Role in the overall proof

By 0132, the raw coordinate operations on `GoldenInt` have been registered with Lean's standard `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` interfaces. Starting with 0133, the source introduces `@[simp]` lemmas that project those standard notations back to explicit coordinate formulas.

`golden_fst_zero` is the first such lemma. It supports later coordinate proofs for `AddCommGroup GoldenInt`, `CommRing GoldenInt`, conjugation, norm, and divisibility by allowing `ext` plus `simp` to normalize the first coordinate of the zero element immediately.

The important API effect is that once an equality of `GoldenInt` values is reduced to coordinate equalities, the first coordinate of zero becomes the ordinary integer `0` without exposing raw implementation details manually.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenZero : GoldenInt := ⟨0, 0⟩`
- `instance : Zero GoldenInt := ⟨goldenZero⟩`

No mathematical lemma is required; the result follows entirely by definitional reduction.

Conceptually, the dependency chain is

$$
\texttt{goldenZero}
\longrightarrow
\texttt{Zero GoldenInt}
\longrightarrow
\texttt{golden\_fst\_zero}.
$$

## Proof / construction flow

The proof is just

```lean
rfl
```

Typeclass resolution expands `(0 : GoldenInt)` through the registered zero instance to `goldenZero`, which unfolds to

```lean
⟨0, 0⟩
```

and projecting `.fst` evaluates to the integer `0`. The two sides are definitionally identical, so reflexivity closes the theorem.

## Lean-specific processing

The `@[simp]` attribute is the key API feature. Lean registers this theorem as a simplifier rewrite rule, so later proofs can reduce `(0 : GoldenInt).fst` to `0` with

```lean
simp
```

The proof itself does not use `simp`; it uses `rfl`. This shows that the `Zero GoldenInt` instance is connected directly to the raw `goldenZero` definition, with no non-definitional theorem layer in between.

## Redundancy and duplication

Mathematically, the theorem adds no new information beyond `goldenZero := ⟨0,0⟩`; the first coordinate is visibly zero from the definition. In that sense it republishes definitional information.

As a Lean API lemma, however, it is useful rather than redundant because it exposes the simplification behavior of standard notation `0` without requiring downstream proofs to unfold the implementation manually.

`golden_fst_zero` and the immediately following `golden_snd_zero` form a symmetric pair and repeat the same pattern for the two coordinates. This duplication is natural for a product-like structure with explicit projection lemmas.

## Optimization candidates

Three designs are worth considering.

1. Keep explicit `@[simp]` projection lemmas as in the current source.
2. Remove dedicated lemmas and rely on simp unfolding `goldenZero` or the `Zero GoldenInt` instance.
3. Implement `GoldenInt` through a more generic product or algebraic structure and reuse more standard projection simp lemmas.

Option 2 may reduce line count, but it makes simplification behavior depend more heavily on unfolding raw implementation details and weakens the public API boundary. The current design costs more declarations but makes the intended simp interface explicit.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`, but this theorem alone requires no advanced Mathlib result. Its direct needs are basic structure support, the `Zero` typeclass, `@[simp]` theorem registration, the integer type `ℤ`, and the upstream `GoldenInt` / `goldenZero` declarations.

Therefore the whole of `Mathlib` should not be necessary merely for this lemma. The complete `GoldenOrder` module is a different matter because later declarations use `AddCommGroup`, `CommRing`, `Zsqrtd`, `ring`, `omega`, and related infrastructure. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Suitability as a Comparator challenge

It is possible, but this single lemma is too small to be an interesting challenge by itself. A better Comparator challenge would group the projection simp lemmas beginning at 0133.

Possible implementations are:

- explicit dedicated `@[simp]` lemmas
- simplification through unfolding raw definitions
- a generic product-like projection API

Useful metrics include how many downstream proofs close with `ext <;> simp`, simplifier trace complexity, and dependence on implementation details.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this theorem appears immediately after the `Mul GoldenInt` instance and is followed by `golden_snd_zero`, `golden_fst_one`, and the remaining projection simp lemmas.

Japanese and English PDFs are present on the target branch, but the concrete page corresponding to this theorem was not identified directly in this pass. Therefore no PDF page or section number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

Where 0133 registers simplification of the first coordinate of zero, the next declaration does the same for the second coordinate.
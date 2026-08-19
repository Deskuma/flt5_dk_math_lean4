# 0134 — `golden_snd_zero`

## Lean type

```lean
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

This is a `theorem`, and it is also marked with the `@[simp]` attribute as a coordinate-projection simplification lemma.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents an element $a+b\varphi$ by an integer pair `⟨a,b⟩`. In the Lean source, the zero element is defined and registered by

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

Therefore the second coordinate of the golden integer zero

$$
0=0+0\varphi
$$

namely the coefficient of $\varphi$, is also $0$. This theorem exposes that fact for the standard notation `(0 : GoldenInt)`.

$$
\operatorname{snd}(0_{\mathbb Z[\varphi]})=0.
$$

Where 0133 `golden_fst_zero` handled the first coordinate of zero, this theorem is its symmetric companion for the second coordinate.

## Role in the overall proof

By 0132, the raw coordinate operations on `GoldenInt` had been registered with Lean's standard `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` interfaces. Starting with 0133, the source begins a projection API of `@[simp]` lemmas that reduce standard notation back to explicit integer coordinates.

`golden_snd_zero` completes that API for the zero element. After an equality of `GoldenInt` values has been reduced by `GoldenInt.ext` to equalities of first and second coordinates, this lemma immediately normalizes `(0 : GoldenInt).snd` to the ordinary integer `0`.

This small theorem supports the proof style used immediately afterward when constructing `AddCommGroup GoldenInt` and `CommRing GoldenInt`:

```lean
ext <;> simp
```

In particular, it is part of the simplifier interface used when reducing ring laws involving zero, such as `zero_add`, `add_zero`, `neg_add_cancel`, `zero_mul`, and `mul_zero`, to coordinatewise integer identities.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenZero : GoldenInt := ⟨0, 0⟩`
- `instance : Zero GoldenInt := ⟨goldenZero⟩`

The proof itself uses no mathematical lemma; it follows entirely by definitional reduction.

Conceptually, the dependency chain is

$$
\texttt{goldenZero}
\longrightarrow
\texttt{Zero GoldenInt}
\longrightarrow
\texttt{golden\_snd\_zero}.
$$

0133 `golden_fst_zero` is its semantic companion, but this theorem does not call it in the Lean proof, so it is not a direct proof dependency.

## Proof / construction flow

The proof body is only

```lean
rfl
```

Lean interprets `(0 : GoldenInt)` through the registered `Zero GoldenInt` instance as `goldenZero`. Unfolding `goldenZero` gives

```lean
⟨0, 0⟩
```

and projecting `.snd` evaluates definitionally to the integer `0`. The two sides are therefore identical by reflexivity.

Conceptually, the reduction is

$$
(0:\texttt{GoldenInt}).\texttt{snd}
\rightsquigarrow
\texttt{goldenZero.snd}
\rightsquigarrow
\langle 0,0\rangle.\texttt{snd}
\rightsquigarrow
0.
$$

## Lean-specific processing

The important point is that `rfl` and `@[simp]` serve different purposes here.

- `rfl` shows that the fact requires no theorem-level mathematical reasoning and follows solely from definitional equality.
- `@[simp]` registers that definitional fact as a stable public rewrite rule for downstream proofs.

Consequently, later code does not need to unfold `goldenZero` or the `Zero GoldenInt` instance manually. A plain

```lean
simp
```

can reduce `(0 : GoldenInt).snd` to `0`.

This is a typical Lean design separating implementation details from the user-facing API. Even though the statement is definitionally obvious, the explicit simp lemma fixes the intended simplifier behavior as part of the public interface.

## Redundancy and duplication

As mathematical information, the theorem is already completely contained in the definition `goldenZero := ⟨0,0⟩`; it does not add a new mathematical fact. In that sense it republishes definitional information.

It is also almost structurally identical to 0133 `golden_fst_zero`, differing only in whether the first or second projection is taken. This is deliberate symmetric duplication for a product-like structure.

As a Lean API, however, the duplication is useful. The simplifier receives an explicit rewrite rule for each projection, so downstream proofs need not know the internal representation of `goldenZero`.

## Optimization candidates

Three implementation families are worth considering.

1. Keep `golden_fst_zero` and `golden_snd_zero` as separate explicit `@[simp]` theorems, as in the current source.
2. Remove the dedicated lemmas and allow simp to unfold `goldenZero` or the `Zero GoldenInt` instance directly.
3. Move the coordinate API toward a generic product-like abstraction and reuse or generate more projection simplification lemmas.

Option 2 can reduce declaration count, but it couples simplification more strongly to raw implementation unfolding and can make downstream proofs more sensitive to representation changes. The current approach is superficially repetitive but gives a stable and explicit public simp API.

Looking at the projection lemmas around 0133–0144, many consecutive declarations follow the same `rfl` pattern. A local helper macro or generated boilerplate could therefore reduce source repetition. On the other hand, explicit enumeration is easy to audit, which is valuable in a proof development whose design favors transparency.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib` globally, but this theorem alone needs no advanced Mathlib theorem. Its direct requirements are basic structure and projection support, the `Zero` typeclass, the integer type `ℤ`, theorem declarations with the `@[simp]` attribute, and the upstream `GoldenInt` / `goldenZero` definitions.

Therefore the whole of `Mathlib` should not be necessary merely for this lemma. The complete `GoldenOrder` module is different: immediately downstream it uses `AddCommGroup`, `AddGroupWithOne`, `CommRing`, `Zsqrtd`, `ring`, `omega`, and related infrastructure, so the actual minimal module import set is governed by the full module dependency graph.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified. This import optimization discussion is therefore an explicit hypothesis.

## Suitability as a Comparator challenge

By itself the theorem is too small to make an interesting challenge, but the family of projection simp lemmas beginning at 0133 is well suited to a Comparator challenge.

Possible implementations include:

- explicit dedicated `@[simp]` lemmas for each coordinate
- simplification through unfolding raw definitions
- a generic product-like API or generation helper

Useful comparison metrics are the number of downstream theorems that close with `ext <;> simp`, simplifier trace length, dependence on raw implementation details, code size, robustness under representation changes, and readability during proof auditing.

The theorem is nearly trivial to prove, but it is a good minimal example for comparing the value of keeping definitionally obvious facts as part of a public simp API.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In the Lean source, the relevant declarations occur in the order

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

so this theorem is the second member of the zero-projection pair, followed by the beginning of the projection pair for the unit element `1`.

The target branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. However, the specific PDF page corresponding to this small Lean projection theorem was not identified directly in this pass, so no page or section number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

With 0133–0134, the simp API for both coordinates of zero is complete. The next stage begins normalization of the unit element `1 = 1 + 0\varphi`, starting with its first coordinate.
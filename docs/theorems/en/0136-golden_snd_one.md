# 0136 — `golden_snd_one`

## Lean type

```lean
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

This is a `theorem`, and it is also marked with the `@[simp]` attribute as a coordinate-projection simplification lemma.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents a golden integer

$$
a+b\varphi
$$

by an integer pair `⟨a,b⟩`. In the Lean source, the multiplicative identity is defined and registered through

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

Therefore the standard notation `(1 : GoldenInt)` reduces definitionally to the coordinate pair `⟨1,0⟩`, whose second coordinate is the integer `0`. Mathematically, the theorem states

$$
\operatorname{snd}(1_{\mathbb Z[\varphi]})=0,
$$

that is, the multiplicative identity of the golden integer ring has no $\varphi$ component.

## Role in the overall proof

Declarations 0133–0136 form the first projection API exposing the coordinates of `Zero GoldenInt` and `One GoldenInt` as `@[simp]` lemmas.

Where 0135 `golden_fst_one` normalizes the first coordinate of the identity to `1`, the present theorem normalizes its second coordinate to `0`. Together they allow extensionality proofs involving `1 : GoldenInt` to avoid explicit coordinate calculations: `simp` can eliminate both coordinates of the identity automatically.

This simplification infrastructure becomes important in the later `golden_fst_add` and `golden_snd_add` lemmas and in the construction of the additive-group and ring structures, where standard notation is repeatedly reduced to coordinate arithmetic.

## Direct dependencies

The declaration directly depends on:

- `GoldenInt`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `instance : One GoldenInt := ⟨goldenOne⟩`
- the second-coordinate projection `GoldenInt.snd`

Conceptually, the dependency chain is

$$
\texttt{goldenOne}
\longrightarrow
\texttt{One GoldenInt}
\longrightarrow
\texttt{golden\_snd\_one}.
$$

No mathematical lemma is needed between these steps; definitional reduction is sufficient.

## Proof / construction flow

The proof is simply

```lean
:= rfl
```

Lean unfolds `(1 : GoldenInt)` through the `One GoldenInt` instance to `goldenOne`, then unfolds `goldenOne = ⟨1,0⟩`. The left-hand side becomes `⟨1,0⟩.snd`, which reduces definitionally to `0`. Both sides are therefore the same term.

The proof content is consequently not a theorem-level derivation but a confirmation that the representation and instance registration were arranged with the desired definitional transparency.

## Lean-specific processing

The theorem has two Lean-specific roles.

First, closing by `rfl` means that the equality is definitional rather than being derived propositionally from a previously proved theorem.

Second, the `@[simp]` attribute installs the rewrite

```lean
(1 : GoldenInt).snd
```

to `0` in the simplifier. This prevents the second coordinate of the identity from surviving unnecessarily in coordinatewise proofs using `GoldenInt.ext`, and it contributes to short `ext <;> simp` proofs of later algebraic laws.

## Redundancy and duplication

0135 `golden_fst_one` and the present theorem expose the two projections of the same raw definition `goldenOne = ⟨1,0⟩`, so structurally they form a deliberate pair of similar declarations.

This is intentional API-level duplication. Giving the simplifier separate projection rules is simple and predictable, and it avoids forcing downstream proofs to unfold the entire structure equality merely to recover one coordinate.

## Optimization candidates

Three approaches can be considered.

1. Keep the current separate `@[simp]` theorems for `fst` and `snd`.
2. Expose one simp lemma for the entire value of `goldenOne` and let projection simplification follow from structure reduction.
3. Recast `GoldenInt` using existing product or quadratic-algebra infrastructure and reuse more generic simplification lemmas.

The current approach creates more declarations, but its simp surface is local and explicit: each coordinate has a visible normal form. For an auditable proof development, that clarity is a reasonable trade-off.

## Required Mathlib imports and import optimization

The standalone source imports `Mathlib` globally. This theorem itself requires only `GoldenInt`, the `One` instance, structure projection, the `@[simp]` attribute, and definitional equality via `rfl`; it invokes no advanced Mathlib theorem.

Thus the theorem alone does not justify importing the whole of `Mathlib`. The true minimal import set depends on how the upstream `GoldenInt` definitions are modularized. Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified and should be treated as an optimization hypothesis.

## Suitability as a Comparator challenge

It is small, but still suitable. One can compare:

- the current dedicated `@[simp]` projection theorem;
- a single whole-value simp lemma for `goldenOne`;
- downstream proofs that use `change` / `rfl` and unfold the representation locally instead of publishing a simp rule.

Metrics include downstream proof length, simplifier stability, unnecessary structure unfolding, readability of simp traces, and API discoverability.

The mathematical content is elementary, but the declaration makes a useful Lean-library-design Comparator challenge about which definitional facts should be promoted to the public simp API.

## Relation to the PDFs and Lean source

The formal basis is the Lean source on the `docs/flt5-theorem-museum-v2` branch together with the theorem-museum documents immediately preceding this declaration. The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

However, no concrete PDF page or section corresponding to this small definitional projection lemma was identified directly in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
```

With 0133–0136, the simplification API for both coordinates of zero and one is complete. The next stage moves to coordinate projections of the binary operation `+`.
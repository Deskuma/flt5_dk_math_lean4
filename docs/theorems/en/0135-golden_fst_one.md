# 0135 — `golden_fst_one`

## Lean type

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

This is a `theorem`, and it is also marked with the `@[simp]` attribute as a coordinate-projection simplification lemma.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents a golden integer

$$
a+b\varphi
$$

by an integer pair `⟨a,b⟩`. In the Lean source, the multiplicative identity is defined and registered through the raw definition

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

Therefore the first coordinate of the standard notation `(1 : GoldenInt)` is the integer `1`. The theorem exposes

$$
\operatorname{fst}(1_{\mathbb Z[\varphi]})=1
$$

as part of the Lean simp API.

## Role in the overall proof

After 0133 `golden_fst_zero` and 0134 `golden_snd_zero` normalize the two coordinates of zero, this theorem begins the coordinate normalization of the multiplicative identity `1`.

Later constructions of `AddCommGroup GoldenInt`, `AddGroupWithOne GoldenInt`, and `CommRing GoldenInt` reduce structural laws to coordinate statements handled by `simp` and `ring`. In that setting, automatic normalization of `(1 : GoldenInt).fst` to `1` is a basic ingredient for facts involving `one_mul`, `mul_one`, casts, and norm computations.

In particular, the theorem records as a small public lemma that the multiplicative identity of `GoldenInt` is not an abstractly introduced value unrelated to the representation, but is definitionally the explicit coordinate pair `⟨1,0⟩`.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `One GoldenInt := ⟨goldenOne⟩`

The theorem does not use 0133 or 0134 in its proof. Those declarations are sibling lemmas belonging to the same projection-simp API family.

Conceptually, the dependency chain is

$$
\texttt{goldenOne}
\longrightarrow
\texttt{One GoldenInt}
\longrightarrow
\texttt{golden_fst_one}.
$$

## Proof / construction flow

The proof is only

```lean
:= rfl
```

and proceeds by definitional reduction:

1. `(1 : GoldenInt)` unfolds through the `One GoldenInt` instance to `goldenOne`.
2. `goldenOne` unfolds to `⟨1,0⟩`.
3. `.fst` computes to the first component `1`.
4. The left-hand and right-hand sides are definitionally identical, so `rfl` closes the theorem.

Thus the proof contains no algebraic reasoning; definitional equality itself is the proof.

## Lean-specific processing

The `@[simp]` attribute registers this theorem as a rewrite rule for the simplifier. Downstream, `simp` can automatically normalize

```lean
(1 : GoldenInt).fst
```

to

```lean
1
```

The important design point is that, although the theorem closes by `rfl`, it is still exported explicitly as a simp lemma. Lean could often compute the expression by unfolding definitions, but a public simp lemma makes downstream proofs less dependent on the concrete unfolding behavior of `goldenOne` and its typeclass instance.

The design therefore preserves definitional transparency while also stabilizing the rewrite interface.

## Redundancy and duplication

Mathematically, the theorem carries little new information because it follows immediately from `goldenOne = ⟨1,0⟩`. Since it also closes by `rfl`, many occurrences could be handled by direct unfolding without naming the lemma.

However, the paired `fst` / `snd` simp lemmas around 0133–0136 provide API symmetry. They hide the raw representation from downstream proofs and expose a stable simplification surface over standard notation. The apparent redundancy is therefore intentional interface redundancy.

## Optimization candidates

Three designs are worth considering:

1. keep the individual projection lemmas, as in the current source, and prioritize an explicit simp API;
2. make `goldenOne` or the `One GoldenInt` definition sufficiently simp-transparent and remove some individual projection lemmas;
3. define a systematic policy for `GoldenInt` extensionality and coordinate simplification, grouping the projection API conceptually.

The second option may reduce line count, but broad unfolding through the simplifier can make simp normal forms depend more strongly on implementation details. The current design spends a few tiny lemmas to preserve a cleaner abstraction boundary.

## Required Mathlib import and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself requires no advanced Mathlib theorem; directly it only needs `GoldenInt`, `goldenOne`, the standard `One` interface, and Lean's basic support for `@[simp]` and `rfl`.

Therefore importing all of `Mathlib` is not necessary for this theorem in isolation. At module scale, however, `GoldenOrder` also constructs `AddCommGroup` and `CommRing`, performs integer arithmetic, and uses tactics such as `ring`, so the true minimal import set is governed by those broader dependencies. No Lean build is performed in this museum pass, so the exact minimal import set is unverified and remains an optimization hypothesis.

## Suitability as a Comparator challenge

Yes, although it is best suited to a small API-design challenge rather than a mathematical challenge.

Possible implementations to compare are:

- an individual `@[simp] theorem golden_fst_one ... := rfl`;
- reliance on simplifier unfolding of the raw definitions;
- a more systematic coordinate-simplification API for `GoldenInt`.

Useful metrics include the amount of explicit `simp` configuration required downstream, resistance to changes in internal definitions, readability of simp traces, the number of lemmas closed by `rfl`, and symmetry of the public API. This is primarily a Comparator for Lean API design and simp-normal-form design.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `GoldenOrder` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. The standalone source blob SHA confirmed in this run is `fab7f3e9cc1d1f2a5ae587ea0261aec194880558`.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page corresponding to this tiny projection theorem was not identified in this run, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

After 0135 fixes the first coordinate of the multiplicative identity, the next lemma exposes that its second coordinate is `0`, meaning that `1` has no component in the golden-ratio direction.
# 0159 — `golden_mul_eq`

## Lean type

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

This is a `theorem` exposing the definitional identity between the raw operation `goldenMul` and the standard multiplication `x * y` obtained through the `Mul GoldenInt` instance. It is registered as a `@[simp]` theorem.

## Mathematical statement and meaning of the declaration

Read elements of `GoldenInt` as

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

The raw multiplication `goldenMul` incorporates the defining relation

$$
\varphi^2=\varphi+1
$$

into its coordinate formula:

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

Thus it represents

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi.
$$

The standard notation `x * y`, however, is already interpreted through

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

and therefore denotes the same operation. The theorem proves no new multiplication law; it exposes the agreement

$$
\texttt{goldenMul x y}=x*y
$$

between the raw API and the standard algebra API as a simp rule.

## Role in the overall proof

By 0155, `GoldenInt` has entered Mathlib's algebra hierarchy through `IsDomain`. From 0156 onward, the source contains a bridge block normalizing raw coordinate operations to standard notation:

```lean
@[simp] theorem golden_add_eq ...
@[simp] theorem golden_neg_eq ...
@[simp] theorem golden_sub_eq ...
@[simp] theorem golden_mul_eq ...
@[simp] theorem golden_pow_eq ...
```

0159 is the multiplication member of this block.

This bridge is especially important downstream. Later modules such as `GoldenDivisibility` and `GoldenEuclidean` contain definitions written with the explicit operation `goldenMul` while also invoking generic Mathlib theorems stated with the standard multiplication `*`. The standalone source later uses `golden_mul_eq` explicitly in rewriting steps inside Euclidean-domain construction and power/conjugation arguments.

The theorem is therefore a small but load-bearing API boundary connecting golden-integer-specific coordinate multiplication to generic commutative-ring reasoning.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- `goldenMul`
- `instance : Mul GoldenInt := ⟨goldenMul⟩`
- Lean's standard `Mul` notation
- reflexivity `rfl`
- the `@[simp]` attribute

Conceptually the dependency chain is

$$
\texttt{GoldenInt}
\longrightarrow
\texttt{goldenMul}
\longrightarrow
\texttt{Mul GoldenInt}
\longrightarrow
\texttt{golden_mul_eq}.
$$

The earlier 0143 `golden_fst_mul` and 0144 `golden_snd_mul` expose the two coordinate projections of standard multiplication. The present theorem serves a different purpose: it identifies the raw function name itself with standard `*` notation.

## Proof / construction flow

The proof is a single `rfl`:

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

Lean elaborates the right-hand side `x * y` by typeclass resolution through `Mul GoldenInt`. Since that instance stores `goldenMul` as its operation, unfolding the right-hand side produces exactly the left-hand side.

No coordinate expansion or ring calculation is required because the two expressions are definitionally equal before theorem rewriting begins.

## Lean-specific processing

The important mechanisms are typeclass resolution, definitional equality, and simp normalization.

The syntax `x * y` is elaborated through the `Mul GoldenInt` instance. Because the registered instance is `⟨goldenMul⟩`, `goldenMul x y` and `x * y` are definitionally the same expression.

Nevertheless, keeping an explicit `@[simp]` theorem gives the simplifier the chosen normalization direction

```lean
goldenMul x y
```

toward

```lean
x * y.
```

This helps downstream proofs leave raw implementation syntax and enter Mathlib's standard algebra vocabulary, where generic lemmas about associativity, commutativity, divisibility, and Euclidean-domain structure are available directly.

## Redundancy and duplication

Logically, the theorem is redundant: unfolding the `Mul` instance already makes the equality reflexive. The multiplication coordinate projections were also exposed earlier by 0143 and 0144.

The API roles are nevertheless distinct.

- 0143–0144 expose the coordinates of standard multiplication.
- 0159 normalizes the raw function name `goldenMul` to standard `*`.
- The raw coordinate layer remains visible for auditability while the downstream proof surface can be expressed with standard notation.

It is therefore better understood as interface layering rather than mathematical duplication.

## Optimization candidates

Possible designs include:

1. Keep the current `@[simp] theorem ... := rfl` bridge.
2. Remove the theorem and unfold the `Mul` instance at use sites.
3. Hide `goldenMul` after algebra-structure construction and expose only standard `*` downstream.
4. Group 0156–0160 explicitly as a raw-to-standard bridge section.
5. Compare the explicit coordinate implementation with an `AdjoinRoot`-based or generic quadratic-algebra implementation.

For a formalization emphasizing auditability, the present design is attractive: the raw operation remains explicit while the bridge theorem permits standard algebra notation everywhere downstream.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself invokes no advanced Mathlib result; directly it requires `GoldenInt`, `goldenMul`, the `Mul GoldenInt` instance, ordinary equality machinery, and `@[simp]`.

Thus all of `Mathlib` is unlikely to be required solely for 0159. The complete `GoldenOrder` module also uses `CommRing`, `IsDomain`, `Zsqrtd`, and tactics or infrastructure such as `ring`, `omega`, and `norm_num`, so the true minimum import set is governed by the module as a whole.

No Lean build is performed in this museum pass, so a finer-grained minimum import set remains unverified and is only an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. Candidate implementations include:

- explicit `goldenMul` plus a `Mul` instance and this bridge theorem;
- inlining the coordinate formula directly into the `Mul` instance;
- hiding the raw operation and exposing only standard `*`;
- implementing the order through generic quadratic-order or `AdjoinRoot` infrastructure.

Useful comparison metrics include the number of facts that close by `rfl`, simp stability, downstream proof size, robustness under definition changes, auditability of the raw coordinate layer, and interoperability with generic Mathlib algebra.

This makes a compact experiment for measuring the trade-off between definitional transparency in a specialized coordinate implementation and reuse in a more abstract algebraic implementation.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, `golden_add_eq`, `golden_neg_eq`, `golden_sub_eq`, the present theorem, and `golden_pow_eq` occur in that order. Immediately afterward the source moves into the golden-specific number-theoretic API beginning with `goldenPhi`, `goldenConj`, and `goldenNorm`.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The specific PDF page or section corresponding to this small API bridge theorem was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

By 0159, raw addition, negation, subtraction, and multiplication have all been connected to standard notation. The next item, 0160, exposes the definitional identity between the recursive raw power `goldenPow` and the standard power `x ^ n` supplied by `CommRing GoldenInt`, closing the raw-operation bridge block.
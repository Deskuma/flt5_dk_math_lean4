# 0158 — `golden_sub_eq`

## Lean type

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

This is a `theorem` exposing the definitional identity between the raw operation `goldenSub` and the standard subtraction `x - y` obtained through the `Sub GoldenInt` instance. It is registered as a `@[simp]` theorem.

## Mathematical statement and meaning of the declaration

Read elements of `GoldenInt` as

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

The upstream raw subtraction is defined by

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

so mathematically

$$
goldenSub(x,y)=x+(-y)=(a-c)+(b-d)\varphi.
$$

On the other hand, the standard notation `x - y` is interpreted through the already registered instance

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

and therefore refers to the same function.

Thus this theorem proves no new subtraction law. It exposes the agreement

$$
\texttt{goldenSub x y}=x-y
$$

between the raw API and the standard algebra API as a named simp rewrite rule.

## Role in the overall proof

By 0155, `GoldenInt` has entered Mathlib's standard algebra hierarchy through `IsDomain`. From 0156 onward, the development contains a block of bridge theorems that normalize the raw coordinate API toward standard notation. 0156 `golden_add_eq` handles addition, 0157 `golden_neg_eq` handles negation, and the present theorem handles subtraction constructed from those operations.

This allows the explicit bootstrap operation `goldenSub` to remain visible and auditable while downstream proofs can use the generic ring and additive-group notation `x - y`.

In source order the block is

```lean
@[simp] theorem golden_add_eq ...
@[simp] theorem golden_neg_eq ...
@[simp] theorem golden_sub_eq ...
@[simp] theorem golden_mul_eq ...
@[simp] theorem golden_pow_eq ...
```

so this theorem is the subtraction member of the raw-operation bridge block.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- `goldenAdd`
- `goldenNeg`
- `goldenSub`
- `instance : Sub GoldenInt := ⟨goldenSub⟩`
- Lean's standard `Sub` notation
- reflexivity `rfl`

Conceptually the dependency chain is

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}
\longrightarrow
\texttt{golden_sub_eq}.
$$

Although 0156 `golden_add_eq` and 0157 `golden_neg_eq` are semantically nearby, the proof term of this theorem does not rewrite with them. Because the `Sub` instance directly stores `goldenSub`, the proof closes with `rfl` alone.

## Proof / construction flow

The proof is one step:

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

Lean elaborates the right-hand side `x - y` through the `Sub GoldenInt` instance. Since the operation stored in that instance is `goldenSub`, unfolding the right-hand side produces exactly `goldenSub x y`.

The two sides are therefore definitionally equal before any theorem rewriting or ring calculation is required, and reflexivity closes the goal.

Conceptually this is the API normalization

$$
\text{raw subtraction}
\longrightarrow
\text{standard subtraction notation}.
$$

## Lean-specific processing

The important Lean mechanisms are typeclass resolution, definitional equality, and the `@[simp]` attribute.

The syntax `x - y` is not merely presentation: Lean resolves a `Sub` instance for `GoldenInt`. Because the registered instance is `⟨goldenSub⟩`, the expressions `goldenSub x y` and `x - y` are definitionally identical without using the theorem itself.

Nevertheless, the explicit `@[simp]` theorem gives the simplifier the chosen normalization direction from

```lean
goldenSub x y
```

to

```lean
x - y.
```

This matches the design of the 0156–0160 bridge block, which normalizes raw implementation syntax toward Mathlib's standard algebra notation.

Since `goldenSub` itself is defined as `goldenAdd x (goldenNeg y)`, it can still be unfolded further into addition and negation when necessary. Ordinary downstream proofs, however, can use this bridge and remain at the standard subtraction layer without depending on that implementation detail.

## Redundancy and duplication

From the viewpoint of logical information, the theorem is redundant because unfolding the instance already makes the equality reflexive. Also, since 0156 and 0157 already connect raw addition and negation to standard notation, one could unfold `goldenSub = goldenAdd + goldenNeg` and reconstruct the same semantic relationship indirectly.

As an API theorem, however, it is useful.

- It preserves the raw operation name `goldenSub` for auditability.
- It gives downstream simp normalization a standard-notation target `x - y`.
- It reduces the need for callers to unfold the `Sub` instance or the definition of `goldenSub`.
- It keeps a uniform bridge API across addition, negation, subtraction, multiplication, and powers in 0156–0160.

Thus the theorem is mathematically trivial but meaningful as an interface declaration.

## Optimization candidates

Possible designs include:

1. Keep the current `@[simp] theorem ... := rfl` bridge.
2. Remove the theorem and unfold `goldenSub` or the `Sub` instance at use sites.
3. Hide `goldenSub` after algebra-structure construction and expose only `x - y` downstream.
4. Group `golden_add_eq` through `golden_pow_eq` explicitly into an API-bridge section with a source comment fixing the intended normalization direction.
5. Compare the current raw-operation-first design with a design in which subtraction is defined directly from standard notation `x + (-y)` after the additive structures are available.

Because this formalization deliberately keeps the raw coordinate layer visible, options 1 or 4 are the most natural. Saving a few lines is less valuable than preserving a readable boundary between the bootstrap layer and the standard algebra interface.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib` globally. This theorem itself invokes no advanced Mathlib theorem; directly it requires `GoldenInt`, `goldenSub`, the `Sub GoldenInt` instance, ordinary equality machinery, and the `@[simp]` attribute.

Therefore all of `Mathlib` is unlikely to be required solely for 0158. The complete `GoldenOrder` module also uses `CommRing`, `IsDomain`, `Zsqrtd`, and tactics or infrastructure such as `ring`, `omega`, and `norm_num`, so the true minimal import set is governed by the module as a whole.

No Lean build is performed in this museum pass, so a more granular minimum import set remains unverified and is explicitly only an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. The comparison concerns Lean API normalization strategy rather than mathematical difficulty.

Candidate approaches include:

- keeping the current explicit `@[simp]` bridge theorem;
- unfolding the raw definition or instance wherever required;
- hiding raw subtraction and exposing only standard `x - y`;
- comparing `goldenSub := goldenAdd x (goldenNeg y)` with a direct coordinate-subtraction implementation.

Useful metrics include simp stability, downstream proof size, robustness under definition changes, frequency with which raw implementation details appear in errors, auditability of the coordinate layer, and interoperability with generic algebra theorems.

In particular, this gives a small clean experiment for measuring the value of retaining an API theorem whose proof is only `rfl`, and for deciding how explicitly a derived subtraction operation should appear in the public surface.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, `goldenSub` is defined as `goldenAdd x (goldenNeg y)`, the `Sub GoldenInt` instance registers `⟨goldenSub⟩`, and `golden_add_eq`, `golden_neg_eq`, the present theorem, `golden_mul_eq`, and `golden_pow_eq` occur in that order.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The specific PDF page or section corresponding to this small API bridge theorem was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

By 0158, addition, negation, and subtraction in the raw API have all been connected to standard notation. The next item, 0159, exposes the same definitional agreement for the raw multiplication `goldenMul`, whose coordinate formula incorporates the reduction `\varphi^2=\varphi+1`, and the standard multiplication `x * y`.
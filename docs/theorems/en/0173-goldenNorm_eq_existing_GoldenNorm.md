# 0173 — `goldenNorm_eq_existing_GoldenNorm`

## Lean type

```lean
/-- Compatibility between the structured norm and the earlier binary quadratic form. -/
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

This is a `theorem` stating that the structure-level norm `goldenNorm` of the `GoldenInt` built directly from integer coordinates `M,N` is definitionally identical to the earlier binary quadratic form `GoldenNorm M N` already used in previous FLT5 layers.

## Mathematical statement and meaning of the declaration

Read the golden integer with coordinates `M,N` as

$$
M+N\varphi.
$$

The structured norm `goldenNorm` returns

$$
N(M+N\varphi)=M^2+MN-N^2,
$$

while the existing API `GoldenNorm M N` denotes the same quadratic form

$$
M^2+MN-N^2.
$$

Thus the mathematical content is

$$
\mathrm{goldenNorm}(M+N\varphi)=\mathrm{GoldenNorm}(M,N).
$$

This is not a new number-theoretic result. It is a representation-compatibility theorem closing the boundary between the structured golden-integer API and the earlier two-coordinate norm API.

## Role in the overall proof

Declaration 0172 `goldenNorm_eq_GoldenNorm` already established, for arbitrary `x : GoldenInt`,

```lean
goldenNorm x = GoldenNorm x.fst x.snd
```

The present theorem is the coordinate-entry version of that bridge. Earlier FLT5 layers often already carry explicit integers `M,N`, so 0173 lets those proofs move into the structured `GoldenInt` API without first introducing a named `x` and then projecting `x.fst` and `x.snd`.

Conceptually,

```text
integer coordinates M,N
    │
    ├─ GoldenNorm M N
    │
    └─ ⟨M,N⟩ : GoldenInt
          │
          └─ goldenNorm ⟨M,N⟩
```

and the theorem states that the two routes meet at the same integer.

The next declaration is `goldenNorm_mul`, which proves the multiplicativity

$$
N(xy)=N(x)N(y)
$$

of the structured norm. Therefore 0173 can be viewed as the final coordinate bridge before the development shifts from representation compatibility to ring-theoretic norm properties.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenNorm`
- the earlier binary quadratic form `GoldenNorm`
- the structure literal `⟨M,N⟩ : GoldenInt`

Because the proof is `rfl`, 0173 does not formally invoke 0172. Although it could be derived from 0172, both theorems close independently from the same definitional equality in the source.

## Proof / construction flow

The proof is a single reflexivity term:

```lean
:= rfl
```

The left-hand side

```lean
goldenNorm (⟨M, N⟩ : GoldenInt)
```

reduces to

```lean
M ^ 2 + M * N - N ^ 2
```

and `GoldenNorm M N` on the right unfolds to exactly the same integer expression.

The proof flow is therefore

```text
goldenNorm ⟨M,N⟩
→ unfold goldenNorm
→ M^2 + M*N - N^2

GoldenNorm M N
→ unfold GoldenNorm
→ M^2 + M*N - N^2

→ rfl
```

No rewrite theorem, simplifier, or ring tactic is required.

## Lean-specific processing

The fact that the theorem closes by `rfl` is the key implementation detail.

It means `goldenNorm` and `GoldenNorm` are not merely propositionally related by a later algebraic proof: after reduction, they are the same term.

The type annotation in

```lean
(⟨M,N⟩ : GoldenInt)
```

also matters. It directs elaboration to the `GoldenInt` constructor rather than an unrelated pair type. Its projections then reduce definitionally to `M` and `N`, which is why not even `simp` is needed.

## Redundancy and duplication

Declaration 0172

```lean
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

specialized at `x := (⟨M,N⟩ : GoldenInt)` gives essentially the same statement as 0173.

There is therefore clear duplication in the theorem surface.

The calling styles differ, however:

- 0172 is natural when a proof already has `x : GoldenInt` and wants to descend to the binary API.
- 0173 is natural when an earlier proof still has explicit coordinates `M,N : ℤ` and wants to enter the structured API.

The duplication is therefore better described as ergonomic API duplication than as mathematical duplication.

## Optimization candidates

Possible designs include:

1. keep both 0172 and 0173 to minimize downstream rewriting;
2. keep 0172 as the primitive theorem and derive 0173 by

```lean
simpa using goldenNorm_eq_GoldenNorm (⟨M, N⟩ : GoldenInt)
```

3. keep only the coordinate theorem and derive the structure theorem through `x.fst` and `x.snd`;
4. define `goldenNorm` directly as `GoldenNorm x.fst x.snd`, making the bridge almost purely documentary;
5. introduce a generic quadratic-form abstraction and obtain both structured and coordinate APIs as specializations of one primitive definition.

The local proof is already minimal. Any meaningful optimization concerns theorem count, naming, and API boundaries rather than tactic length.

## Required Mathlib imports and import optimization

This theorem uses no tactic at all. In isolation it needs only `GoldenInt`, `goldenNorm`, `GoldenNorm`, and basic integer operations.

Therefore the standalone artifact's broad `import Mathlib` is very likely excessive for this theorem alone.

At module scope, however, `GoldenOrder` also uses `Zsqrtd`, algebraic typeclass infrastructure, `omega`, `norm_num`, and `ring`. Any genuine import minimization should therefore be validated for the whole module with a Lean build. This museum run performs no Lean build, so no exact reduced import set is claimed.

## Comparator challenge suitability

Yes, but this is primarily an API-architecture challenge rather than a tactic-performance challenge.

Candidate designs include:

- the current pair of 0172/0173 bridge theorems;
- a single structure bridge;
- a single coordinate bridge;
- making `goldenNorm := GoldenNorm x.fst x.snd` the unique implementation;
- deriving both interfaces from a generic quadratic-norm abstraction.

Useful comparison criteria are downstream rewrite length, theorem-surface size, transparency of definitional unfolding, ease of connecting earlier coordinate-based FLT5 results to `GoldenInt`, and reuse for general quadratic orders.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following 0173 in the Lean source is

```lean
/-- The golden norm is multiplicative. -/
theorem goldenNorm_mul (x y : GoldenInt) :
    goldenNorm (goldenMul x y) = goldenNorm x * goldenNorm y := by
  simp [goldenNorm, goldenMul]
  ring
```

Therefore the next museum entry is **0174 `goldenNorm_mul`**.

With 0172–0173 the representation bridge is complete; 0174 moves on to the substantive algebraic property that the golden norm is multiplicative under golden-integer multiplication.
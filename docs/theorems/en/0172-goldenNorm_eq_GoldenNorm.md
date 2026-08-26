# 0172 — `goldenNorm_eq_GoldenNorm`

## Lean type

```lean
/-- The structure norm is the previously exposed binary golden norm. -/
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

This is a `theorem` stating that the one-argument norm `goldenNorm` on the `GoldenInt` structure is definitionally identical to the earlier two-variable quadratic form `GoldenNorm` when applied to the coordinates `x.fst` and `x.snd`.

## Mathematical statement and meaning of the declaration

Read an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

Upstream, `goldenNorm` is defined by

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

so

$$
N(x)=a^2+ab-b^2.
$$

The present theorem identifies this with the pre-existing binary API

$$
\mathrm{GoldenNorm}(a,b).
$$

Thus its mathematical content is the equality of two presentations of the same norm:

$$
N(a+b\varphi)=\mathrm{GoldenNorm}(a,b)=a^2+ab-b^2.
$$

It introduces no new number-theoretic fact. Its purpose is to close the interface boundary between the older binary quadratic-form API and the newer structure-based API.

## Role in the overall proof

`GoldenOrder` constructs `GoldenInt` as an explicit two-coordinate structure and defines `goldenConj` and `goldenNorm` on it. Earlier FLT5 layers already use the integer binary form `GoldenNorm M N` in square/golden and five-adic bridge formulas.

This theorem connects the two views:

```text
older binary API
GoldenNorm M N
        ↑
        │ fst / snd
        │
structured API
goldenNorm x
```

It therefore permits results written with `GoldenNorm M N` to be reinterpreted as norm statements about the structured element `⟨M,N⟩`, and conversely allows structured norm computations to be returned to the earlier binary theorem surface.

Immediately afterward the source provides the more coordinate-oriented bridge

```lean
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

so 0172 is the general bridge for an already-constructed `GoldenInt`, while the following declaration is a convenience bridge for proofs that still begin with explicit integer coordinates `M,N`.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenNorm`
- the earlier binary quadratic form `GoldenNorm`
- `GoldenInt.fst`
- `GoldenInt.snd`

Because the proof is `rfl`, it depends on no other theorem or tactic.

Conceptually,

$$
\texttt{goldenNorm},\ \texttt{GoldenNorm}
\longrightarrow
\texttt{goldenNorm_eq_GoldenNorm}.
$$

## Proof / construction flow

The proof is exactly one reflexivity term:

```lean
:= rfl
```

After unfolding, the left-hand side `goldenNorm x` becomes

```lean
x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

and `GoldenNorm x.fst x.snd` on the right unfolds to the same expression. No rewrite theorem or algebra tactic is required.

The proof flow is therefore

```text
goldenNorm x
→ unfold goldenNorm
→ x.fst^2 + x.fst*x.snd - x.snd^2

GoldenNorm x.fst x.snd
→ unfold GoldenNorm
→ x.fst^2 + x.fst*x.snd - x.snd^2

→ definitional equality
→ rfl
```

## Lean-specific processing

Closing by `rfl` means the two APIs are not merely propositionally related by a nontrivial proof: their definitions reduce to the same normal form.

This is useful downstream because crossing the bridge adds essentially no algebraic proof burden. If necessary, either side can also be unfolded directly to the same integer polynomial.

The theorem name deliberately retains both naming styles: lowercase `goldenNorm` denotes the structure-level API, while uppercase `GoldenNorm` identifies the pre-existing binary form. The declaration therefore acts as an explicit naming and representation boundary.

## Redundancy and duplication

The immediately following theorem

```lean
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

is nearly a specialization of the present theorem at `x := ⟨M,N⟩`.

There is therefore API-level duplication, although the usage sites differ:

- `goldenNorm_eq_GoldenNorm` is natural when a proof already has a `GoldenInt` value.
- `goldenNorm_eq_existing_GoldenNorm` is natural when a proof still has explicit integer coordinates `M,N` from earlier FLT5 layers.

The duplication can thus be understood as a usability choice providing bridges in both common calling styles.

## Optimization candidates

Possible designs include:

1. keep both bridge theorems for downstream readability;
2. keep only 0172 and derive the coordinate theorem by `simpa using goldenNorm_eq_GoldenNorm (⟨M,N⟩ : GoldenInt)`;
3. keep only the coordinate theorem and derive the structure theorem through `x.fst` and `x.snd`;
4. make `GoldenNorm` the only primitive norm definition and define `goldenNorm` as a wrapper;
5. introduce a general quadratic-form abstraction and obtain both `GoldenNorm` and `goldenNorm` as specializations of it.

The local proof itself is already minimal. Any meaningful optimization concerns API duplication, naming, and module organization rather than tactic length.

## Required Mathlib imports and import optimization

This theorem itself uses no tactics. In isolation it needs only the upstream definitions `GoldenInt`, `goldenNorm`, `GoldenNorm`, and basic integer operations.

Therefore the standalone artifact's global `import Mathlib` is very likely excessive for this theorem alone.

At module level, however, `GoldenOrder` also uses facilities including `Zsqrtd`, `CommRing`, `omega`, `norm_num`, and `ring`. The real minimal import set should therefore be validated at module scope by a Lean build. This museum run does not perform Lean builds, so no exact reduced import list is claimed.

## Comparator challenge suitability

Yes, although this declaration is better suited to comparing API architecture than proof tactics.

Candidate designs include:

- the current pair of structure and coordinate bridge theorems;
- a single structure bridge;
- a single coordinate bridge;
- making `GoldenNorm` primitive and `goldenNorm` a wrapper;
- deriving both interfaces from a generic quadratic-norm abstraction.

Useful comparison criteria are:

- downstream rewrite length;
- number of bridge theorems and API duplication;
- simp normal forms;
- ease of connecting earlier `GoldenNorm M N` results to `GoldenInt`;
- readability of the structured API;
- reuse for general quadratic orders.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following 0172 in the Lean source is

```lean
/-- Compatibility between the structured norm and the earlier binary quadratic form. -/
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

Therefore the next museum entry is **0173 `goldenNorm_eq_existing_GoldenNorm`**. Declaration 0172 bridges an arbitrary structured `GoldenInt` to the older binary norm API; 0173 provides the direct convenience form for the explicit integer coordinates `M,N` used by earlier layers.
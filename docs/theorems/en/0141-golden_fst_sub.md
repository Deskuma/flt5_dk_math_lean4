# 0141 — `golden_fst_sub`

## Lean type

```lean
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

This is a `theorem` marked with the `@[simp]` attribute. It is the first-coordinate projection lemma for subtraction on `GoldenInt`.

## Mathematical statement and meaning of the declaration

Read `GoldenInt` as the golden integer

$$
a+b\varphi
$$

represented by an integer pair `⟨a,b⟩`. For

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

subtraction is

$$
x-y=(a-c)+(b-d)\varphi.
$$

The theorem therefore states, on the first coordinate,

$$
\operatorname{fst}(x-y)=\operatorname{fst}(x)-\operatorname{fst}(y).
$$

The upstream raw operation is constructed from addition and negation:

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

and is connected to the standard notation `x - y` by

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

The present theorem exposes the first coordinate of that standard subtraction as a public simp API whose normal form is ordinary integer subtraction.

## Role in the overall proof

By declaration 0140, the coordinate projection API for zero, one, addition, and negation on `GoldenInt` has been established. This theorem begins the subtraction projection pair by handling the first coordinate.

It supports later proof patterns such as

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
  intros <;> ext <;> simp [add_comm, add_left_comm]
```

After `GoldenInt.ext` reduces an equality of golden integers to two integer-coordinate equalities, `simp` can rewrite `(x - y).fst` to `x.fst - y.fst`. Thus formulas containing subtraction can be transferred from bespoke golden-integer arithmetic to standard integer arithmetic.

This is not itself a fifth-power factorization theorem of FLT5. Its role is infrastructural: it helps lift the explicit coordinate model of the golden integers into Mathlib's standard additive-group and commutative-ring hierarchy, stabilizing the algebra interface used later by norm, divisibility, units, and Euclidean-domain arguments.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenSub`
- `instance : Sub GoldenInt := ⟨goldenSub⟩`
- the projection `GoldenInt.fst`
- standard integer subtraction

Since `goldenSub` itself depends on `goldenAdd` and `goldenNeg`, the conceptual dependency chain is

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}
\longrightarrow
\texttt{golden\_fst\_sub}.
$$

The preceding declarations 0139 `golden_fst_neg` and 0140 `golden_snd_neg` are relevant for understanding the construction of subtraction, but this theorem does not invoke them as theorem-level dependencies; its proof closes by definitional equality alone.

## Proof / construction flow

The proof is the single term `rfl`.

1. Through the `Sub GoldenInt` instance, `x - y` unfolds to `goldenSub x y`.
2. `goldenSub x y` unfolds to `goldenAdd x (goldenNeg y)`.
3. Its first coordinate unfolds to `x.fst + (-y.fst)`.
4. Standard subtraction `x.fst - y.fst` on `Int` reduces to the same term.
5. The two sides are therefore the same Lean term after reduction, so `rfl` closes the theorem.

No `rw`, `simp`, `ring`, or case split is needed in the proof itself. The definition order of the subtraction API is itself sufficient to produce the proof term.

## Lean-specific processing

That `rfl` succeeds means more than mathematical obviousness. It shows that the notation `x - y`, the `Sub GoldenInt` instance, `goldenSub`, `goldenAdd`, `goldenNeg`, and integer subtraction are arranged so that both sides become definitionally equal after reduction.

The `@[simp]` attribute installs the normalization

```lean
(x - y : GoldenInt).fst
```

to

```lean
x.fst - y.fst
```

in the simplifier.

With this dedicated projection theorem, downstream users do not need to unfold `goldenSub`, `goldenAdd`, and `goldenNeg` repeatedly. The internal construction remains hidden while the public API exposes ordinary integer subtraction as the stable normal form.

## Redundancy and duplication

The next declaration, 0142 `golden_snd_sub`, is almost perfectly symmetric; only `fst` versus `snd` changes. This is deliberate API-level duplication.

There is also semantic overlap between this theorem and directly unfolding `goldenSub`, followed by `goldenAdd` and `goldenNeg`. The dedicated `@[simp]` lemma nevertheless prevents broad implementation unfolding and gives the simplifier a stable projection-level normal form.

## Optimization candidates

Three main strategies are worth comparing.

1. Keep separate `fst` / `snd` subtraction projection theorems, as in the current implementation.
2. Mark `goldenSub`, or its `goldenAdd` / `goldenNeg` constituents, for simp unfolding and remove some projection declarations.
3. Recast `GoldenInt` through an existing product or generic quadratic-algebra representation and reuse generic subtraction projection infrastructure.

Approaches 2 or 3 may reduce the declaration count. The current approach, however, locally controls how far `simp` unfolds and keeps proof traces and normal forms predictable. For an FLT5 formalization where auditability matters, this explicit API is a reasonable design choice.

## Required Mathlib imports and import optimization

The standalone source globally uses `import Mathlib`. This theorem itself directly requires only `GoldenInt`, the `Sub` instance, structure projection, `@[simp]`, `rfl`, and basic integer addition, negation, and subtraction infrastructure; it invokes no advanced Mathlib theorem.

Therefore the whole of `Mathlib` should not be required solely for this lemma. The true minimal imports of a modular source are governed by the upstream `GoldenOrder` definitions and basic integer/typeclass infrastructure.

Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified. This point is explicitly an import-optimization hypothesis rather than a confirmed dependency result.

## Suitability as a Comparator challenge

Yes. A useful comparison could test:

- the current dedicated `@[simp]` projection-theorem approach;
- an implementation relying on unfolding `goldenSub`;
- an implementation unfolding all the way to `x + (-y)` and reusing only addition and negation projection lemmas;
- a generic product / quadratic-algebra subtraction API.

Metrics include downstream proof length, number of lemmas closing by `rfl`, simp-trace length, size of unfolded terms, resilience to representation changes, and the automation rate of `ext <;> simp` proofs.

In particular, this theorem makes a compact Comparator challenge for measuring how much definitional transparency is gained by keeping `goldenSub` as a separate raw operation.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch, together with the preceding theorem-museum documents. The dependency order is

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) : (-x).fst = -x.fst := rfl
@[simp] theorem golden_snd_neg (x : GoldenInt) : (-x).snd = -x.snd := rfl
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

The target branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. No concrete PDF page or section corresponding to this small definitional projection lemma was identified in this pass, so no page-level correspondence is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

Declaration 0141 reduces subtraction to integer subtraction on the first coordinate. Declaration 0142 should complete the pair on the second coordinate, giving subtraction a complete two-coordinate simp API.
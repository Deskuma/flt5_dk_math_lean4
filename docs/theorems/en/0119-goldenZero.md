# 0119 — `goldenZero`

## Lean type

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

`goldenZero` is the element of `GoldenInt`, introduced in 0118, whose two integer coordinates are both zero.

$$
goldenZero=(0,0).
$$

Interpreting `GoldenInt` as the coordinate model for $a+b\varphi$, this corresponds to

$$
0+0\varphi=0.
$$

## Mathematical statement

This declaration is a definition rather than a theorem. It gives the concrete candidate for the additive identity in golden-integer coordinates.

An important detail is that the typeclass instance `[Zero GoldenInt]` has not yet been introduced at this point. Later in the source one finds

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

and only there does the ordinary notation `(0 : GoldenInt)` become connected to `goldenZero`.

Thus 0119 belongs to the layer that fixes the coordinate value of zero, while exposure of that value through the `Zero` typeclass is kept separate.

## Role in the whole proof

`GoldenOrder.lean` develops `GoldenInt` into a direct coordinate model of $\mathbb Z[\varphi]$. Article 0118 introduced the carrier, and 0119 supplies its first distinguished element, zero.

The source then proceeds with `goldenOne`, `goldenAdd`, `goldenNeg`, `goldenSub`, and `goldenMul`, and later connects them to the `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` instances. Ring laws are proved afterward, so `goldenZero` is one of the smallest primitive components used in the construction of the ring structure.

It does not yet process FLT5-specific number-theoretic information directly. Its role is in the algebraic infrastructure needed later for golden divisibility, norm arithmetic, the Euclidean structure, and descent.

## Direct dependencies

The direct dependency is essentially only 0118 `GoldenInt`.

- `GoldenInt` — the target type being constructed.
- The integer literal `0 : ℤ` — used for both `fst` and `snd`.
- Structure-constructor notation `⟨0, 0⟩` — shorthand for `GoldenInt.mk 0 0`.

It does not directly depend on the FLT5 equation, five-adic packets, or square-golden packets.

## Construction flow

There is no proof script. The body of the definition is itself a constructor application.

```lean
⟨0, 0⟩
```

From the expected result type `GoldenInt`, Lean interprets this essentially as

```lean
GoldenInt.mk 0 0
```

Therefore, after unfolding,

```lean
(goldenZero).fst = 0
(goldenZero).snd = 0
```

follow by definitional reduction.

The pattern “define the raw operation first, then expose it through a typeclass instance” is repeated immediately with `goldenOne` and the primitive operations that follow.

## Lean-specific processing

### Constructor inference from the expected type

The source writes `⟨0, 0⟩` rather than `GoldenInt.mk 0 0`. Because the declared return type is `GoldenInt`, Lean infers the intended constructor.

### Numeric-literal elaboration

Both `0` literals are elaborated as integers because `GoldenInt.fst` and `GoldenInt.snd` have type `ℤ`.

### Definitional equality

Because `goldenZero` is a definition rather than a theorem, no logical proof is needed to recover its coordinates. `rfl`, `simp [goldenZero]`, or unfolding can expose them directly.

### Separation between raw definition and typeclass instance

The later declaration

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

makes `(0 : GoldenInt)` available. This two-stage design lets the concrete coordinate implementation and its typeclass exposure be audited separately.

## Redundancy and duplication

The declaration itself is minimal and contains no internal redundancy.

At the design level, however, the later instance could be written directly as something like

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

which would eliminate the named definition `goldenZero`. Keeping the raw definition separate instead gives a stable name to the concrete coordinate implementation and keeps it distinct from typeclass construction.

The same pattern is used for `goldenOne`, `goldenAdd`, `goldenNeg`, and related operations, so this is better understood as a consistent API design than as accidental local duplication.

## Optimization candidates

### 1. Inline into the instance

For minimum line count, `goldenZero` could be removed and `⟨0,0⟩` embedded directly in the `Zero GoldenInt` instance. The cost is losing a separately named raw implementation that can be referenced explicitly by downstream proofs.

### 2. Add coordinate simp lemmas

One could add, for example,

```lean
@[simp] theorem goldenZero_fst : goldenZero.fst = 0 := rfl
@[simp] theorem goldenZero_snd : goldenZero.snd = 0 := rfl
```

but these may be unnecessary if the later instance already makes expressions such as `(0 : GoldenInt).fst` reduce cleanly with `rfl` or `simp`.

### 3. Bundle primitive operations earlier

Zero, one, addition, negation, subtraction, and multiplication could be supplied directly while constructing a larger algebraic structure. The current source instead keeps the coordinate operations as small named definitions, which makes the later ring-law proofs and implementation audit easier to follow.

## Required Mathlib imports and import optimization

The standalone source begins with

```lean
import Mathlib
```

but `goldenZero` itself needs no new Mathlib theorem once `GoldenInt` is available. It only needs the structure constructor and integer literals, so importing all of `Mathlib` solely for 0119 would be excessive.

At the module level, however, later parts of `GoldenOrder.lean` use ring structures, integer arithmetic, maps into `Zsqrtd 5`, and proofs involving `simp` and `ring`, so the minimal import set for the whole module is necessarily larger than for this declaration alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified. Import reduction is therefore recorded as a design candidate rather than as an established source property.

## Comparator challenge suitability

As a standalone declaration this is too small to make a substantial challenge, but it fits well as part of a comparison of primitive-operation designs for `GoldenInt`.

Natural variants are: (a) the current two-stage raw-definition + instance design, (b) direct inlining into the typeclass instance, and (c) supplying zero/one/operations as part of a larger ring-structure construction.

Useful comparison criteria include transparency under unfolding, `simp` behavior, separation from instance search, brevity of later ring-law proofs, and auditability of the concrete coordinate implementation.

## Sources and scope of inference

The formal source is the `DkMath/FLT/Five/GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. There `goldenZero` appears immediately after `GoldenInt`, followed by `goldenOne`, the coordinate operations, and later the corresponding `Zero GoldenInt` and related instances.

The target branch also contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The PDF body location corresponding specifically to `goldenZero` was not directly inspected in this pass, so no page number, section number, or PDF wording is inferred.

The proposed simp lemmas and import minimization are optimization candidates, not claims about the current source.

## Next declaration to read

The next declaration in dependency order is

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

Where 0119 supplies the additive identity candidate $0$, the next declaration supplies the multiplicative identity candidate $1$ in the same coordinate model. Therefore `goldenOne` is the natural subject of the next article.

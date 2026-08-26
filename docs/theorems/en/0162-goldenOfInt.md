# 0162 — `goldenOfInt`

## Lean type

```lean
/-- Embed an integer in the golden order. -/
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

This is a `def`, not a theorem. It embeds an integer `a : ℤ` into the first basis direction of the golden-integer ring `GoldenInt`.

## Mathematical statement and meaning of the declaration

Reading an element of `GoldenInt` as

$$
x=a+b\varphi,
$$

`goldenOfInt a` represents

$$
a=a+0\varphi.
$$

It is therefore the most direct coordinate embedding of the ordinary integers $\mathbb Z$ into the constant part of the golden order $\mathbb Z[\varphi]$.

Where 0161 `goldenPhi := ⟨0,1⟩` specifies the second basis direction $\varphi$, 0162 places integers along the first basis direction $1$. Together they expose the two basic axes of the coordinate expression $a+b\varphi$.

## Role in the overall proof

`goldenOfInt` is a raw API bridge between ordinary integer arithmetic and golden-integer arithmetic. `GoldenInt` has already been equipped with `AddGroupWithOne`, `CommRing`, and `IsDomain`, so a standard integer cast is already available. This definition nevertheless provides a named coordinate-level entry point that directly exposes the representation `⟨a,0⟩`.

That explicitness is useful when auditing later constructions involving conjugation, norm, units, divisibility, and the Euclidean-domain structure, because ordinary integers can be recognized immediately as elements with zero $\varphi$-coordinate rather than being hidden behind a generic coercion.

## Direct dependencies

The immediate dependencies are mainly:

- `GoldenInt`
- the integer type `ℤ`
- `GoldenInt.fst`
- `GoldenInt.snd`

No theorem is needed to construct the value: the structure literal `⟨a,0⟩` is sufficient.

Semantically, the earlier `goldenAddGroupWithOne` is also important because its integer cast uses the same coordinate rule:

```lean
intCast := fun z => ⟨z, 0⟩
```

Thus `goldenOfInt a` and the standard cast `(a : GoldenInt)` are based on the same representation principle.

## Proof / construction flow

There is no proof script. The definition is simply

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

Mathematically this is the standard inclusion

$$
\mathbb Z\hookrightarrow\mathbb Z[\varphi],\qquad a\mapsto a+0\varphi.
$$

## Lean-specific processing

Because `GoldenInt` is a structure with two integer coordinates, Lean elaborates `⟨a,0⟩` from the expected type and fills the corresponding fields.

A key distinction is that `goldenOfInt` itself is not the `Int.cast` notation. The standard cast `(a : GoldenInt)` is resolved through the previously constructed `AddGroupWithOne` / `CommRing` instances, whereas `goldenOfInt a` is an independently named raw coordinate API.

Since both use the same coordinate formula, a future bridge theorem of the form `goldenOfInt a = (a : GoldenInt)` would likely close by `rfl`. The existence of such a dedicated theorem was not confirmed in this pass, so that observation is recorded only as a plausible optimization.

## Redundancy and duplication

`goldenOfInt a` and the standard cast `(a : GoldenInt)` are semantically close and may appear redundant. The upstream `intCast` also uses `⟨z,0⟩`, so the coordinate formulas coincide.

Their API roles differ, however:

- the standard cast belongs to Mathlib's generic algebra hierarchy;
- `goldenOfInt` belongs to the explicit coordinate layer of the golden-order implementation.

This mirrors the same design philosophy seen in the raw operations `goldenAdd`, `goldenMul`, and their standard-notation bridges: the implementation preserves an auditable coordinate layer while still participating in generic algebra APIs.

## Optimization candidates

1. Keep the current two-layer design with an explicit raw constructor and the standard cast.
2. Add an `@[simp]` bridge theorem `goldenOfInt a = (a : GoldenInt)` to normalize raw syntax into standard algebra notation.
3. Redefine `goldenOfInt` as a thin alias returning `(a : GoldenInt)`, provided the bootstrap order and definitional transparency remain acceptable.
4. Under a more general quadratic-order abstraction, replace this declaration by the canonical base-ring embedding.

The current `⟨a,0⟩` representation is extremely transparent and makes the coordinate semantics immediately visible.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but `goldenOfInt` in isolation requires only the definition of `GoldenInt`, the integer type, and the zero literal.

No advanced Mathlib import is needed specifically for this declaration. The complete `GoldenOrder` module also uses `Zsqrtd`, ring tactics, `omega`, `norm_num`, and related infrastructure, so its true minimal import set would need to be checked by a Lean build. No build is performed in this museum pass, so import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementation families to compare include:

- the current raw coordinate definition `goldenOfInt a := ⟨a,0⟩`;
- a design using only the standard cast `(a : GoldenInt)`;
- the canonical base-ring embedding of a generic quadratic-order abstraction;
- an integer embedding arising from an `AdjoinRoot`- or quotient-based implementation.

Evaluation criteria include the number of bridge lemmas closed by `rfl`, simplicity of bootstrap construction, simp normal forms, transparency of coordinate unfolding, and generalizability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. The source order already confirmed by the 0161 document places `goldenOfInt` immediately after `goldenPhi`, followed by `goldenConj` and `goldenNorm`.

The target branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page corresponding to this one-line definition was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is `goldenConj`.

For a golden integer

$$
a+b\varphi,
$$

the next step defines the conjugation induced by the conjugate golden root $\varphi' = 1-\varphi$ in explicit coordinates. With 0161 `goldenPhi` and 0162 `goldenOfInt`, the two basis directions are now explicit, so the following declaration begins expressing the Galois-type symmetry of that basis.
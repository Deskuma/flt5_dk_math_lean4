# 0161 — `goldenPhi`

## Lean type

```lean
/-- The basis element `phi`. -/
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

This is a `def`, not a theorem. It defines the distinguished basis element $\varphi$ of the golden-integer ring `GoldenInt` as the coordinate pair `⟨0,1⟩`.

## Mathematical statement and meaning of the declaration

Reading an element of `GoldenInt` as

$$
x=a+b\varphi,
$$

`goldenPhi` represents

$$
\varphi=0+1\varphi.
$$

Its first coordinate is therefore $0$ and its second coordinate is $1$.

Declarations 0156–0160 formed the API bridge that normalizes the raw operations into standard algebra notation. Declaration 0161 now reintroduces the arithmetic data specific to the golden order by naming its distinguished generator inside the already constructed `CommRing GoldenInt`.

## Role in the overall proof

`goldenPhi` is the reference element that makes the subsequent golden-order arithmetic concrete. Immediately afterward, the source defines `goldenOfInt`, `goldenConj`, and `goldenNorm`, and then proves

```lean
@[simp] theorem golden_phi_sq :
    goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne := by
  decide
```

which formalizes the defining relation

$$
\varphi^2=\varphi+1.
$$

The following theorems also show that conjugation sends $\varphi$ to $1-\varphi$ and that $N(\varphi)=-1$. Later, `goldenUnit_phi` uses the norm computation to prove that $\varphi$ is a unit.

Thus 0161 is not merely a convenience constant: it injects the specifically “golden” arithmetic content back into the abstract ring structure.

## Direct dependencies

The immediate dependencies are mainly:

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`

The construction itself needs essentially no theorem and almost no typeclass inference beyond elaborating the structure literal `⟨0,1⟩` at the expected type `GoldenInt`.

Semantically, however, the previously constructed `CommRing GoldenInt` and the raw multiplication `goldenMul` are important because they let `goldenPhi` function as a ring generator rather than merely a coordinate vector.

## Proof / construction flow

There is no proof script. The definition is simply

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

Mathematically, this selects the second basis vector in the basis $(1,\varphi)$.

## Lean-specific processing

Since `GoldenInt` is a structure with two integer coordinates, Lean elaborates `⟨0,1⟩` from the expected type and fills the corresponding fields.

`goldenPhi` itself is not marked `@[simp]`. Instead, downstream proofs unfold it locally with expressions such as `simp [goldenPhi]` or `norm_num [goldenNorm, goldenPhi]`.

This preserves the meaningful symbolic name `goldenPhi` by default, rather than globally reducing every occurrence to the raw coordinate pair `⟨0,1⟩`.

## Redundancy and duplication

One could write `⟨0,1⟩` directly wherever the generator is needed, so a named constant might seem redundant. In the downstream source, however, many declarations refer to the same mathematical element, including

- `golden_phi_sq`
- `goldenConj_phi`
- `goldenNorm_phi`
- `goldenUnit_phi`
- `goldenTau_eq_phi_mul_sqrtFive`

Using a named constant therefore makes the proof intent substantially clearer than repeatedly exposing a coordinate literal.

## Optimization candidates

1. Keep the current explicit named constant `goldenPhi`.
2. Define the generator through a more general quadratic-order abstraction and specialize it to the golden order.
3. Consider adding projection lemmas such as `(goldenPhi).fst = 0` and `(goldenPhi).snd = 1` only if repeated downstream use justifies them; otherwise `simp [goldenPhi]` is sufficient.
4. If the implementation later moves toward `AdjoinRoot`, provide a bridge theorem between the abstract root and this coordinate generator.

The current representation is extremely transparent and makes the local FLT5 coordinate calculations easy to audit.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but `goldenPhi` itself needs only the definition of `GoldenInt` and integer literals.

No advanced Mathlib import is needed by this declaration in isolation. The complete `GoldenOrder` source also uses `Zsqrtd`, `ring`, `omega`, `norm_num`, and related infrastructure, so the true minimal module import set would need to be verified by a Lean build. No build is run in this museum pass, so import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementations to compare include:

- the current explicit coordinate generator `goldenPhi := ⟨0,1⟩`;
- a specialization of a generic quadratic-order generator;
- a bridge from an `AdjoinRoot`- or quotient-based generator.

Metrics could include how directly `golden_phi_sq` is proved, the proof burden for conjugation, norm, and unit theorems, transparency of coordinate unfolding, and generalizability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this definition appears immediately after `golden_pow_eq`, followed by `goldenOfInt`, `goldenConj`, `goldenNorm`, and `golden_phi_sq`.

The target branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page corresponding to this one-line definition was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- Embed an integer in the golden order. -/
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

Where `goldenPhi` supplies the second basis direction $\varphi$, `goldenOfInt` embeds ordinary integers along the first basis direction. Together they make the two basic axes of the coordinate expression $a+b\varphi$ explicit.
# 0218 — `goldenQuotientNumerator_snd`

## Lean type

```lean
theorem goldenQuotientNumerator_snd (x y : GoldenInt) :
    (goldenQuotientNumerator x y).snd =
      x.snd * y.fst - x.fst * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

This is a `theorem` expanding the second coordinate of `x * conjugate(y)`, as defined by 0216 `goldenQuotientNumerator`, into an explicit polynomial in the integer coordinates of `x` and `y`.

## Mathematical statement

Write `x=a+bφ` and `y=c+dφ`. From 0163 `goldenConj`,

$$
\overline y=(c+d)-d\varphi.
$$

The golden multiplication law is

$$
(A+B\varphi)(C+D\varphi)
=(AC+BD)+(AD+BC+BD)\varphi.
$$

Applying this to `x` and `conj(y)`, the second coordinate is

$$
b(c+d)+a(-d)+b(-d)=bc-ad.
$$

Thus the theorem exposes

$$
(x\overline y)_{\varphi}=bc-ad.
$$

Together with 0217 for the first coordinate, it yields the complete numerator formula

$$
x\overline y
=
\bigl(a(c+d)-bd\bigr)
+
\bigl(bc-ad\bigr)\varphi.
$$

## Role in the full proof

The `GoldenEuclidean` layer rationalizes the quotient by

$$
\frac{x}{y}=\frac{x\overline y}{N(y)}
$$

for nonzero `y`, then rounds the two rational coordinates to the nearest integers in order to construct a Euclidean quotient.

Declaration 0216 packages the numerator `x * conjugate(y)` as a `GoldenInt`. Declarations 0217 and 0218 then expose its two integral coordinates. The immediately following declaration 0219 `goldenQuotientCoords` divides those coordinates by `goldenNorm y` and moves into `GoldenRat = ℚ × ℚ`.

Farther downstream, `goldenRemainder_norm_rat_identity` rewrites by both `goldenQuotientNumerator_fst` and the present theorem while reconstructing the original coordinates `x.fst` and `x.snd` from quotient coordinates. The theorem is therefore not merely cosmetic: it is a direct algebraic input to the norm-contraction proof for the Euclidean remainder.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0216 `goldenQuotientNumerator`
- 0163 `goldenConj`
- 0124 `goldenMul`
- the `ring` tactic
- the upstream coordinate simp API

Conceptually,

$$
\texttt{goldenQuotientNumerator}
+\texttt{goldenConj}
+\texttt{goldenMul}
\longrightarrow
\text{explicit second-coordinate polynomial}.
$$

## Proof flow

```lean
simp [goldenQuotientNumerator, goldenMul, goldenConj]
ring
```

1. Expand `goldenQuotientNumerator x y` to `goldenMul x (goldenConj y)`.
2. Expand `goldenConj y` to coordinates `⟨y.fst + y.snd, -y.snd⟩`.
3. Expand the second-coordinate formula of `goldenMul`.
4. Let `simp` simplify projections, signs, and elementary integer operations.
5. Let `ring` normalize the remaining polynomial identity to

$$
x.snd\cdot y.fst-x.fst\cdot y.snd.
$$

## Lean-specific processing

No `ext` is required because the goal is already an equality in `ℤ`, namely the `.snd` projection, rather than an equality of whole `GoldenInt` values.

`simp [goldenQuotientNumerator, goldenMul, goldenConj]` aggressively unfolds the raw coordinate API and reduces the projection to an integer expression. `ring` then handles associativity, commutativity, distributivity, and sign normalization.

The resulting expression

```lean
x.snd * y.fst - x.fst * y.snd
```

has a determinant-like cross-term shape. Mathematically it is the `φ`-coordinate of the rationalized numerator and will later be combined with the denominator `N(y)` in the quotient coordinates.

## Redundancy and duplication

Declarations 0217 and 0218 are a symmetric pair of projection theorems, and their proofs follow the same pattern.

One alternative would be a single theorem returning both coordinate formulas, for example a conjunction containing the `.fst` and `.snd` identities.

However, downstream proofs often rewrite coordinates separately, so individual projection theorems are convenient for `rw` and `simp`. In `goldenRemainder_norm_rat_identity`, both names can simply be supplied to the rewrite set. The current API is therefore practically well-shaped despite the local duplication.

## Optimization candidates

1. **Derive 0217 and 0218 from one pair theorem**
   - perform the coordinate expansion once and expose the projections as corollaries.

2. **Prefer standard multiplication notation**
   - define `goldenQuotientNumerator` using `x * goldenConj y` and reduce exposure of raw `goldenMul`.

3. **Introduce a dedicated numerator structure**
   - give semantic field names to the two coordinates; this may improve readability but is heavier than reusing `GoldenInt`.

4. **Generalize to a quadratic order**
   - derive conjugation, norm, and rationalized-numerator formulas for a relation `θ²=pθ+q`, then specialize to the golden case.

The local proof is already concise, so most optimization opportunities concern API architecture rather than tactic compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The theorem itself directly needs only a small surface:

- integer ring operations
- `simp`
- `ring`

`GoldenInt`, `goldenMul`, `goldenConj`, and `goldenQuotientNumerator` are project-local upstream declarations.

A standalone version of this theorem should need much less than all of `Mathlib`, but the complete `GoldenEuclidean.lean` module also uses rationals, rounding, absolute value, `field_simp`, `nlinarith`, and Euclidean-domain infrastructure. The true minimal import set therefore needs to be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Possible variants include:

- A: current `simp [defs]; ring`
- B: adjust definitions so the second-coordinate identity is nearly definitional
- C: prove one pair theorem for both 0217 and 0218
- D: derive the formula from a bundled `RingEquiv` / conjugation / norm API
- E: specialize a generic quadratic-order formula

Useful metrics include proof size, dependence on raw definitions, rewrite ergonomics, generalizability, and usefulness in the later `field_simp` reconstruction proof.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0217 and immediately before `goldenQuotientCoords`. Later, `goldenRemainder_norm_rat_identity` explicitly rewrites by both 0217 and 0218.

The branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small coordinate theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0219 `goldenQuotientCoords`**:

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

With the two integral coordinates of `x * conjugate(y)` now exposed by 0217 and 0218, 0219 divides each by `N(y)` to construct the actual rational quotient coordinates. The next stage then rounds those coordinates to obtain the nearest integral golden quotient and its remainder.

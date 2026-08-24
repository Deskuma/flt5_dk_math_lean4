# 0217 — `goldenQuotientNumerator_fst`

## Lean type

```lean
theorem goldenQuotientNumerator_fst (x y : GoldenInt) :
    (goldenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) - x.snd * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

This is a `theorem` expanding the first coordinate of `x * conjugate(y)`, named in 0216 `goldenQuotientNumerator`, into an explicit integer polynomial in the coordinates of `x` and `y`.

## Mathematical statement

Write

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

By 0163 `goldenConj`,

$$
\overline y=(c+d)-d\varphi.
$$

Using the golden multiplication law

$$
(a+b\varphi)(e+f\varphi)=(ae+bf)+(af+be+bf)\varphi
$$

with `e=c+d` and `f=-d`, the first coordinate becomes

$$
a(c+d)+b(-d)=a(c+d)-bd.
$$

The theorem exposes exactly this identity in Lean coordinates:

$$
(x\overline y).\mathrm{fst}
=x.\mathrm{fst}(y.\mathrm{fst}+y.\mathrm{snd})
-x.\mathrm{snd}\,y.\mathrm{snd}.
$$

## Role in the full proof

`GoldenEuclidean.lean` constructs Euclidean division by representing the quotient of nonzero `y` as

$$
\frac{x\overline y}{N(y)},
$$

moving to rational coordinates, rounding to a nearby lattice point, and proving strict norm contraction for the remainder.

Declaration 0216 fixes the numerator `x\overline y` as a `GoldenInt`. To pass from that integer object to `GoldenRat = ℚ × ℚ`, its two integer coordinates must be made explicit.

0217 supplies the first coordinate. The following 0218 `goldenQuotientNumerator_snd` supplies the second, and `goldenQuotientCoords` divides both by `goldenNorm y` to construct the rational quotient coordinates.

Later remainder identities use these coordinate formulas in reverse to identify the rationalized remainder with the quotient-coordinate rounding error. Thus 0217 is not merely a projection lemma; it is one half of the coordinate API underlying the Euclidean contraction argument.

## Direct dependencies

The direct definitional dependencies are:

- 0216 `goldenQuotientNumerator`
- 0124 `goldenMul`
- 0163 `goldenConj`
- `GoldenInt`

The proof uses the tactics `simp` and `ring`. No new number-theoretic theorem is required; after unfolding the raw coordinate definitions, the goal is an integer polynomial identity.

## Proof flow

```lean
simp [goldenQuotientNumerator, goldenMul, goldenConj]
ring
```

The `simp` step performs the structural expansion:

1. unfold `goldenQuotientNumerator x y` to `goldenMul x (goldenConj y)`;
2. unfold `goldenConj y` to the coordinates `⟨y.fst + y.snd, -y.snd⟩`;
3. expand the first coordinate of `goldenMul`.

The remaining goal is an equality of integer polynomial expressions. `ring` normalizes addition, subtraction, signs, and products and closes the identity.

## Lean-specific processing

Because the theorem concerns only `.fst`, it does not need `GoldenInt.ext`; Lean can compute the relevant projection directly after unfolding.

The left-hand side is expressed through the raw `goldenMul` / `goldenConj` API, while the right-hand side uses ordinary integer operations. `simp` removes this representation boundary and `ring` absorbs differences in algebraic normal form.

Using `ring` after controlled unfolding also makes the proof less sensitive to parenthesization and to the exact order in which the negative second conjugate coordinate is expanded.

## Redundancy and duplication

0217 and the following 0218 are paired projection theorems for the same intermediate object and therefore have nearly identical proof architecture.

One could instead define `goldenQuotientNumerator` directly by its explicit coordinate pair, potentially making the projection results closer to `rfl`. The current design deliberately keeps the mathematical definition “multiply by the conjugate” as the source of truth and derives coordinate formulas as theorems. This preserves clearer mathematical provenance.

## Optimization candidates

1. Define `goldenQuotientNumerator` using standard notation `x * goldenConj y` to reduce the raw/standard API boundary.
2. Prove one equality of coordinate pairs and derive 0217/0218 by projection.
3. Introduce a helper packaging both quotient-numerator coordinates for reuse by `goldenQuotientCoords`.
4. Generalize the coordinate formula for `x * conj y` to a generic quadratic order and specialize to the golden order.
5. Keep the current small projection theorems to preserve local downstream rewrite usability.

The current design has more theorem granularity, but it lets later proofs refer to exactly the coordinate they need.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is mainly `simp` and `ring`; the mathematical objects themselves come from the upstream `GoldenInt` API.

The declaration alone should require much less than all of `Mathlib`, but the full `GoldenEuclidean.lean` module also uses `round`, `abs_sub_round`, `nlinarith`, `linarith`, `field_simp`, and Euclidean-domain infrastructure. Because this museum pass does not run a Lean build, the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include the current `simp + ring` proof, a `ring_nf`-centered proof, a single coordinate-pair equality followed by projections, an explicit-coordinate definition of `goldenQuotientNumerator`, and a generic quadratic-order abstraction.

Comparison axes include proof size, robustness under changes to raw definitions, visibility of mathematical provenance, downstream rewrite ergonomics, and dependence on the simp set.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository's 0216 document records this theorem as the next declaration, including its Lean type and proof. Japanese and English PDFs also exist on the target branch, but the exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0218 `goldenQuotientNumerator_snd`**.

0217 exposes the first coordinate of `x * conjugate(y)`; 0218 exposes the second coordinate

$$
(x\overline y).\mathrm{snd}=x.\mathrm{snd}\,y.\mathrm{fst}-x.\mathrm{fst}\,y.\mathrm{snd}.
$$

Once both coordinates are available, `goldenQuotientCoords` divides them by `N(y)` and constructs the actual rational quotient coordinates.

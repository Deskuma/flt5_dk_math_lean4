# 0223 — `golden_quotient_mul_add_remainder`

## Lean type

```lean
theorem golden_quotient_mul_add_remainder (x y : GoldenInt) :
    y * goldenQuotient x y + goldenRemainder x y = x := by
  simp [goldenRemainder, golden_mul_eq]
  ring
```

This is a `theorem` stating that the quotient from 0220 `goldenQuotient` and the remainder from 0221 `goldenRemainder` satisfy the standard Euclidean division reconstruction identity.

## Mathematical statement and meaning of the declaration

Declaration 0221 defines the remainder by

$$
r=x-qy,
$$

where

$$
q=goldenQuotient(x,y),\qquad r=goldenRemainder(x,y).
$$

The present theorem rearranges this definition into

$$
yq+r=x.
$$

Because the golden order is commutative, $qy=yq$, so

$$
yq+(x-qy)=x
$$

is simply a commutative-ring identity. Thus the theorem introduces no new number-theoretic content; it is an interface theorem certifying that the explicitly constructed quotient/remainder pair is oriented exactly as required by the Euclidean-domain API.

## Role in the full proof

`GoldenEuclidean.lean` constructs a concrete Euclidean division algorithm on `GoldenInt`.

The relevant sequence is:

1. 0219 `goldenQuotientCoords` constructs rational quotient coordinates.
2. 0220 `goldenQuotient` rounds those coordinates to the nearest golden-integer lattice point.
3. 0221 `goldenRemainder` defines $r=x-qy$.
4. 0222 `goldenQuotient_zero` closes the divisor-zero quotient law.
5. **0223 proves the reconstruction identity $yq+r=x$.**
6. From 0224 onward, the absolute norm is packaged as the Euclidean size and the remainder is shown to decrease strictly.
7. The final `goldenEuclideanDomain` instance installs the quotient, remainder, size, and their laws into `EuclideanDomain GoldenInt`.

Thus 0223 supplies the **correctness** of the quotient/remainder pair, while later declarations supply the **smallness** of the remainder. Both are required for Euclidean division.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0159 `golden_mul_eq`
- the `CommRing GoldenInt` structure
- the `ring` tactic

The theorem does not depend on the rational-coordinate contraction estimate, on 0215 `goldenNorm_ne_zero_of_ne_zero`, or on a nonzero-divisor hypothesis. The reconstruction identity follows purely from the definition of the remainder.

Conceptually,

$$
\texttt{goldenRemainder}(x,y)=x-qy
\Longrightarrow
yq+\texttt{goldenRemainder}(x,y)=x.
$$

## Proof flow

The current proof has two steps:

```lean
by
  simp [goldenRemainder, golden_mul_eq]
  ring
```

### 1. Normalize the remainder and raw multiplication

Unfolding `goldenRemainder` gives a goal conceptually of the form

```lean
y * goldenQuotient x y +
  (x - goldenMul (goldenQuotient x y) y) = x
```

The theorem `golden_mul_eq` connects the raw operation

```lean
goldenMul (goldenQuotient x y) y
```

with standard multiplication

```lean
goldenQuotient x y * y.
```

### 2. Close the commutative-ring identity with `ring`

The remaining expression has the form

$$
yq+(x-qy)=x,
$$

and `ring` normalizes commutativity, addition, and subtraction in the already constructed `CommRing GoldenInt`.

## Lean-specific processing

### 1. The statement uses `y * q`, while the remainder definition uses `q * y`

Declaration 0221 defines

```lean
goldenRemainder x y :=
  x - goldenMul (goldenQuotient x y) y
```

with the product ordered as `q*y`. The theorem statement is written as `y*q+r=x`.

This mismatch is mathematically harmless because `GoldenInt` is commutative, and `ring` absorbs the reordering.

### 2. `golden_mul_eq` bridges the raw and standard APIs

The remainder definition uses the raw multiplication `goldenMul`, while the theorem statement uses standard `*`. Declaration 0159 `golden_mul_eq` exposes their definitional compatibility to simplification.

### 3. No `y ≠ 0` hypothesis is required

The theorem is valid for every `x,y : GoldenInt`, including `y=0`. This matches the total quotient/remainder operations expected by the Euclidean-domain structure.

The divisor-zero policy was separately recorded in 0222, but the present identity does not need to invoke it explicitly: the remainder definition alone is sufficient.

## Redundancy and duplication

The theorem is almost definitional once `goldenRemainder` is unfolded, so it carries little independent mathematical information. Its value is API-level: it can be supplied directly to the final Euclidean-domain structure as the quotient/remainder reconstruction law.

The appearance of `golden_mul_eq` is caused by maintaining both a raw `goldenMul` API and the standard `*` notation. If `goldenRemainder` were defined directly as

```lean
x - goldenQuotient x y * y
```

this bridge might disappear from the proof.

On the other hand, keeping the raw operation visible preserves the explicit-coordinate audit trail used throughout the FLT5 development.

## Optimization candidates

1. **Define `goldenRemainder` using standard multiplication**
   - this may remove the `golden_mul_eq` rewrite.

2. **Align the theorem statement with the order `q*y+r=x`**
   - this would match the remainder definition more directly, although the final `EuclideanDomain` field may prefer the current `y*q+r=x` orientation.

3. **Try a pure `simpa [goldenRemainder, golden_mul_eq]` proof**
   - whether simplification alone handles the commutativity is unverified because no Lean build is run in this museum pass.

4. **Bundle quotient and remainder together**
   - a structure carrying quotient, remainder, reconstruction identity, and strict-size certificate could make the final instance assembly more explicit.

5. **Abstract the reconstruction lemma over a generic commutative ring**
   - the implication from `r := x-qy` to `yq+r=x` is not specific to the golden order.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is small:

- `simp`
- the `ring` tactic
- commutative-ring addition, multiplication, and subtraction

The theorem itself does not use rounding, `field_simp`, `nlinarith`, or nearest-integer estimates.

The surrounding `GoldenEuclidean.lean` module does use rational rounding, nonlinear inequalities, denominator clearing, and the Euclidean-domain hierarchy, so module-level import minimization is a broader task.

No Lean build is performed here, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current `simp [goldenRemainder, golden_mul_eq]; ring`
- B: define the remainder using standard `*` and close mostly by simplification
- C: an explicit `calc` proof of `y*q + (x-q*y) = x`
- D: reuse a reconstruction law from a quotient/remainder bundle
- E: apply a generic commutative-ring reconstruction lemma

Useful comparison axes include proof size, exposure of the raw/standard API boundary, dependence on `ring`, robustness under implementation changes, naturalness for the final `EuclideanDomain` instance, and generalizability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source places this theorem immediately after 0222 `goldenQuotient_zero` and immediately before 0224 `goldenEuclideanSize`.

The branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0224 `goldenEuclideanSize`**:

```lean
/-- Euclidean size is the natural absolute value of the golden norm. -/
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

By 0223, the quotient/remainder reconstruction law is complete. Declaration 0224 now defines the Euclidean induction measure as

$$
|N(x)|\in\mathbb N,
$$

which will then be shown positive on nonzero elements, multiplicative, and strictly decreasing on remainders.
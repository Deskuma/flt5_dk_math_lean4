# 0209 — `GoldenRat`

## Lean type

```lean
/-- Rational coordinates in the basis `1, phi`. -/
abbrev GoldenRat := ℚ × ℚ
```

This is an `abbrev`, not a theorem. It represents rational coordinates in the golden basis `1, φ` simply as the product type `ℚ × ℚ`.

## Mathematical statement and meaning of the declaration

Where `GoldenInt` represents integral coordinates

$$
a+b\varphi,\qquad a,b\in\mathbb Z,
$$

`GoldenRat` represents rational coordinates in the same basis,

$$
u+v\varphi,\qquad u,v\in\mathbb Q.
$$

The important point is that no new algebraic structure is being constructed. The Euclidean-division proof only needs temporary rational quotient coordinates, so they are stored as the ordinary pair type `ℚ × ℚ`.

Because this is an `abbrev`, Lean treats `GoldenRat` transparently as `ℚ × ℚ`, and later code can use the standard projections `.1` and `.2` directly.

## Role in the full proof

By 0208 `GoldenRelPrime`, the development has completed its explicit divisibility, unit, and relative-primality API for the golden integers. Declaration 0209 begins `GoldenEuclidean.lean`, whose purpose is to promote this explicit ring to a Mathlib `EuclideanDomain`.

The module header explains the strategy: represent the rational quotient of two golden integers in the basis `1,φ`, round both coordinates to nearest integers, and study the resulting rounding error.

If the error coordinates satisfy

$$
|u|,|v|\le \frac12,
$$

the golden norm form

$$
u^2+uv-v^2
$$

obeys the uniform bound

$$
\left|u^2+uv-v^2\right|\le \frac5{16}<1.
$$

After clearing denominators, this becomes the strict norm decrease required for Euclidean division.

`GoldenRat` is therefore the type-level starting point of the norm-Euclidean construction: it inserts a temporary rational coordinate space between the integral golden order and the rounded integral quotient.

## Direct dependencies

The declaration has an extremely small direct dependency surface:

- the rational type `ℚ`
- the product type `Prod`
- the `abbrev` mechanism

It directly depends on no project-local theorem or tactic.

Semantically, however, it relies on the interpretation of `GoldenInt` as integral coordinates in the basis `1,φ`; `GoldenRat` is the same coordinate system with coefficients extended from `ℤ` to `ℚ`.

## Construction flow

The construction is a single line:

```lean
abbrev GoldenRat := ℚ × ℚ
```

No new constructor or coercion is introduced. Consequently, later declarations can access the two rational coordinates directly through

```lean
x.1
x.2
```

and reuse the existing API for pairs.

## Lean-specific processing

An `abbrev` is treated as a particularly transparent alias. Theorems stated using `GoldenRat` can be unfolded to ordinary statements about `ℚ × ℚ` without introducing a substantial definitional boundary.

This lets the development reuse `Prod` projections, equality, and simp support without defining a dedicated coordinate structure merely for the Euclidean-division helper layer.

The tradeoff is that the type system does not distinguish an arbitrary rational pair from a pair intended to represent coordinates in the golden basis. In this context the representation is local to the proof infrastructure, so the implementation favors lightness over stronger nominal type safety.

## Redundancy and duplication

`GoldenRat` is only an alias for `ℚ × ℚ`, so it adds no logical expressive power. The source could use `ℚ × ℚ` directly everywhere.

The dedicated name is nevertheless useful:

- it records that the pair is interpreted in the basis `1,φ`;
- it gives downstream declarations such as `goldenRatNorm` a domain-specific type name;
- it clearly separates the rational-coordinate Euclidean layer from the integral-coordinate `GoldenInt` layer.

Thus the redundancy is semantic naming rather than mathematical duplication.

## Optimization candidates

1. **Keep the current `abbrev`**
   - minimal implementation and complete reuse of the `Prod` API.

2. **Introduce a dedicated `structure GoldenRat`**
   - could provide meaningful field names instead of `.1` and `.2`, but would require more constructors, extensionality support, and coercion/API maintenance.

3. **Abstract a parameterized quadratic-coordinate type**
   - useful if the same Euclidean-cell argument is later generalized beyond the golden order.

4. **Model this as a scalar extension of `GoldenInt`**
   - mathematically more structural, perhaps via module or quadratic-algebra machinery, but likely heavier than necessary for the local rounding proof.

For the present nearest-integer rounding argument, the `abbrev` design is highly economical.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself essentially requires only the basic definitions of `ℚ` and `Prod`.

The surrounding `GoldenEuclidean.lean` module immediately uses `round`, `abs_sub_round`, absolute values, inequalities, `nlinarith`, integer/rational casts, and later Euclidean-domain infrastructure. Therefore the minimal imports for the full module are substantially broader than those required by 0209 alone.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. A small representation challenge could compare:

- A: current `abbrev GoldenRat := ℚ × ℚ`
- B: dedicated `structure GoldenRat` with named coordinates
- C: a common parametric coordinate structure shared with `GoldenInt`
- D: an abstract quadratic-algebra or scalar-extension representation

Useful metrics include proof length, simp behavior, projection readability, nominal type safety, generalizability, and transparency of the Euclidean remainder proof.

The contrast between A and B is especially useful for measuring whether a proof-local coordinate type benefits enough from a dedicated structure to justify the added API.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The module header explicitly describes the rational-quotient strategy: round the two golden-basis coordinates, bound the norm on the fundamental cell by `5/16 < 1`, and use the resulting strict contraction to construct `EuclideanDomain GoldenInt`.

The branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact page or section corresponding to this small `abbrev` was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0210 `goldenRatNorm`**:

```lean
/-- The golden norm polynomial on rational coordinates. -/
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

Declaration 0209 prepares the rational coordinate space, and 0210 extends the same quadratic norm form used by `goldenNorm` from integral coordinates to `ℚ`. This becomes the central quantity for measuring contraction on the rounding-error cell.
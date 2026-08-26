# 0216 — `goldenQuotientNumerator`

## Lean type

```lean
/-- Numerator coordinates of `x * conjugate(y)`. -/
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

This is a `def`, not a theorem. For golden integers `x,y`, it names the numerator `x * conjugate(y)` used when constructing the rational quotient `x / y`.

## Mathematical statement and meaning of the declaration

Write

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

In a quadratic extension one rationalizes division by multiplying by the conjugate:

$$
\frac{x}{y}=\frac{x\overline y}{y\overline y}
=\frac{x\overline y}{N(y)}.
$$

The present definition extracts the numerator

$$
x\overline y
$$

as a concrete `GoldenInt`.

By 0163 `goldenConj`,

$$
\overline y=(c+d)-d\varphi.
$$

Expanding `goldenMul`, the following declarations expose

$$
(x\overline y).\mathrm{fst}=a(c+d)-bd,
$$

$$
(x\overline y).\mathrm{snd}=bc-ad.
$$

Thus `goldenQuotientNumerator` is the integer-coordinate layer implementing conjugate rationalization before division by the norm occurs.

## Role in the full proof

`GoldenEuclidean.lean` constructs a nearest-lattice quotient and remainder in order to make `GoldenInt` a `EuclideanDomain`.

Declarations 0209–0214 prepare rational coordinates and prove strict norm contraction on the nearest-integer error cell. Declaration 0215 establishes

$$
y\neq0\Longrightarrow N(y)\neq0,
$$

which certifies that the norm of a nonzero divisor can safely appear in a denominator. With 0216 the development begins implementing the actual quotient

$$
\frac{x\overline y}{N(y)}.
$$

In source order, the present definition is followed by:

- 0217 `goldenQuotientNumerator_fst`
- 0218 `goldenQuotientNumerator_snd`
- `goldenQuotientCoords`
- `goldenQuotient`
- `goldenRemainder`

`goldenQuotientCoords` divides the two integer coordinates of this numerator by `goldenNorm y`, and `goldenQuotient` rounds those rational coordinates back to an integral golden lattice point.

Later, `goldenRemainder_norm_rat_identity` uses the coordinate formulas from 0217 and 0218 to reconstruct the original coordinates from quotient coordinates and prove the key remainder-norm identity. The present definition therefore fixes the algebraic numerator of Euclidean division in one auditable location.

## Direct dependencies

The direct dependencies are:

- 0124 `goldenMul`
- 0163 `goldenConj`

The type itself depends on `GoldenInt`.

Because this is a definition, it has no theorem-level proof dependencies. Conceptually,

$$
(x,y)
\longmapsto
\overline y
\longmapsto
x\overline y.
$$

Declaration 0215 `goldenNorm_ne_zero_of_ne_zero` is not required by the type of this definition, but it is the logical prerequisite for the immediately following step of dividing the coordinates by `N(y)`.

## Construction flow

The construction is one line:

```lean
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

1. Take the conjugate `goldenConj y` of the divisor.
2. Multiply it by the dividend `x` using the raw operation `goldenMul`.
3. Return the resulting golden integer as the quotient numerator.

No denominator handling or coercion to rational numbers occurs here. Those operations are deliberately postponed to `goldenQuotientCoords`.

## Lean-specific processing

The definition intentionally uses the raw API:

```lean
goldenMul x (goldenConj y)
```

Although this is already definitionally compatible with the standard notation

```lean
x * goldenConj y,
```

the raw name makes the following coordinate lemmas easy to prove by directly unfolding `goldenMul` and `goldenConj`.

The result type is still `GoldenInt`, not `GoldenRat`. Therefore the development preserves the integer lattice through the conjugate-multiplication stage and delays the transition to `ℚ` until denominator division is unavoidable.

This layering is useful in Lean: 0217 and 0218 are pure integer polynomial identities closed by `ring`; rational division enters only at the later `goldenQuotientCoords` layer.

## Redundancy and duplication

Mathematically, this definition is a thin wrapper around `x * conjugate(y)`, so it adds no new algebraic information. Downstream code could inline

```lean
goldenMul x (goldenConj y)
```

at every use site.

The dedicated name nevertheless makes the Euclidean construction visibly three-stage:

- algebraic numerator: `goldenQuotientNumerator`
- rational quotient coordinates: `goldenQuotientCoords`
- nearest integral quotient: `goldenQuotient`

That separation is valuable for auditing the implementation.

There is also an API-level duplication question because the standard multiplication notation is already available. Whether this layer should continue to expose `goldenMul` explicitly is a design choice rather than a mathematical necessity.

## Optimization candidates

1. **Keep the named intermediate definition**
   - preserves a clear quotient-construction pipeline and shortens the following coordinate lemmas.

2. **Use standard multiplication notation**
   - define `goldenQuotientNumerator x y := x * goldenConj y` to make the generic ring API more visible.

3. **Bundle conjugation as a `RingEquiv`**
   - move more of the algebraic meaning of conjugation into standard Mathlib structure.

4. **Inline 0217/0218 into quotient coordinates**
   - define `goldenQuotientCoords` directly from explicit formulas, reducing intermediate objects at the cost of reuse and auditability.

5. **Generalize quadratic-order quotient numerators**
   - abstract the construction `x * conj y` for a more general quadratic order.

The current design favors visibility of proof structure over minimal line count, which is a reasonable tradeoff for an auditable Euclidean-domain construction.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present definition itself requires only a very small surface:

- `GoldenInt`
- `goldenMul`
- `goldenConj`

No advanced theorem or tactic is needed by this declaration alone.

The complete `GoldenEuclidean.lean` module, however, uses `round`, `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, and Euclidean-domain infrastructure. Therefore the true minimal import set must be measured at module scope rather than from 0216 in isolation.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current named intermediate `goldenQuotientNumerator`
- B: inline `x * conj y` directly into `goldenQuotientCoords`
- C: use only standard `*` notation
- D: bundle conjugation as a `RingEquiv`
- E: abstract the construction to a generic quadratic order

Useful comparison axes are downstream proof length, ease of coordinate expansion, raw/standard API boundaries, reusability, mathematical readability, and auditability of the Euclidean proof.

The contrast between A and B is especially useful for testing whether a one-line intermediate definition materially improves the clarity of a long formal construction.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this definition immediately after 0215 `goldenNorm_ne_zero_of_ne_zero`, followed by the first- and second-coordinate theorems for the numerator and then by `goldenQuotientCoords`.

The branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0217 `goldenQuotientNumerator_fst`**:

```lean
theorem goldenQuotientNumerator_fst (x y : GoldenInt) :
    (goldenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) - x.snd * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

Now that 0216 fixes `x * conjugate(y)` as an intermediate object, 0217 expands its first coordinate into an explicit integer polynomial. Together with the following second-coordinate formula, this prepares the concrete rational coordinates used by `goldenQuotientCoords`.

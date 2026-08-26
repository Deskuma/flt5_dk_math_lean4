# 0219 — `goldenQuotientCoords`

## Lean type

```lean
/-- Rational coordinates of `x/y` in the golden basis. -/
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

This is a `def`, not a theorem. For two golden integers `x` and `y`, it defines the two rational coordinates of the quotient `x/y` in the basis `1,φ`, with result type `GoldenRat = ℚ × ℚ`.

## Mathematical statement and meaning of the declaration

Write `x=a+bφ` and `y=c+dφ`. Using golden conjugation and the norm, for nonzero `y` one formally rationalizes the quotient as

$$
\frac{x}{y}=\frac{x\overline y}{N(y)}.
$$

Declaration 0216 `goldenQuotientNumerator` packages the numerator

$$
x\overline y
$$

as a `GoldenInt`, while 0217 and 0218 expose its two coordinates as

$$
(x\overline y).\mathrm{fst}=a(c+d)-bd,
$$

$$
(x\overline y).\mathrm{snd}=bc-ad.
$$

Therefore the present definition represents

$$
\operatorname{goldenQuotientCoords}(x,y)
=
\left(
\frac{a(c+d)-bd}{N(y)},
\frac{bc-ad}{N(y)}
\right).
$$

Here

$$
N(y)=c^2+cd-d^2.
$$

An important implementation point is that this `def` itself does not assume `y ≠ 0`. Division in `ℚ` is a total operation in Lean, so the term remains well-typed even when `goldenNorm y = 0`. When the coordinates are used as the ordinary mathematical quotient, 0215 `goldenNorm_ne_zero_of_ne_zero` supplies the required nonzero-denominator fact from `y ≠ 0`.

## Role in the full proof

The purpose of `GoldenEuclidean.lean` is to construct norm-Euclidean division on `GoldenInt`. To do that, the exact quotient of `x` by a nonzero `y` is first represented in rational golden coordinates, and those two coordinates are then rounded to their nearest integers.

The pipeline is:

1. 0215 proves `y ≠ 0 → N(y) ≠ 0`.
2. 0216 constructs the integral numerator `x * conjugate(y)`.
3. 0217 and 0218 expose its two integral coordinates.
4. **0219, the present definition,** divides both coordinates by `N(y)` and moves into `ℚ × ℚ`.
5. 0220 `goldenQuotient` rounds each coordinate to obtain the nearest integral golden quotient.
6. 0221 `goldenRemainder` defines the residual `x - qy`.
7. Later results combine the rounding cell `[-1/2,1/2]^2` with the norm contraction from 0213–0214 to show that the remainder has strictly smaller Euclidean size than the divisor.

Thus 0219 is the **type boundary** between integral coordinate algebra and the geometry of nearest-lattice rounding.

## Direct dependencies

The direct definitions are:

- `GoldenInt`
- 0209 `GoldenRat`
- 0216 `goldenQuotientNumerator`
- 0164 `goldenNorm`
- coercion from integers to rationals
- division in `ℚ`

Because this is a definition, there is no proof script, and 0215 `goldenNorm_ne_zero_of_ne_zero` is not a direct dependency of the term.

Mathematically, however, interpreting the result as `x/y` requires

$$
y\neq0\Longrightarrow N(y)\neq0,
$$

which is exactly what 0215 provides.

Conceptually,

$$
x\overline y
\xrightarrow{\text{0217,0218}}
(A,B)\in\mathbb Z^2
\xrightarrow{/N(y)}
\left(\frac{A}{N(y)},\frac{B}{N(y)}\right)\in\mathbb Q^2.
$$

## Construction flow

The definition simply builds the two rational coordinates as a pair:

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

For the first coordinate,

```lean
(goldenQuotientNumerator x y).fst : ℤ
```

is explicitly cast to `ℚ`, while `goldenNorm y : ℤ` is coerced to `ℚ` by the expected type of division.

The second coordinate is constructed in exactly the same way.

At this stage no rounding is performed: the exact rational coordinates are retained. Discretization back to the golden-integer lattice is deliberately postponed to the next declaration, `goldenQuotient`.

## Lean-specific processing

### 1. `GoldenRat` is an `abbrev`

Declaration 0209 defines

```lean
abbrev GoldenRat := ℚ × ℚ
```

so the pair literal used here is definitionally just `Prod ℚ ℚ`. Downstream code can use `.1` and `.2` directly without additional projection lemmas.

### 2. Explicit numerator coercion

The expression

```lean
((goldenQuotientNumerator x y).fst : ℚ)
```

explicitly invokes the coercion `ℤ → ℚ`. The denominator `goldenNorm y` is coerced to `ℚ` from the expected type of `/`.

### 3. Zero division is not prohibited at the type level

Division in `ℚ` is total, so Lean does not require a proof of `goldenNorm y ≠ 0` when defining this function. This keeps `goldenQuotientCoords x 0` well-typed and allows later declarations such as `goldenQuotient_zero` to be stated for a total function.

When later proofs use ordinary rational identities or `field_simp`, the denominator nonzero condition becomes relevant, and 0215 supplies it.

## Redundancy and duplication

Declarations 0217 and 0218 expose explicit formulas for the numerator coordinates, yet this definition refers again to `.fst` and `.snd` of the packaged numerator. One alternative would therefore inline the formulas from 0217 and 0218 directly into this definition.

The present design is nevertheless structurally cleaner because it separates three stages:

- integral numerator algebra;
- rationalization by the norm;
- nearest-integer rounding.

The two coordinates also share the same denominator. A heavier design could represent them with a dedicated structure carrying a common denominator, but `ℚ × ℚ` is simpler and gives direct access to Mathlib's rational arithmetic.

## Optimization candidates

1. **Move toward the standard multiplication / conjugation API**
   - reduce exposure of raw `goldenMul` through the quotient pipeline.

2. **Provide a nonzero-denominator wrapper**
   - a helper taking `y ≠ 0` could package the denominator proof for later rational identities.
   - the current total-function design remains advantageous for Euclidean operations.

3. **Compare an inlined coordinate definition**
   - place the explicit formulas from 0217 and 0218 directly in the pair and compare downstream proof burden against the current numerator-object design.

4. **Generalize to a quadratic order**
   - conjugation, norm, and rationalized quotient coordinates are generic features of quadratic extensions; a relation `θ²=pθ+q` could be abstracted and the golden case specialized.

5. **Replace `GoldenRat` by a dedicated structure**
   - semantic field names such as `oneCoord` and `phiCoord` could improve readability, at the cost of a heavier API.

The local definition is already minimal; the meaningful optimization space is primarily architectural.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The present definition itself mainly needs:

- `ℚ`
- `Prod`
- integer-to-rational coercion
- field division
- project-local `GoldenInt`, `GoldenRat`, `goldenQuotientNumerator`, and `goldenNorm`

No tactic is used by this `def`.

The complete `GoldenEuclidean.lean` module also uses `round`, `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, and Euclidean-domain infrastructure, so its true minimal import set is much broader than the surface needed by 0219 alone.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current definition through the packaged numerator object
- B: directly inline the explicit coordinate formulas from 0217 and 0218
- C: replace `GoldenRat` with a dedicated structure
- D: use a quotient API that explicitly takes `y ≠ 0`
- E: specialize a generic quadratic-order quotient-coordinate construction

Useful metrics include:

- definitional transparency
- convenience for downstream `field_simp`
- handling of zero denominators
- proof-term size
- auditability of the API boundary
- generalizability

The contrast between A and D is especially instructive: A keeps Euclidean operations total, whereas D makes the ordinary mathematical precondition `y ≠ 0` explicit in the API.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this definition immediately after declarations 0217 and 0218, and immediately before

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0220 `goldenQuotient`**:

```lean
/-- The nearest integral golden quotient. -/
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

Now that 0219 constructs the exact rational quotient coordinates, 0220 rounds each coordinate independently to the nearest integer and returns an actual `GoldenInt` quotient. This is the step from the continuous rational quotient back to the discrete golden lattice, after which `goldenRemainder` and the norm-contraction argument follow.

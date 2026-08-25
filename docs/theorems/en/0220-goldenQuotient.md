# 0220 — `goldenQuotient`

## Lean type

```lean
/-- The nearest integral golden quotient. -/
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

This is a `def`, not a theorem. It takes the exact rational quotient coordinates produced by 0219 `goldenQuotientCoords`, rounds each coordinate to its nearest integer, and returns the resulting `GoldenInt`.

## Mathematical statement and meaning of the declaration

Write `x=a+bφ` and `y=c+dφ`. Declaration 0219 constructs rational coordinates

$$
(A,B)=\operatorname{goldenQuotientCoords}(x,y)
$$

which, for nonzero `y`, are mathematically interpreted through

$$
\frac{x}{y}=A+B\varphi.
$$

The present definition chooses

$$
q=\operatorname{round}(A)+\operatorname{round}(B)\varphi
$$

as the quotient in the golden order.

Thus `goldenQuotient` is not the exact quotient in a field. It is the discrete lattice point in the coordinate lattice $\mathbb Z^2$ obtained by rounding the exact rational quotient coordinatewise.

Mathlib's rounding theorem gives

$$
|A-\operatorname{round}(A)|\le\frac12,
$$

$$
|B-\operatorname{round}(B)|\le\frac12,
$$

so the quotient error lies in the square fundamental cell $[-1/2,1/2]^2$.

## Role in the full proof

The purpose of `GoldenEuclidean.lean` is to construct norm-Euclidean division on `GoldenInt`. The pipeline is:

1. `goldenQuotientCoords` computes the exact rational quotient in the basis `1,φ`.
2. **The present `goldenQuotient` rounds those two coordinates to integers.**
3. 0221 `goldenRemainder` defines

$$
r=x-qy.
$$

4. The coordinate rounding error lies in $[-1/2,1/2]^2$.
5. Declarations 0213–0214 provide

$$
|u^2+uv-v^2|<1
$$

on that cell.
6. `golden_remainder_size_lt` derives strict Euclidean decrease.
7. Finally, `goldenEuclideanDomain : EuclideanDomain GoldenInt` installs this definition directly as its quotient operation.

The source later contains

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  ...
```

so this declaration is not merely a helper: it is the concrete quotient algorithm of the final Euclidean-domain instance.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0219 `goldenQuotientCoords`
- Mathlib's `round : ℚ → ℤ`
- the `GoldenInt` structure constructor

Because this is a definition, there is no proof script.

Mathematical background is supplied by:

- 0211 `exists_int_near_rat`
- 0212 `exists_goldenRat_near_int`
- 0213 `goldenRat_norm_abs_le_five_sixteen`
- 0214 `goldenRat_norm_abs_lt_one`

Conceptually,

$$
\operatorname{goldenQuotientCoords}(x,y)=(A,B)\in\mathbb Q^2
\longrightarrow
(\operatorname{round}A,\operatorname{round}B)\in\mathbb Z^2
\longrightarrow
q\in\mathbb Z[\varphi].
$$

## Construction flow

The definition rounds the two coordinates independently:

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

1. Compute `goldenQuotientCoords x y : GoldenRat`.
2. Project the rational coordinate in the basis direction `1` using `.1`.
3. Apply `round` to obtain an integer.
4. Repeat the same process on the `φ` coordinate using `.2`.
5. Reassemble the two integers as a `GoldenInt`.

No global search for an optimal lattice point is performed. The later fundamental-cell estimate is strong enough that simple coordinatewise rounding already guarantees Euclidean contraction.

## Lean-specific processing

### 1. `round` returns an integer

Each coordinate of `goldenQuotientCoords x y` has type `ℚ`, while `round` returns `ℤ`. The two values can therefore be inserted directly into the `fst` and `snd` fields of `GoldenInt`.

### 2. The quotient is a total function

As in 0219, this definition does not assume `y ≠ 0`. Hence `goldenQuotient x 0` is still a well-typed term.

This is important because the quotient field of a Euclidean-domain structure is a total operation. The following theorem separately establishes the desired zero-divisor behavior:

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ...
```

### 3. Computability is separated from the specification

The present declaration is written as an ordinary definition, while the eventual Euclidean-domain instance is declared `noncomputable`. This keeps the mathematical quotient algorithm and its formal specification separate from the computability status of the final structure.

### 4. The rounding errors are used directly downstream

In `golden_remainder_size_lt`, the source introduces

```lean
let A := (goldenQuotientCoords x y).1
let B := (goldenQuotientCoords x y).2
have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
```

so the exact two `round` operations chosen here are precisely the objects whose error is later fed into the norm-contraction theorem.

## Redundancy and duplication

Declaration 0212 already proves that every `GoldenRat` has nearby integral coordinates, but the present definition does not reuse that existential theorem; it chooses the canonical witnesses `round A` and `round B` directly.

This is mild logical duplication, but it is structurally justified. A Euclidean-domain quotient must be a concrete function, while an existential statement only proves that some suitable lattice point exists. Thus 0212 serves as the geometric existence layer and 0220 serves as the canonical implementation layer.

The expressions `(goldenQuotientCoords x y).1` and `.2` also recur frequently downstream. Local names such as `A` and `B`, or semantic projection helpers, may improve readability in larger proofs.

## Optimization candidates

1. **Introduce a dedicated rounding helper**

```lean
def goldenRound (x : GoldenRat) : GoldenInt :=
  ⟨round x.1, round x.2⟩
```

and define `goldenQuotient x y := goldenRound (goldenQuotientCoords x y)`.

2. **Bundle the quotient with rounding certificates**

A structure could return both the rounded quotient and the two `≤ 1/2` error proofs. This may shorten downstream proofs, at the cost of making the quotient API heavier.

3. **Generalize lattice rounding to quadratic orders**

The step “rational quotient coordinates → integral lattice point” is generic for many quadratic orders. The golden case could specialize a broader framework, leaving only the norm-cell estimate order-specific.

4. **Compare coordinatewise rounding with a true norm-nearest lattice point**

The present method rounds each coordinate independently. A search for the lattice point minimizing the golden norm of the remainder might produce a different quotient, but the existing $5/16<1$ bound already makes coordinatewise rounding sufficient for Euclideanity.

5. **Compare an explicit zero-denominator branch**

One could define `if y = 0 then 0 else ...`. The current design is simpler because rational division is total and `goldenQuotient_zero` separately proves the required behavior.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The declaration itself directly needs mainly:

- `ℚ` and `ℤ`
- `round`
- product projections
- project-local `GoldenInt`, `GoldenRat`, and `goldenQuotientCoords`

No tactic is used by this `def`.

The complete `GoldenEuclidean.lean` module additionally uses `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, `measure`, and the `EuclideanDomain` hierarchy, so the true minimal module import set is substantially larger.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current coordinatewise `round`
- B: a separate `goldenRound : GoldenRat → GoldenInt` helper
- C: quotient bundled with its rounding-error certificates
- D: search for a norm-nearest lattice point
- E: specialize a generic quadratic-order rounding framework

Useful comparison axes include:

- size of the Euclidean-decrease proof
- transparency of the quotient definition
- downstream simp / rewrite burden
- computability
- reuse of proof certificates
- generalizability

The contrast between A and C is especially useful for measuring the trade-off between a lightweight quotient function and one that carries proof data alongside the selected quotient.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source confirms the sequence

```lean
def goldenQuotientCoords ...

def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩

def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0221 `goldenRemainder`**:

```lean
/-- The residual after nearest-lattice normalization. -/
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

Now that 0220 has selected the discrete quotient `q`, 0221 defines

$$
r=x-qy
$$

inside the golden order. From there the development proves the quotient/remainder identity and the norm contraction needed for the Euclidean-domain specification.
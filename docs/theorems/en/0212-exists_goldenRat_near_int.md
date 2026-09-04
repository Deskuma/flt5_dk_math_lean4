# 0212 — `exists_goldenRat_near_int`

## Lean type

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

This is a `theorem` stating that for rational golden-basis coordinates `x = (x.1, x.2)`, one can choose integer coordinates `m,n` simultaneously so that each coordinate is within distance `1/2` of its chosen integer.

## Mathematical statement

Declaration 0209 defines

```lean
abbrev GoldenRat := ℚ × ℚ
```

so `x : GoldenRat` represents rational coordinates

$$
x=(u,v),\qquad u,v\in\mathbb Q
$$

in the basis `1,φ`.

The theorem states

$$
\forall (u,v)\in\mathbb Q^2,\quad
\exists m,n\in\mathbb Z,
\quad |u-m|\le\frac12,
\quad |v-n|\le\frac12.
$$

Thus nearest-integer rounding places the error coordinates

$$
U=u-m,\qquad V=v-n
$$

inside the fundamental cell

$$
|U|\le\frac12,
\qquad
|V|\le\frac12.
$$

## Role in the full proof

The purpose of `GoldenEuclidean.lean` is to construct `GoldenInt` as a norm-Euclidean domain. To do that, a rational quotient must be rounded to the golden integer lattice so that the resulting remainder has strictly smaller absolute norm than the divisor.

Declarations 0209 `GoldenRat` and 0210 `goldenRatNorm` prepare the rational quotient space and the quadratic norm form

$$
Q(u,v)=u^2+uv-v^2.
$$

Declaration 0211 `exists_int_near_rat` gives nearest-integer rounding for one rational coordinate. The present theorem is the two-coordinate version needed to place the quotient error directly into a square fundamental cell.

The next theorem, 0213 `goldenRat_norm_abs_le_five_sixteen`, proves on this cell that

$$
|u^2+uv-v^2|\le\frac{5}{16}.
$$

Since `5/16 < 1`, this becomes a strict contraction estimate and later feeds into `golden_remainder_size_lt`, yielding

$$
|N(r)|<|N(y)|.
$$

Thus 0212 is the nearest-lattice normalization step that moves an arbitrary rational quotient into the region where the golden norm is uniformly contracting.

## Direct dependencies

The direct dependencies are:

- 0209 `GoldenRat := ℚ × ℚ`
- Mathlib `round`
- Mathlib `abs_sub_round`
- the rational type `ℚ`
- the integer type `ℤ`
- absolute value and order structure

The proof does not directly invoke 0211 `exists_int_near_rat`. Instead it applies `round` and `abs_sub_round` independently to both coordinates.

Conceptually,

$$
(u,v)
\longmapsto
(\operatorname{round}(u),\operatorname{round}(v))
\longmapsto
(U,V)\in[-1/2,1/2]^2.
$$

## Proof flow

The proof constructs both witnesses and both certificates at once:

```lean
exact ⟨round x.1, round x.2,
  abs_sub_round x.1, abs_sub_round x.2⟩
```

1. Choose `round x.1` as the integer witness `m`.
2. Choose `round x.2` as the integer witness `n`.
3. Supply `abs_sub_round x.1` for the first coordinate bound.
4. Supply `abs_sub_round x.2` for the second coordinate bound.
5. The two inequalities fill the conjunction and close the existential statement.

No additional arithmetic, case split, `linarith`, or `ring` is needed.

## Lean-specific processing

The conclusion has the nested shape

```lean
∃ m n : ℤ,
  |x.1 - m| ≤ (1 : ℚ) / 2 ∧
  |x.2 - n| ≤ (1 : ℚ) / 2
```

so the apparently flat constructor expression

```lean
⟨round x.1, round x.2,
  abs_sub_round x.1, abs_sub_round x.2⟩
```

is elaborated from the expected type as:

- first existential witness,
- second existential witness,
- left proof of the conjunction,
- right proof of the conjunction.

`round x.1` and `round x.2` have type `ℤ`, while in the expressions `x.1 - m` and `x.2 - n` the integer witnesses are coerced automatically to `ℚ`. `abs_sub_round` uses the same coercion convention, so the proof terms match exactly without `norm_cast` or `simpa`.

## Redundancy and duplication

Declaration 0211 already exposes the one-variable nearest-integer theorem, but the present theorem does not reuse it. Instead, it directly applies the same Mathlib primitives twice.

There is therefore mild proof-architecture duplication:

- 0211: one-coordinate wrapper;
- 0212: direct two-coordinate use of the underlying primitive.

One could instead prove 0212 by calling 0211 on `x.1` and `x.2`, extracting the witnesses with `rcases`, and combining them. That would make the dependency graph more explicitly layered, but the current proof is shorter and has shallower dependency depth.

There is also some repeated tuple syntax because `GoldenRat` is only an `abbrev` for `ℚ × ℚ`. If future proofs need semantically named coordinates, a dedicated structure could be considered, though the lightweight pair representation is currently advantageous.

## Optimization candidates

1. **Reuse 0211 explicitly**
   - makes the one-dimensional to two-dimensional dependency graph clearer.

2. **Keep the current direct witness construction**
   - shortest proof and direct use of Mathlib's rounding primitives.

3. **Introduce a dedicated rounding function**
   - for example `goldenRatRound : GoldenRat → GoldenInt`;
   - this could align the theorem more closely with the later `goldenQuotient` construction.

4. **Introduce a fundamental-cell predicate**
   - package `|u| ≤ 1/2 ∧ |v| ≤ 1/2` into a named predicate;
   - this could clarify the API from 0212 to 0213 to strict contraction.

5. **Compare with a general lattice-rounding abstraction**
   - theoretically possible, but likely more abstraction than this specialized two-dimensional proof needs.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself directly needs mainly rational and integer types, nearest-integer rounding, absolute value, and order.

The exact minimal Mathlib import names are not verified because this museum pass does not run a Lean build. Therefore any reduction from `import Mathlib` is recorded only as an optimization candidate rather than a confirmed minimal import set.

At module scale, `GoldenEuclidean.lean` later uses `nlinarith`, `linarith`, `ring`, `field_simp`, casts, and Euclidean-domain infrastructure, so the full module necessarily has a broader import surface than 0212 alone.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current direct coordinatewise use of `round` / `abs_sub_round`
- B: reuse 0211 `exists_int_near_rat` twice
- C: define a dedicated `goldenRatRound` function and prove its error bound
- D: construct the bounds manually from floor / ceil

Useful comparison axes are proof size, dependency clarity, coercion burden, dependence on Mathlib primitives, connection to the downstream Euclidean construction, and API reuse.

The A-versus-B comparison is particularly good for measuring the value of explicitly reusing a thin wrapper theorem in a theorem-museum-style dependency graph.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this theorem appears immediately after 0211 and is followed by 0213 `goldenRat_norm_abs_le_five_sixteen`:

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0213 `goldenRat_norm_abs_le_five_sixteen`**:

```lean
/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| ≤ (5 : ℚ) / 16 := by
  ...
```

Declaration 0212 puts the rounding error inside the square `[-1/2,1/2]^2`; 0213 proves that the golden quadratic norm form is uniformly bounded by `5/16` on that whole cell. This is the quantitative core of the Euclidean contraction argument.
# 0211 — `exists_int_near_rat`

## Lean type

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩
```

This is a `theorem` stating that every rational number `x` lies within distance `1/2` of some integer `n`.

## Mathematical statement

The claim is the basic nearest-integer rounding fact

$$
\forall x\in\mathbb Q,\quad \exists n\in\mathbb Z,\quad |x-n|\le\frac12.
$$

The proof simply chooses Mathlib's `round x` as the integer witness. The theorem `abs_sub_round x` then provides

$$
|x-\operatorname{round}(x)|\le\frac12,
$$

which closes the existential statement immediately.

This theorem is not specific to golden integers. It gives a local name, inside `GoldenEuclidean.lean`, to a general rational rounding fact and connects it to the next simultaneous two-coordinate rounding step.

## Role in the full proof

Declarations 0209 `GoldenRat := ℚ × ℚ` and 0210 `goldenRatNorm` prepare rational golden-basis quotients and the quadratic norm polynomial used to measure their error. The present theorem supplies the one-dimensional rounding certificate needed to move each quotient coordinate to the nearest integer lattice point.

The next declaration, 0212 `exists_goldenRat_near_int`, chooses integers for both `x.1` and `x.2` and obtains

$$
|x_1-m|\le\frac12,
\qquad
|x_2-n|\le\frac12.
$$

Thus the rounding error `(u,v)` enters the fundamental cell

$$
|u|\le\frac12,
\qquad
|v|\le\frac12.
$$

The strategy documented in `GoldenEuclidean.lean` is then to prove on this cell that

$$
|u^2+uv-v^2|\le\frac{5}{16}<1,
$$

which ultimately makes the absolute norm of the Euclidean remainder strictly smaller than that of the divisor.

Thus 0211 is a tiny theorem, but it is the first operational step in placing the quotient error inside the bounded cell where Euclidean contraction can be proved.

## Direct dependencies

The direct dependencies are:

- the rational type `ℚ`
- the integer type `ℤ`
- absolute value `|x|`
- Mathlib's `round x : ℤ`
- Mathlib's `abs_sub_round x`

Neither `GoldenRat` nor `goldenRatNorm` appears directly in the theorem type. They are upstream in source order because of the Euclidean-construction narrative, while the actual Lean proof closes entirely through the general ordered-field rounding API.

Conceptually,

$$
x\in\mathbb Q
\longmapsto
\operatorname{round}(x)\in\mathbb Z
\longmapsto
|x-\operatorname{round}(x)|\le\frac12.
$$

## Proof flow

The proof is a single line:

```lean
exact ⟨round x, abs_sub_round x⟩
```

1. Choose `round x` as the existential witness `n : ℤ`.
2. The remaining goal is `|x - round x| ≤ 1/2`.
3. `abs_sub_round x` has exactly that content, so it is supplied directly as the certificate.

No new inequality reasoning or case split is performed. The theorem is essentially a local existential wrapper around Mathlib's nearest-integer estimate.

## Lean-specific processing

`⟨round x, abs_sub_round x⟩` is constructor notation for the existential target

```lean
∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2
```

The expected type tells Lean that `round x` is the witness for `n`, and the second component must prove the target after substituting that witness.

`round x` has type `ℤ`. In the expression `x - n`, the integer `n` is coerced to `ℚ`, so subtraction and absolute value are evaluated in the rationals. The annotation `(1 : ℚ) / 2` fixes the right-hand side as rational one-half.

This coercion is implicit in the statement, but `abs_sub_round` uses the same convention. Consequently the proof matches exactly without requiring `simpa`, cast rewriting, or normalization lemmas.

## Redundancy and duplication

Logically, this theorem is little more than existential packaging of Mathlib's `abs_sub_round`, so it adds almost no new mathematical information.

The next declaration 0212 can also construct its two witnesses directly from `round x.1`, `round x.2`, and two applications of `abs_sub_round`, without calling 0211. In that implementation sense, the wrapper is redundant.

There are still useful reasons to retain it:

- it names the one-variable rounding primitive of the Euclidean construction;
- downstream code can be insulated from the specific Mathlib lemma name;
- a future change in rounding policy could preserve the local API;
- the dependency progression from one coordinate to two coordinates becomes explicit for auditing and exposition.

It is therefore best viewed as API/expository redundancy rather than mathematical redundancy requiring removal.

## Optimization candidates

1. **Make 0212 explicitly reuse 0211**
   - obtain the two coordinate witnesses from `exists_int_near_rat x.1` and `exists_int_near_rat x.2`, making the dependency graph more layered and textbook-like.

2. **Remove 0211 and use Mathlib directly**
   - reduces code volume but hides the local rounding primitive.

3. **Separate a strict or tie-breaking variant**
   - the current bound is `≤ 1/2`, so equality is possible for half-integers. This is sufficient unless a later argument needs a strict coordinate bound or a specified tie-breaking rule.

4. **Consider generalization beyond `ℚ`**
   - theoretically possible for types equipped with suitable rounding structure, but likely unnecessary here because the Euclidean quotient is specifically rational.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem by itself needs essentially the rational/integer rounding and absolute-value order API providing `round` and `abs_sub_round`.

The precise minimal Mathlib import containing those declarations was not verified in this museum pass because no Lean build is run. Therefore no exact minimal module name is asserted here; import reduction remains an explicit optimization candidate.

The complete `GoldenEuclidean.lean` module later uses rational/integer casts, inequalities, `ring`, and Euclidean-domain construction, so its module-level minimal imports will be broader than the needs of 0211 in isolation.

## Comparator challenge suitability

Yes. Although small, the theorem offers a clean API-design comparison.

Possible implementations are:

- A: current `⟨round x, abs_sub_round x⟩`
- B: prove the `1/2` estimate manually using floor/ceiling cases
- C: delete 0211 and use `abs_sub_round` twice directly in 0212
- D: make 0212 invoke 0211 twice as a layered API

Useful metrics include proof length, Mathlib dependency surface, clarity of the dependency graph, coercion burden, interchangeability of the rounding policy, and readability of downstream Euclidean proofs.

The C-versus-D comparison is especially useful for testing whether a thin wrapper theorem is worthwhile for theorem-museum auditability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, 0210 `goldenRatNorm` is immediately followed by this theorem, and 0212 `exists_goldenRat_near_int` follows next:

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩

/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0212 `exists_goldenRat_near_int`**:

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

Declaration 0211 guarantees that one rational coordinate can be rounded to within `1/2` of an integer. Declaration 0212 performs the same construction simultaneously for both golden-basis coordinates, directly constructing the fundamental cell needed for Euclidean contraction.
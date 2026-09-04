# 0109 — `signed_endpoint_square_discriminant`

## Lean type

```lean
/-- The signed endpoint coordinates retain a square discriminant. -/
theorem signed_endpoint_square_discriminant (x y : ℤ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * (-(x * y)) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 := by
  ring
```

## Mathematical statement

For arbitrary integers $x,y$, define the square-sum coordinate and the sign-reversed cross coordinate by

$$
M=x^2+y^2,\qquad N=-xy.
$$

Then the square discriminant satisfies

$$
M^2-4N^2=(x^2-y^2)^2.
$$

After substitution this is

$$
(x^2+y^2)^2-4(-xy)^2=(x^2-y^2)^2.
$$

Since $(-xy)^2=(xy)^2$, this is exactly the standard identity

$$
(x^2+y^2)^2-4x^2y^2=(x^2-y^2)^2.
$$

## Role in the whole proof

The preceding article, 0108 `sumGN5_eq_goldenNorm_signed`, moves the sum-type residual `SumGN5` into the golden norm using the negative cross coordinate

$$
N=-uv.
$$

The present theorem shows that the same signed endpoint coordinates preserve not only the golden norm but also the square discriminant.

In the later signed exceptional packet construction it is used directly in the sum branch as

```lean
have hSquare : M ^ 2 - 4 * N ^ 2 = delta ^ 2 := by
  dsimp [M, N, delta]
  exact signed_endpoint_square_discriminant (u : ℤ) (v : ℤ)
```

Thus 0108 and 0109 form a pair: they are the two entrance bridges that place the sum-type source into the existing square/golden invariant API.

Immediately after this theorem, `SignedSquareGoldenSource` records the provenance of $M,N,\delta$ for both the difference orientation and the sum orientation. Article 0109 is the basic identity that closes the square-discriminant side of the sum orientation.

## Direct dependencies

This theorem is mathematically self-contained and directly references no repository-specific definition or lemma.

On the Lean side it needs only:

- the integer type `ℤ`;
- addition, subtraction, multiplication, and powers;
- the `ring` tactic for polynomial normalization over a commutative ring.

Its semantic neighbors are the preceding `sumGN5_eq_goldenNorm_signed` and the following `SignedSquareGoldenSource` / signed exceptional packet construction, but none of those names occurs in the theorem type itself.

## Proof flow

The proof is one line:

```lean
by
  ring
```

`ring` expands both sides into canonical commutative-ring normal form and verifies that they are the same polynomial.

Conceptually, the left side

$$
(x^2+y^2)^2-4(-xy)^2
$$

expands to

$$
x^4+2x^2y^2+y^4-4x^2y^2,
$$

which reduces to

$$
x^4-2x^2y^2+y^4.
$$

The right side $(x^2-y^2)^2$ expands to the same normal form.

## Lean-specific processing

Because the variables are integers from the start, there is no truncated `Nat.sub`, no order side condition, and no `Nat.cast_sub` processing. This sharply contrasts with article 0108.

The minus sign sits outside the product, but `ring` automatically normalizes the fact that

$$
(-xy)^2=x^2y^2.
$$

Therefore no manual `simp [pow_two]` or auxiliary sign lemma is necessary.

From the Lean perspective this theorem is a clean example of how moving to signed coordinates eliminates natural-number case splits and reduces the goal to a pure integer polynomial identity.

## Redundancy and duplication

The mathematical content strongly overlaps with article 0103 `squareGolden_square_discriminant` and its lower-level dependency `endpoint_square_discriminant`.

The only conceptual difference is the sign of the cross coordinate:

- difference orientation: $N=xy$;
- sum orientation: $N=-xy$.

But the discriminant contains only $N^2$, so the sign disappears. Mathematically, there is little need to re-prove a separate signed theorem.

As an API, however, the signed theorem matches the downstream source shape exactly, avoiding an extra sign-elimination rewrite at every use site. It is therefore better viewed as wrapper-level duplication for downstream readability rather than accidental logical duplication.

## Optimization candidates

1. Reuse the existing `endpoint_square_discriminant` and compare whether the signed version can be obtained by a single `simpa`.
2. Introduce a general invariance lemma for the discriminant under sign reversal of the second coordinate,

   $$
   M^2-4(-N)^2=M^2-4N^2,
   $$

   and derive both orientations from one base theorem.
3. Provide square-discriminant theorems directly for the constructors of `SignedSquareGoldenSource`, hiding the endpoint-level helper theorem behind the source API.
4. The current one-line `ring` proof is already extremely short and robust, so optimization is not about reducing line count. The real opportunity is conceptual deduplication and API organization.

## Required Mathlib imports and import optimization

The generated standalone artifact uses

```lean
import Mathlib
```

for the whole concatenated development.

For this theorem alone, integer ring operations and the `ring` tactic are enough, so importing all of Mathlib is clearly broader than necessary. A plausible optimization is to reduce the tactic dependency to `Mathlib.Tactic.Ring` together with the integer/algebra foundations that it requires.

However, the individual `SignedSquareGoldenExceptional.lean` source file could not be fetched directly from this branch; only its generated section inside the standalone artifact was available. Therefore the exact minimal import set for the real module is not asserted without a Lean build and is recorded here only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem is especially suitable because its proof is tiny and the design differences are easy to compare.

Three clear approaches are:

1. Current approach: one `ring` call.
2. Reuse approach: derive the signed theorem from the existing `endpoint_square_discriminant` via `simpa`.
3. General-invariance approach: first prove discriminant invariance under $N\mapsto -N$, then compose it with the existing theorem.

The comparison should not use proof length as the only metric. Better criteria are how much duplication is removed, whether the signed-orientation meaning remains visible in the source, and how naturally the result is consumed by the later packet construction.

## Correspondence with existing materials

The formal source is the `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section generated into `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The standalone manifest places this module immediately after `SquareGoldenNormalForm.lean` and before `GoldenOrder.lean`.

The exact page or section correspondence in the existing Japanese and English PDFs could not be established through the GitHub connector in this run, so no page number is guessed. When narrative PDF text and Lean source differ, this museum treats the Lean source as the formal authority.

## Next declaration to read

The next unexplained declaration in dependency order is not a theorem but the following inductive definition:

```lean
inductive SignedSquareGoldenSource
    (u v w : ℕ) (M N delta : ℤ) : Prop
  | difference :
      M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = (w : ℤ) * (v : ℤ) →
      delta = (w : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
  | sum :
      M = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = -((u : ℤ) * (v : ℤ)) →
      delta = (u : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
```

Article 0108 supplied the golden-norm bridge for the sum residual, and article 0109 supplies the square-discriminant bridge for the same signed endpoint coordinates. With those two pieces in place, the proof is ready to package the difference and sum orientations into a single provenance type. The next article should therefore cover `SignedSquareGoldenSource`.
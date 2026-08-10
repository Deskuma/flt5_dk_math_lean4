# 0097 — `four_mul_goldenNorm_eq_discriminant_five`

## Lean Type

```lean
theorem four_mul_goldenNorm_eq_discriminant_five (m n : ℤ) :
    4 * GoldenNorm m n = (2 * m + n) ^ 2 - 5 * n ^ 2 := by
  unfold GoldenNorm
  ring
```

## Mathematical Statement

For `GoldenNorm m n = m^2 + mn - n^2`,

$$
4\,\mathrm{GoldenNorm}(m,n)=(2m+n)^2-5n^2
$$

holds. Expanding the right-hand side gives $4m^2+4mn-4n^2$, which matches the left-hand side. This identity diagonalizes the quadratic form into a discriminant-$5$ form.

## Role in the Overall Proof

In 0096, `GN5` was identified with `GoldenNorm` in endpoint-square coordinates. This theorem sends that `GoldenNorm` further into the form

$$
X^2-5Y^2,
$$

making the discriminant $5$ intrinsic to the golden-ratio quadratic form. The source module comment likewise describes this diagonalization as the algebraic bridge from the elementary cyclotomic factorization toward the later `GoldenOrder` coordinate order.

## Direct Dependencies

The only direct project-local dependency is `GoldenNorm : ℤ → ℤ → ℤ`. The theorem 0096 is not invoked in the proof body. On the Mathlib side, the proof uses basic integer ring operations, powers, and the `ring` tactic.

## Proof Flow

```lean
unfold GoldenNorm
ring
```

First `GoldenNorm` is unfolded, changing the goal into

$$
4(m^2+mn-n^2)=(2m+n)^2-5n^2.
$$

This is a polynomial identity over the integers, so `ring` normalizes both sides and closes the goal.

## Lean-Specific Processing

The theorem lives entirely in `ℤ`, so unlike 0096 it needs no `push_cast`. `unfold GoldenNorm` opens the named abstraction, and `ring` handles the commutative-ring identity with subtraction.

## Redundancy and Duplication

The two-line proof contains essentially no internal redundancy. There is, however, a general identity for a binary quadratic form $ax^2+bxy+cy^2$:

$$
4a(ax^2+bxy+cy^2)=(2ax+by)^2-(b^2-4ac)y^2.
$$

The present theorem is the specialization $a=1,b=1,c=-1$, whose discriminant is $5$. If the same calculation appears for multiple quadratic forms, this is a natural abstraction candidate.

## Optimization Candidates

1. Keep the current proof: it is shortest and has minimal dependencies.
2. Introduce a general binary-quadratic discriminant identity and specialize it here.
3. If `2*m+n` is repeatedly used downstream, introduce a named discriminant-coordinate helper.
4. Connect this identity to the later `GoldenOrder` norm, while preserving the present theorem as a lightweight elementary-algebra layer.

## Required Mathlib Imports and Import Optimization

The generated standalone artifact uses `import Mathlib`. For this theorem alone, the essential requirements are the commutative ring structure on `ℤ`, powers, and the `ring` tactic, so the umbrella import is likely larger than necessary. However, the same `SquareGoldenBridge.lean` section also contains theorems using `push_cast` and `norm_num`, so the minimal import set for the whole module cannot be stated safely without a Lean build check.

## Comparator Challenge Suitability

This theorem is suitable for a Comparator challenge. Natural competitors are the current `unfold; ring` proof, a `calc` proof exposing the square expansion, and a proof via a general discriminant identity. Useful comparison axes are line count, generality, mathematical transparency, dependency count, and downstream reusability.

## Relation to Existing Materials

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its generated source marker places this theorem in the `DkMath/FLT/Five/SquareGoldenBridge.lean` section.

The GitHub code search for the existing Japanese and English PDFs returned an upstream 502 error in this run, so no concrete PDF page or section number could be verified. No speculative PDF location is supplied.

## Next Theorem to Read

The next declaration in the standalone source is

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

0097 exposes the discriminant $5$ on the golden-norm side; the next article will examine the independent square discriminant retained by the same endpoint-square coordinate world.
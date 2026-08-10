# 0098 — `endpoint_square_discriminant`

## Lean type

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

## Mathematical statement

For arbitrary integers $z,y$,

$$
(z^2+y^2)^2-4(zy)^2=(z^2-y^2)^2
$$

holds.

The left-hand side is the discriminant-like quantity

$$
M^2-4N^2
$$

for the endpoint-square coordinates

$$
M=z^2+y^2,\qquad N=zy,
$$

and the theorem states that this quantity is the perfect square

$$
(z^2-y^2)^2.
$$

It is also the specialization of the elementary identity

$$
(a+b)^2-4ab=(a-b)^2
$$

at $a=z^2$ and $b=y^2$.

## Role in the overall proof

Article 0096 moved `GN5` to `GoldenNorm` in endpoint-square coordinates, and 0097 diagonalized `GoldenNorm` into the discriminant-five form. Independently of that golden-norm calculation, the present theorem records that the same endpoint-square coordinates preserve

$$
M^2-4N^2=(z^2-y^2)^2,
$$

a perfect-square boundary.

Thus the same coordinate pair $(M,N)$ carries two structures at once.

1. Golden-norm side: `GoldenNorm M N`.
2. Square-world side: $M^2-4N^2$ is a perfect square.

This simultaneous preservation of a golden norm and a square discriminant on the same coordinates is exactly the design used immediately afterward in `SquareGoldenNormalForm.lean`. In particular, the later theorem `squareGolden_square_discriminant` directly reuses the present theorem.

## Direct dependencies

There are no direct project-local definition or lemma dependencies. The statement uses only `ℤ`, integer addition, subtraction, multiplication, and powers.

The proof depends on Mathlib's `ring` tactic.

A later declaration that directly reuses this theorem is the following theorem from the `SquareGoldenNormalForm.lean` section:

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

## Proof flow

The proof is one line:

```lean
ring
```

`ring` normalizes both sides as integer polynomials. Expanding the left-hand side gives

$$
z^4+2z^2y^2+y^4-4z^2y^2,
$$

which simplifies to

$$
z^4-2z^2y^2+y^4.
$$

The right-hand side

$$
(z^2-y^2)^2
$$

has the same normal form, so the goal closes.

## Lean-specific processing

The theorem is already stated over `ℤ`, so unlike 0096 it needs no `push_cast` to move from naturals to integers. It also has no project-local named definition that must be unfolded.

Because the proof is a pure identity in a commutative ring with subtraction, `ring` is the natural tactic. `nlinarith` can sometimes solve related polynomial goals when supplied with suitable hypotheses, but here there are no hypotheses and `ring` expresses the intent more directly.

Lean represents `^ 2` through `Pow.pow`, but `ring` handles natural exponents during polynomial normalization, so no explicit rewrite by `pow_two` is required.

## Redundancy and duplication

Mathematically, this is a specialization of the more general identity

$$
(a+b)^2-4ab=(a-b)^2,
$$

so the calculation itself is not unique. In addition, the later `squareGolden_square_discriminant` becomes the same identity after unfolding `SquareGoldenM` and `SquareGoldenN`.

However, keeping the present theorem separate makes it reusable as a general endpoint-square identity, independent of the later named coordinates `SquareGoldenM/N`. The duplication is therefore better understood as an intentional separation between a reusable algebraic layer and a later semantic coordinate layer.

## Optimization candidates

1. Keep the theorem as is. A one-line proof with a meaningful name is already strong.
2. Introduce the general lemma `(a+b)^2 - 4*a*b = (a-b)^2`, then specialize with `a=z^2`, `b=y^2`. For this theorem alone, the abstraction cost is probably larger than the gain.
3. Package the endpoint-square coordinates into a structure carrying `mass := z^2+y^2`, `cross := zy`, and the square-discriminant invariant together. This becomes attractive if the coordinate pair is passed around frequently later.
4. Keep `squareGolden_square_discriminant` as an unfolding step followed by an application of this theorem, avoiding duplicated `ring` calculations. The current source already follows this strategy.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. According to the generated source manifest, this theorem belongs to the `DkMath/FLT/Five/SquareGoldenBridge.lean` section.

For the theorem in isolation, the direct requirements are the commutative-ring structure on integers, natural-number powers, and the `ring` tactic. Therefore the umbrella `Mathlib` import is likely broader than necessary for this theorem alone. A reduction centered around `Mathlib.Tactic.Ring` is a plausible candidate, but the surrounding module also contains theorems using `push_cast` and `norm_num`, so the exact minimal import set for the whole source module is not asserted without a Lean build.

## Comparator challenge suitability

Suitable, although at a foundational difficulty level.

Three proof styles can be compared:

1. The current single `ring` call.
2. Prove the general identity `(a+b)^2-4ab=(a-b)^2` and specialize it.
3. Expand with rewrites such as `pow_two`, then finish with `ring_nf` or local algebraic rewrites.

Useful comparison axes are proof length, mathematical transparency, generality, dependency count, and downstream reuse by `squareGolden_square_discriminant`. This makes a good small Comparator example contrasting shortest kernel-checked algebra with a more structure-revealing proof.

## Correspondence with existing materials

The formal final authority is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The generated source marker confirms that this theorem belongs to the `DkMath/FLT/Five/SquareGoldenBridge.lean` section, followed immediately by `goldenNorm_eq_fifth_power_of_GN5` and then by `SquareGoldenNormalForm.lean`.

For the existing Japanese and English PDFs, GitHub code search again returned an upstream 502 error during this run, so no exact page or section correspondence could be verified. No PDF location has been filled in by inference.

## Next theorem to read

The next theorem in source order is

```lean
theorem goldenNorm_eq_fifth_power_of_GN5
    {g y b : ℕ} (hGN : GN5 g y = b ^ 5) :
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
      (b : ℤ) ^ 5 := by
  calc
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
        (GN5 g y : ℤ) := (GN5_eq_goldenNorm_squareLink g y).symm
    _ = ((b ^ 5 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hGN
    _ = (b : ℤ) ^ 5 := by norm_num
```

The present article records the independent perfect-square boundary retained by the endpoint-square coordinates. The next article transports the natural-number fifth-power fact `GN5 g y = b^5` into the golden world as `GoldenNorm = b^5` on those same coordinates. Together these provide the two data channels needed for the subsequent simultaneous square/golden normal form.
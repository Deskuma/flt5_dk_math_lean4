# 0102 — `squareGolden_tenth_boundary_base`

## Lean type

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

## Mathematical statement

Writing 0100 `SquareGoldenM` and 0101 `SquareGoldenN` as

$$
M=z^2+y^2,\qquad N=zy,
$$

this theorem states

$$
M-2N=(z-y)^2.
$$

After unfolding the definitions, this is simply the completing-the-square identity

$$
z^2+y^2-2zy=(z-y)^2.
$$

Its importance is that the linear combination $M-2N$ of the square/golden coordinates is always a perfect square. Thus the pair $(M,N)$ retains not only golden-norm information but also the square of the original endpoint difference $z-y$.

## Role in the overall proof

`SquareGoldenNormalForm.lean` lifts the Branch-B fifth-power normal form into a packet that simultaneously preserves square-world and golden-norm information. The present theorem is the first preservation law in that module.

Later, `exists_branchB_squareGoldenNormalForm` uses the fifth-power normal-form relation

$$
z=y+a^5
$$

and combines it with the present theorem to obtain

$$
M-2N=(z-y)^2=(a^5)^2=a^{10}.
$$

The Lean source directly invokes `squareGolden_tenth_boundary_base z y` when constructing the `tenth_boundary` field.

Therefore this theorem is the first stage of the bridge

$$
\text{endpoint difference}
\longrightarrow
\text{square boundary}
\longrightarrow
\text{tenth-power boundary}.
$$

Where 0098 `endpoint_square_discriminant` preserves the quadratic discriminant

$$
M^2-4N^2=(z^2-y^2)^2,
$$

this theorem preserves the lower-degree linear combination

$$
M-2N=(z-y)^2.
$$

The later packet keeps both kinds of square data.

## Direct dependencies

There are exactly two project-local direct dependencies:

1. 0100 `SquareGoldenM`
2. 0101 `SquareGoldenN`

They are defined by

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2

def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

The proof also uses the `ring` tactic. No other project-local theorem is called.

## Proof flow

The proof has only two stages.

### 1. Unfold the coordinate definitions

```lean
unfold SquareGoldenM SquareGoldenN
```

This changes the goal essentially into

```lean
(z : ℤ) ^ 2 + (y : ℤ) ^ 2 - 2 * ((z : ℤ) * (y : ℤ)) =
  ((z : ℤ) - (y : ℤ)) ^ 2
```

### 2. Normalize the polynomial identity

```lean
ring
```

normalizes both sides as polynomials over the integers and closes the equality.

Mathematically this is completing the square; in Lean, `ring` performs the expansion, reassociation, and coefficient normalization in one step.

## Lean-specific processing

### 1. Natural-number inputs are already lifted to integer coordinates

Because `SquareGoldenM` and `SquareGoldenN` return `ℤ`, the theorem can directly use

```lean
(z : ℤ) - (y : ℤ)
```

without encountering truncating natural-number subtraction.

If the right-hand side were written as `((z - y : ℕ) : ℤ)^2`, an assumption such as $y\le z$ would be needed. Using the integer difference makes the identity unconditional.

### 2. No cast-normalization tactic is needed

After unfolding the coordinate definitions, every term already lives in `ℤ`, so neither `push_cast` nor `norm_cast` is required.

### 3. `ring` handles subtraction directly

Since the integers form a ring, `ring` can process

$$
(z-y)^2=z^2-2zy+y^2
$$

as an ordinary ring identity. No order hypothesis on the naturals is needed.

## Redundancy and duplication

The mathematical content is a special case of the classical identity

$$
a^2+b^2-2ab=(a-b)^2.
$$

If a general lemma for that identity existed, this theorem could be derived from it with `simpa`.

Also, 0098 `endpoint_square_discriminant` proves

$$
(z^2+y^2)^2-4(zy)^2=(z^2-y^2)^2,
$$

which is another perfect-square identity in the same endpoint-square coordinates. The two results are computationally close but preserve different invariants, so they are not redundant architecturally.

Later, `exists_branchB_squareGoldenNormalForm` uses this theorem once and then substitutes $z-y=a^5$ to reach $a^{10}$. One could combine those steps into a single theorem, but the current split cleanly separates a pure coordinate identity from FLT5-specific provenance, which improves auditability.

## Optimization candidates

### Candidate A — Abstract the general completing-the-square lemma

For example, one could first prove

```lean
theorem sq_add_sq_sub_two_mul_eq_sq_sub (a b : ℤ) :
    a ^ 2 + b ^ 2 - 2 * (a * b) = (a - b) ^ 2 := by
  ring
```

and derive the present theorem using `simpa [SquareGoldenM, SquareGoldenN]`.

However, the current theorem is already extremely short, and introducing a general lemma increases the declaration count. Without another reuse site, that abstraction may be unnecessary.

### Candidate B — Compare with `ring_nf`

A proof using `ring_nf` is conceivable, but `unfold ...; ring` expresses the intent more directly: unfold the coordinate API, then close a polynomial identity.

### Candidate C — Keep the current proof

As the first theorem over the two-coordinate API, the present form is especially easy to audit. There is almost no meaningful proof-length optimization left.

## Required Mathlib imports and import-optimization candidates

The generated standalone artifact uses

```lean
import Mathlib
```

for the complete file.

For this theorem alone, the needed ingredients are essentially:

1. `ℕ`, `ℤ`, and the coercion from naturals to integers.
2. The definitions `SquareGoldenM` and `SquareGoldenN`.
3. The `ring` tactic.

Thus the main tactic dependency is in the `Mathlib.Tactic.Ring` family. However, the full `SquareGoldenNormalForm.lean` module later uses `exact_mod_cast` together with project-local FLT5 theorems, so the exact minimal import set for the module should not be asserted without a Lean build.

A safe import-optimization process would separate project-local imports from tactic imports and narrow the umbrella `Mathlib` import incrementally, validating each stage with the build. No Lean build is performed in this museum entry.

## Comparator challenge suitability

Yes. This theorem is a small, closed polynomial identity and is therefore well suited to comparing proof styles.

Possible competitors include:

1. The current `unfold ...; ring` proof.
2. Prove a general completing-the-square lemma first, then use `simpa`.
3. A `ring_nf` proof.
4. Test whether a suitable `nlinarith` proof is competitive.

Useful metrics include proof-term simplicity, readability, replay stability, import weight, and generalizability.

For a Comparator challenge, it would be better to compare not only shortest proof length but also which proof most clearly preserves the mathematical meaning of the named coordinate API.

## Next theorem to read

The Lean source places the following theorem immediately afterward:

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

The present theorem preserves the linear square boundary

$$
M-2N=(z-y)^2,
$$

whereas the next theorem preserves the independent square discriminant

$$
M^2-4N^2=(z^2-y^2)^2.
$$

Therefore `squareGolden_square_discriminant` is the natural next declaration in dependency order.

## Sources and notes

The formal basis for this entry is the `SquareGoldenNormalForm.lean` section embedded in the generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch. In that current source, this theorem appears immediately after `SquareGoldenM` and `SquareGoldenN`, and it is directly reused by `exists_branchB_squareGoldenNormalForm` to construct the `tenth_boundary` field.

A concrete page-level correspondence for this theorem in the existing Japanese and English PDFs could not be confirmed in this run. GitHub code search also returned an upstream error, so no PDF section number, page number, or narrative correspondence has been guessed.

The standalone artifact records the split source name as `DkMath/FLT/Five/SquareGoldenNormalForm.lean`; the primary formal evidence for this article is the current generated standalone content that was successfully fetched from the target branch.
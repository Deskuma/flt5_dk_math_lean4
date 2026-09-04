# 0285 — `zeroSectorA`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It defines the lower factor `A` used in the zero-sector inversion. Combining the previously introduced quantities

$$
U=X^2+5s^2,
\qquad
W=4d^5,
$$

it fixes the named integer quantity

$$
A=U-W.
$$

## Lean type

```lean
/-- The lower inversion factor `A = U-W`. -/
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

Thus its full Lean type is

```lean
zeroSectorA : ℤ → ℤ → ℕ → ℤ
```

The inputs `r,s` are integers, `d` is a natural number, and the result is an integer. The cast from `d : ℕ` to `ℤ` is not written directly in this definition; it is handled inside the directly dependent definition 0284 `zeroSectorW`.

## Mathematical meaning

Substituting the definitions from 0282–0284,

$$
X=2r+s,
$$

$$
U=X^2+5s^2,
$$

$$
W=4d^5,
$$

we obtain

$$
A=U-W,
$$

that is,

$$
A=(2r+s)^2+5s^2-4d^5.
$$

If `U` is viewed as the center and `W` as the displacement from that center, then `A` is the **lower symmetric factor**. The immediately following declaration 0286 `zeroSectorB` defines

$$
B=U+W,
$$

so together they form the symmetric factor pair

$$
A=U-W,
\qquad
B=U+W.
$$

This symmetrization allows the later proof to use the difference-of-squares identity

$$
AB=(U-W)(U+W)=U^2-W^2
$$

to convert the zero-sector quartic / fifth-power information into a product factorization.

## Role in the full proof

`zeroSectorA` is the first actual factor in the inversion coordinate system.

In the canonical source, it is paired with 0286 `zeroSectorB` to prove first

$$
AB=20s^4,
$$

and then, using the zero-sector tenth-power split, to obtain

$$
AB=4Q^5.
$$

The source also proves the exact relations

$$
B-A=8d^5,
$$

and

$$
A+B=2U.
$$

Thus `A` is not merely an abbreviation. Later the source proves `A>0` and then defines

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

so that the lower integer factor can be transferred to the natural-number factor `A0`. This naturalized factor then becomes structural data in the later fifth-power factorization / inversion packet.

In this sense, 0285 is the **boundary where the central quantity and the fifth-power displacement are converted into a concrete lower factor usable for product factorization**.

## Direct dependencies

### 0283 `zeroSectorU`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

This supplies the central quantity

$$
U=X^2+5s^2.
$$

### 0284 `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

This supplies the displacement subtracted in the present definition,

$$
W=4d^5.
$$

### 0282 `zeroSectorX`

This is not referenced directly by the body of `zeroSectorA`. It is a **transitive dependency** through `zeroSectorU`.

### Theorem dependencies

Because this declaration is a `def`, it directly uses no proof lemmas. The tenth-power split from 0281 provides the mathematical origin of `d`, but that theorem name does not occur in the Lean definition body.

## Definition / construction flow

### 1. Receive `r,s,d`

```lean
(r s : ℤ) (d : ℕ)
```

The definition takes the integer zero-sector coordinates `r,s` and the natural-number tenth-power root parameter `d`.

### 2. Compute the center `U`

```lean
zeroSectorU r s
```

This is

$$
(2r+s)^2+5s^2.
$$

### 3. Compute the displacement `W`

```lean
zeroSectorW d
```

As an integer, this is

$$
4d^5.
$$

### 4. Subtract in `ℤ`

```lean
zeroSectorU r s - zeroSectorW d
```

and define

$$
A=U-W.
$$

At this stage positivity is not part of the definition. The canonical source proves `A_pos` later using the hypotheses packaged in `GoldenZeroSectorCandidate`. Therefore it would be incorrect to read this declaration alone as asserting `A>0` for arbitrary `r,s,d`.

## Lean-specific processing

There is no tactic proof in this declaration; the right-hand side is the definitional equation itself. Hence

```lean
example (r s : ℤ) (d : ℕ) :
    zeroSectorA r s d = zeroSectorU r s - zeroSectorW d := by
  rfl
```

is closed by `rfl`.

To expand all the way to

$$
A=(2r+s)^2+5s^2-4d^5,
$$

one must unfold several definitions, for example

```lean
unfold zeroSectorA zeroSectorU zeroSectorX zeroSectorW
```

or

```lean
simp only [zeroSectorA, zeroSectorU, zeroSectorX, zeroSectorW]
```

as appropriate.

`zeroSectorA` itself does not write the cast of `d`, so one type boundary is encapsulated inside `zeroSectorW`. This is useful as an API choice: callers pass `d : ℕ` directly.

In the canonical proof of `factor_product_twenty`, the source uses

```lean
unfold zeroSectorA zeroSectorB
ring
```

to normalize

$$
AB=U^2-W^2.
$$

Thus the source deliberately switches between the structural names `A,B` and polynomial expansion only where algebraic normalization is needed.

## Redundancy and duplication

The body is one line, so there is no local computational redundancy.

In principle, later expressions could inline

```lean
zeroSectorU r s - zeroSectorW d
```

and omit the name `zeroSectorA`. In the canonical source, however, `A` appears in many downstream declarations, including

- `factor_product_twenty`,
- `factor_product`,
- `factor_difference`,
- `factor_sum`,
- `A_pos`,
- `A_lt_B`,
- `A0`, and
- `A0_cast`.

Therefore the named definition has substantial structural value; simple inlining would reduce readability and obscure the factorization architecture.

Moreover, `A` and `B` are an exact symmetric pair. Attempting to eliminate only one of the two would damage that symmetry. Keeping the two small parallel definitions is an effective representation of the mathematics in the code.

## Optimization candidates

### Preserve the symmetric-identity API

Rather than repeatedly unfolding `A` and `B` downstream, it is preferable to use the named theorems already present in the source, such as

$$
B-A=8d^5,
\qquad
A+B=2U.
$$

This reduces downstream dependence on implementation details. The source already follows this direction, so the practical optimization is to **prefer the existing API** rather than add more unfolding.

### A simp lemma for `A=U-W`

Because the definition can already be unfolded directly, a separate theorem such as

```lean
@[simp] theorem zeroSectorA_eq ...
```

has limited value. Aggressive `[simp]` unfolding could also erase the useful abstract name `A` too early and produce much larger expressions.

Therefore the present design, without an eager simp rule for this definition, appears reasonable.

### Bundling the factor data in a structure

One could consider bundling `U,W,A,B` into a structure to reduce repeated `r,s,d` arguments. However, later source code already introduces structural packages such as `GoldenZeroSectorCandidate` and the inversion packet. The benefit of introducing another structure at this early definition layer is therefore unverified.

This remains a design possibility rather than a demonstrated improvement.

## Required Mathlib imports and import optimization

The repository's standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For `zeroSectorA` itself, the only new operation beyond its two dependencies is subtraction of two integers. The definition therefore does not intrinsically require all of Mathlib.

However, this run does not perform a Lean build, and the generated source has not been rebuilt as an isolated module to verify a minimal import set. Consequently the exact minimal imports are **unverified**.

A proper import optimization would audit the entire dependency graph of `SignedGoldenZeroSectorInversion`, replace the umbrella `Mathlib` import with narrower integer, natural-number, and polynomial-arithmetic imports, and then verify the result by a Lean build. That verification is intentionally not performed here.

## Comparator challenge suitability

### Assessment: low for the bare definition, high when paired with the `A/B` identities

The bare definitional equality

```lean
zeroSectorA r s d = zeroSectorU r s - zeroSectorW d
```

is solved by `rfl`, so it offers almost no meaningful proof-strategy comparison.

After adding 0286 `zeroSectorB`, however, one can ask for proofs of

$$
AB=U^2-W^2,
$$

$$
B-A=8d^5,
$$

and

$$
A+B=2U.
$$

These are useful Comparator challenges because they expose choices among `unfold`, `simp only`, and `ring`, and test how long a proof preserves the abstract factor names before expanding them.

In particular, the first transformation in `factor_product_twenty`,

$$
AB=U^2-W^2,
$$

is short and self-contained enough to make a good challenge target.

## Comparison with the existing PDFs

The repository tree on the target branch contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`, and
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

In this run, however, GitHub's ordinary UTF-8 file retrieval path rejected the PDF binary, so the PDF body could not be obtained in an analyzable form. Therefore the exact page, section, and wording in which `A=U-W` appears have not been verified.

No PDF-specific correspondence is guessed here. This document is grounded in the canonical Lean source `Flt5DkMath/FLT5StandAlone.lean` and the repository material that could be inspected directly.

## Next declaration to read

The next declaration is **0286 `zeroSectorB`**, also a `def`.

```lean
/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

It introduces

$$
B=U+W.
$$

Together with 0285,

$$
A=U-W,
$$

the inversion factor pair

$$
(A,B)=(U-W,U+W)
$$

is then complete.
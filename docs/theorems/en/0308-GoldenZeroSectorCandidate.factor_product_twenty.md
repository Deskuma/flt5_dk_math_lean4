# 0308 — `GoldenZeroSectorCandidate.factor_product_twenty`

## Declaration kind

This declaration is a **`theorem`**.

It appears immediately after 0307 `GoldenZeroSectorCandidate.discriminant_eq` and converts the discriminant identity already obtained as a difference of squares into the product of the two zero-sector inversion factors `A = U-W` and `B = U+W`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Before sign removal, the two inversion factors multiply to `20*s^4`. -/
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 := by
      unfold zeroSectorA zeroSectorB
      ring
    _ = 20 * p.s ^ 4 := p.discriminant_eq
```

The conclusion is the integer identity

$$
A(r,s,d)B(r,s,d)=20s^4.
$$

## Mathematical meaning

The zero-sector inversion defines

$$
U=X^2+5s^2,
$$

$$
W=4d^5,
$$

$$
A=U-W,
$$

$$
B=U+W.
$$

Therefore the elementary difference-of-squares identity gives

$$
AB=(U-W)(U+W)=U^2-W^2.
$$

The preceding theorem 0307 `discriminant_eq` has already established

$$
U^2-W^2=20s^4,
$$

so combining the two identities yields

$$
AB=20s^4.
$$

The theorem does not create new number-theoretic information by itself. Instead, it repackages the diagonal discriminant information from 0307 into a product of two factors, which is the form needed by the later gcd, 2-adic splitting, and fifth-power factorization arguments.

## Role in the full proof

0307 compresses the quartic identity into the difference of squares

$$
U^2-W^2=20s^4,
$$

whereas 0308 turns that difference of squares into the explicit product of the inversion factors.

This is the boundary between geometric/algebraic reconstruction and multiplicative arithmetic. The following theorem additionally uses the sign-removal formula

$$
s=-5^6c^{10}
$$

to normalize the product into

$$
AB=4Q^5,
\qquad
Q=5^5c^8.
$$

Thus this theorem is the entry point to the central fifth-power product. In particular, the later `A0_mul_B0`, `GoldenZeroSectorInversionPacket.factor_product`, and the two-adic factor-branch decomposition preserve and exploit this multiplicative form.

## Direct dependencies

### `zeroSectorA`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

This defines the lower inversion factor

$$
A=U-W.
$$

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

This defines the upper inversion factor

$$
B=U+W.
$$

### `zeroSectorU`, `zeroSectorW`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2

def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

They provide the center and half-difference from which `A` and `B` are constructed.

### `GoldenZeroSectorCandidate.discriminant_eq`

```lean
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4
```

This is the main preceding theorem consumed by 0308.

### `ring`

After unfolding `A` and `B`, `ring` closes

$$
(U-W)(U+W)=U^2-W^2
$$

as a polynomial identity over the integers.

## Proof flow

1. The first `calc` step starts from the product of `zeroSectorA` and `zeroSectorB`.
2. `unfold zeroSectorA zeroSectorB` expands the target to

$$
(U-W)(U+W)=U^2-W^2.
$$

3. `ring` normalizes and closes this difference-of-squares identity.
4. The second step applies `p.discriminant_eq` directly to obtain

$$
U^2-W^2=20s^4.
$$

5. Hence `A*B = 20*s^4` follows.

## Lean-specific handling

The first `unfold` expands only `zeroSectorA` and `zeroSectorB`; it deliberately leaves `zeroSectorU`, `zeroSectorW`, and `zeroSectorX` folded. For `ring`, `U` and `W` may remain ring atoms, so their internal formulas do not need to be exposed again.

This is a useful abstraction boundary. It avoids re-expanding `U=X^2+5s^2` and `W=4d^5`, while allowing the already-proved discriminant identity from 0307 to be reused directly.

The second step is written simply as

```lean
_ = 20 * p.s ^ 4 := p.discriminant_eq
```

so the theorem is supplied as a term without an additional `exact` or `rw` step.

## Redundancy and duplication

The proof is extremely short and contains essentially no local duplication.

Conceptually, the identity

$$
(U-W)(U+W)=U^2-W^2
$$

is a general ring identity rather than anything specific to FLT5. If this exact transformation appeared repeatedly, it could be extracted into a reusable lemma.

For this single location, however, introducing such a lemma would likely add more naming and argument plumbing than the present `ring` call.

## Optimization candidates

One possible optimization is to replace `ring` with an existing difference-of-squares identity, or to factor out a small general lemma. Conceptually one could isolate

```lean
have hsq :
    (zeroSectorU p.r p.s - zeroSectorW p.d) *
      (zeroSectorU p.r p.s + zeroSectorW p.d) =
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 := by
  ring
```

as reusable algebra.

Nevertheless, the current

```lean
unfold zeroSectorA zeroSectorB
ring
```

is already concise and preserves the abstraction of `zeroSectorU` and `zeroSectorW`, so it is locally a strong implementation.

It would also be technically possible to merge 0307 and 0308 into a single theorem, but keeping the discriminant identity and its factorization as separate responsibilities makes the dependency graph easier to read.

The exact minimal Lean forms of these alternatives are **not verified here**, because this run does not perform a Lean build.

## Required Mathlib import and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The facilities directly needed by this theorem include at least:

- integer addition, subtraction, multiplication, and powers;
- `calc`;
- `unfold`;
- the `ring` tactic;
- `zeroSectorA`, `zeroSectorB`, `zeroSectorU`, `zeroSectorW`;
- `GoldenZeroSectorCandidate.discriminant_eq`.

This proof does not use `omega`, `linarith`, `positivity`, `norm_num`, or `exact_mod_cast`.

The generated source module is `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`. The exact minimal Mathlib import set is **not verified** under the no-build constraint of this task; establishing it would require checking that source module's import graph separately.

## Comparator challenge suitability

**Suitable; beginner to intermediate difficulty.**

A Comparator challenge could compare:

- the direct `unfold zeroSectorA zeroSectorB; ring` proof;
- a proof applying a general difference-of-squares lemma;
- whether 0307 `discriminant_eq` is reused rather than reproved;
- how much the proof grows if `zeroSectorU` and `zeroSectorW` are unnecessarily unfolded.

This makes it more interesting than a bare `ring` hole: the main design question is the abstraction boundary at which an already-proved theorem should be reused.

## Cross-check against the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed from the GitHub repository.

However, the normal GitHub connector text fetch does not return binary PDF contents, so this run cannot directly match 0308 to a specific PDF page, section, or equation number. No such PDF location is inferred.

The Lean code, declaration order, direct dependencies, and relationship to the following declaration in this explanation are grounded in the repository's `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0309 `GoldenZeroSectorCandidate.factor_product`, again a **`theorem`**.

The canonical Lean source continues with

```lean
/-- Central fifth-power product of the positive inversion factors. -/
theorem factor_product (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        20 * p.s ^ 4 := p.factor_product_twenty
    _ = 4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
      rw [p.s_eq_neg_five_pow_mul_tenth]
      unfold zeroSectorQ
      push_cast
      ring
```

It substitutes the sign-removed coordinate

$$
s=-5^6c^{10}
$$

into the 0308 identity

$$
AB=20s^4
$$

and, with

$$
Q=5^5c^8,
$$

normalizes it to

$$
AB=4Q^5.
$$

This is the central fifth-power product theorem of the zero-sector inversion.
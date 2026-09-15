# 0307 — `GoldenZeroSectorCandidate.discriminant_eq`

## Declaration kind

This is a **`theorem`**.

It appears immediately after 0306 `GoldenZeroSectorCandidate.square_reconstruction` and converts the diagonal quartic identity into a difference-of-squares relation using the zero-sector inversion quantities `U` and `W`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The diagonal quartic identity becomes a difference of two squares. -/
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4 := by
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq p.r p.s
  rw [p.H_eq_tenth] at hdiag
  unfold zeroSectorU zeroSectorW
  calc
    (zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2) ^ 2 -
        (4 * (p.d : ℤ) ^ 5) ^ 2 =
        (zeroSectorX p.r p.s ^ 4 +
          10 * zeroSectorX p.r p.s ^ 2 * p.s ^ 2 +
          5 * p.s ^ 4 - 16 * (p.d : ℤ) ^ 10) +
          20 * p.s ^ 4 := by ring
    _ = 20 * p.s ^ 4 := by rw [← hdiag]; ring
```

The conclusion is the integer identity

$$
U(r,s)^2-W(d)^2=20s^4.
$$

## Mathematical meaning

The relevant definitions are

$$
X=2r+s,
$$

$$
U=X^2+5s^2,
$$

$$
W=4d^5.
$$

The preceding theorem `sixteen_mul_goldenFifthSndFactor_eq` gives

$$
16H(r,s)=X^4+10X^2s^2+5s^4,
$$

while the candidate theorem `H_eq_tenth` gives

$$
H(r,s)=d^{10}.
$$

Hence

$$
16d^{10}=X^4+10X^2s^2+5s^4.
$$

Also,

$$
U^2=(X^2+5s^2)^2
=X^4+10X^2s^2+25s^4,
$$

and

$$
W^2=(4d^5)^2=16d^{10}.
$$

Subtracting therefore yields

$$
U^2-W^2=20s^4.
$$

The theorem compresses the diagonalized quartic factor together with the tenth-power split into a form immediately suitable for factorization.

## Role in the full proof

This is a central transition in the zero-sector inversion layer. Up through 0306, the proof records that `U` retains the original square coordinate. In 0307, `W` is brought in and the expression becomes

$$
U^2-W^2,
$$

which factors as a product.

The next theorem, 0308 `factor_product_twenty`, uses

$$
(U-W)(U+W)=U^2-W^2
$$

to obtain

$$
AB=20s^4.
$$

Thus 0307 is the bridge from the quartic identity to the inversion-factor product.

## Direct dependencies

### `sixteen_mul_goldenFifthSndFactor_eq`

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4
```

This supplies the diagonal quartic identity.

### `GoldenZeroSectorCandidate.H_eq_tenth`

```lean
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

This replaces the quartic factor by the tenth power of `d`.

### `zeroSectorU`, `zeroSectorW`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2

def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

These definitions build the two squares appearing in the conclusion.

### `ring`

The proof uses polynomial normalization in both algebraic steps.

## Proof flow

1. Obtain `sixteen_mul_goldenFifthSndFactor_eq p.r p.s` as `hdiag`.
2. Rewrite `hdiag` using `p.H_eq_tenth`, replacing $H$ by $d^{10}$.
3. Unfold `zeroSectorU` and `zeroSectorW` so that the goal becomes a polynomial identity in $X,s,d$.
4. The first `ring` proves

$$
U^2-W^2
=
\bigl(X^4+10X^2s^2+5s^4-16d^{10}\bigr)+20s^4.
$$

5. `rw [← hdiag]` identifies the parenthesized expression with zero.
6. The final `ring` closes the remaining arithmetic and yields $20s^4$.

## Lean-specific processing

The rewrite

```lean
rw [p.H_eq_tenth] at hdiag
```

acts on the auxiliary identity rather than on the main goal. This is an important proof-structuring choice: the quartic factor is converted to a tenth power at the source-identity level, after which the remainder of the theorem is pure integer-ring algebra.

`zeroSectorX` is intentionally not unfolded. For `ring`, `zeroSectorX p.r p.s` can remain an atomic ring expression; expanding it to `2*r+s` is unnecessary. This preserves the abstraction boundary created by diagonalization.

## Redundancy and duplication

The proof itself is compact and contains little obvious redundancy. Conceptually, however, it does not call 0306 `square_reconstruction`; instead it unfolds `zeroSectorU` again.

That is not necessarily a defect. The present theorem must align the coefficients of the quartic diagonal identity directly, and exposing the concrete form `U=X^2+5s^2` is particularly convenient for `ring`.

## Optimization candidates

One possible refactoring would separate the candidate-independent algebra into a generic lemma, for example:

```lean
theorem zeroSector_discriminant_algebra
    (X s d : ℤ)
    (h : 16 * d ^ 10 = X ^ 4 + 10 * X ^ 2 * s ^ 2 + 5 * s ^ 4) :
    (X ^ 2 + 5 * s ^ 2) ^ 2 - (4 * d ^ 5) ^ 2 = 20 * s ^ 4 := by
  nlinarith [h]
```

This exact proposal is **unverified**, because no Lean build is performed in this museum task. A proof based on 0306 `square_reconstruction` is another possible refactoring, although the current two-stage `ring` proof may remain shorter and more robust.

## Required Mathlib imports and import optimization

The standalone source uses the broad Mathlib environment. This theorem directly needs at least:

- integers `ℤ`
- powers, multiplication, and subtraction
- rewriting with `rw`
- the `ring` tactic
- `zeroSectorU`, `zeroSectorW`, and `zeroSectorX`
- `sixteen_mul_goldenFifthSndFactor_eq`
- `H_eq_tenth`

The proof does not use `omega`, `linarith`, `positivity`, `norm_num`, or `exact_mod_cast`.

The exact minimal Mathlib import set is **not verified**, because Lean builds are explicitly excluded from this task. Import optimization would require checking the import graph of the source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` and validating a reduced set separately.

## Comparator challenge suitability

**Suitable; intermediate difficulty.**

A useful Comparator challenge would compare:

- rewriting `hdiag` with `H_eq_tenth` before polynomial normalization,
- leaving `zeroSectorX` folded as a ring atom,
- one large `ring` proof versus the current two-step `calc` proof,
- a version attempting to route through `square_reconstruction`.

This makes the theorem a good exercise in proof architecture rather than merely a `ring` hole-filling task.

## PDF cross-check

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed from the repository.

However, the ordinary GitHub text fetch available in this run does not return the binary PDF body, so this execution could not directly match 0307 to a specific PDF page, section, or equation number. No location in the PDFs is therefore inferred.

The Lean code, declaration order, direct dependencies, and relationship to the following declaration are grounded in the repository file `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0308 `GoldenZeroSectorCandidate.factor_product_twenty`, also a **`theorem`**.

The repository source continues with:

```lean
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

Thus 0307's

$$
U^2-W^2=20s^4
$$

is converted, using $A=U-W$ and $B=U+W$, into

$$
AB=20s^4,
$$

the first explicit factor-product theorem of the inversion step.
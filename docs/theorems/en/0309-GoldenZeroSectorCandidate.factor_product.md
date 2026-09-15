# 0309 — `GoldenZeroSectorCandidate.factor_product`

## Declaration kind

This declaration is a **`theorem`**.

It takes the identity

$$
A B = 20s^4
$$

proved in 0308 `GoldenZeroSectorCandidate.factor_product_twenty`, and normalizes it using the zero-sector candidate's exact sign-removal formula together with the definition of the fifth-power mass `Q`, obtaining

$$
A B = 4Q^5.
$$

The module description of `SignedGoldenZeroSectorInversion` itself highlights this equality as one of the central identities of the certified inversion.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

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

The conclusion is an equality in `ℤ`:

$$
A(r,s,d)B(r,s,d)=4Q(c)^5.
$$

Here

$$
Q(c)=5^5c^8.
$$

## Mathematical meaning

0308 establishes

$$
AB=20s^4.
$$

The candidate sign-removal theorem gives

$$
s=-5^6c^{10}.
$$

Taking the fourth power removes the sign:

$$
s^4=5^{24}c^{40}.
$$

Hence

$$
20s^4=20\cdot 5^{24}c^{40}
      =4\cdot 5^{25}c^{40}.
$$

On the other hand,

$$
Q=5^5c^8,
$$

so

$$
Q^5=5^{25}c^{40}.
$$

Therefore

$$
20s^4=4Q^5,
$$

and consequently

$$
AB=4Q^5.
$$

The point is not merely to rewrite a product. It reorganizes `20*s^4` into a small 2-adic coefficient `4` times a perfect fifth power `Q^5`. This is the form that later gcd splitting and 2-adic branch analysis can use directly.

## Role in the full proof

This theorem is the central normalization point of the zero-sector inversion.

0307 `discriminant_eq` converts the quartic identity into the difference of squares

$$
U^2-W^2=20s^4.
$$

0308 `factor_product_twenty` turns that into the multiplicative form

$$
AB=20s^4.
$$

The present theorem then incorporates the candidate's tenth-power split and obtains

$$
AB=4Q^5.
$$

From this point onward, the proof no longer has to carry the large fourth power of the signed coordinate `s` explicitly. Instead, it can work with the fact that the product of the two inversion factors is almost a fifth power, up to the small coefficient `4`.

The module header explicitly records

```text
A*B = 4*Q^5 for Q = 5^5*c^8
```

so this identity is one of the principal invariants preserved by the inversion packet.

## Direct dependencies

### `GoldenZeroSectorCandidate.factor_product_twenty`

```lean
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4
```

This immediately supplies the first step of the current theorem.

### `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`

```lean
theorem s_eq_neg_five_pow_mul_tenth (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10)
```

This earlier theorem reconstructs the exact sign of `s` from the candidate field

```lean
s_natAbs_eq : s.natAbs = 5 ^ 6 * c ^ 10
```

together with `s < 0`. The proof here rewrites `s^4` using this exact equality.

### `zeroSectorQ`

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

This is the fifth-power mass

$$
Q=5^5c^8.
$$

Its exponents are chosen so that

$$
Q^5=5^{25}c^{40},
$$

which exactly absorbs the 5-adic part of `20*s^4`.

### `zeroSectorA`, `zeroSectorB`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

These are the two inversion factors forming the left-hand side.

### `push_cast`

Because `zeroSectorQ : ℕ → ℕ` while the product `A*B` lives in `ℤ`, `push_cast` pushes natural-number operations through the cast so that the remaining goal is a single integer ring identity.

### `ring`

After rewriting and unfolding, `ring` closes the polynomial identity

$$
20(-5^6c^{10})^4=4(5^5c^8)^5.
$$

## Proof flow

1. The first `calc` step applies 0308 `p.factor_product_twenty` directly, reducing the goal to

$$
20s^4=4Q^5.
$$
2. `rw [p.s_eq_neg_five_pow_mul_tenth]` replaces `s` by

$$
-5^6c^{10}.
$$
3. `unfold zeroSectorQ` expands the right-hand side to the definition

$$
Q=5^5c^8.
$$
4. `push_cast` normalizes casts from `ℕ` into `ℤ`.
5. `ring` normalizes the exponents and coefficients and proves `20*s^4 = 4*Q^5`.
6. The two `calc` steps combine to yield `A*B = 4*Q^5`.

## Lean-specific processing

A central type issue is that `zeroSectorQ` has type `ℕ → ℕ`, whereas `zeroSectorA` and `zeroSectorB` take values in `ℤ`. Therefore the theorem statement contains the explicit cast

```lean
(zeroSectorQ p.c : ℤ)
```

before raising `Q` to the fifth power.

After `unfold zeroSectorQ`, expressions such as `5 ^ 5 * p.c ^ 8` originate on the natural-number side. `push_cast` distributes the cast through multiplication and powers, leaving a clean integer expression for `ring`.

The proof also rewrites with an exact signed equality for `s`. Since the exponent is four, the negative sign disappears in the final normalization, and this even-power arithmetic is handled automatically by `ring`.

## Redundancy and duplication

The proof is short and contains essentially no local duplication.

Conceptually, however, the normalization

$$
20(-5^6c^{10})^4=4(5^5c^8)^5
$$

is an important FLT5-specific exponent identity, while the current implementation leaves it embedded inside the sequence `rw` / `unfold` / `push_cast` / `ring`.

If the same normalization is reused later, it could be extracted into a named lemma such as `twenty_mul_visible_fourth_eq_four_mul_Q_fifth`. For this theorem alone, however, the present four-line local proof is shorter and clearer.

## Optimization candidates

One possible refactoring is to isolate the mass-normalization step first:

```lean
have hmass : 20 * p.s ^ 4 = 4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
  rw [p.s_eq_neg_five_pow_mul_tenth]
  unfold zeroSectorQ
  push_cast
  ring
```

Then `factor_product` becomes only the composition of 0308 with this mass identity.

The current implementation has the advantage of not introducing another theorem and of keeping the full normalization visible in one place.

Using `norm_num` to simplify only the constant powers is another theoretical possibility, but because powers of the variable `c` are involved as well, `ring` is the more natural closer. Since Lean builds are forbidden in this task, no claim is made here about a verified minimal proof or import set.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The present theorem directly needs at least:

- powers and multiplication on `ℕ` and `ℤ`,
- casts from `Nat` to `Int`,
- `calc`,
- `rw`,
- `unfold`,
- `push_cast`,
- `ring`,
- the earlier theorem `factor_product_twenty`,
- the earlier theorem `s_eq_neg_five_pow_mul_tenth`.

The proof does not directly use `omega`, `linarith`, `nlinarith`, `positivity`, or `exact_mod_cast`.

The generated source module is `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`. The exact minimal Mathlib import set has not been verified because this task forbids Lean builds. It is plausible that the imports can be reduced to the tactic support for `ring` and `push_cast` plus the necessary integer/natural-number cast infrastructure, but that remains unverified here.

## Comparator challenge suitability

**Suitable, medium difficulty.**

Useful comparison dimensions include:

- reusing `s_eq_neg_five_pow_mul_tenth` versus rebuilding the signed formula from `s_natAbs_eq`,
- preserving the `zeroSectorQ` abstraction versus unfolding it immediately,
- using `push_cast` versus a proof based on explicit `norm_cast` / `exact_mod_cast` transformations,
- extracting `20*s^4 = 4*Q^5` into a standalone lemma versus keeping the normalization local.

This makes a good Comparator challenge because it tests not only algebraic normalization but also the `ℕ`/`ℤ` boundary, reuse of existing theorems, and the choice of abstraction boundary.

## PDF cross-check

The target branch contains the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The normal GitHub text-fetch path does not return binary PDF contents, so this run could not directly cross-check the exact PDF page, section, or equation number corresponding to this theorem. No PDF location is therefore inferred.

The Lean code, declaration order, definitions, direct dependencies, and relation to following declarations in this explanation are grounded in the repository source `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0310 `GoldenZeroSectorCandidate.factor_difference`, again a **`theorem`**.

The Lean source continues with

```lean
/-- Exact distance between the upper and lower inversion factors. -/
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

Where 0309 fixes the product

$$
AB=4Q^5,
$$

0310 fixes the exact distance between the two factors:

$$
B-A=8d^5.
$$

Together, the product and difference provide the next layer of constraints required by the inversion-factor arithmetic.
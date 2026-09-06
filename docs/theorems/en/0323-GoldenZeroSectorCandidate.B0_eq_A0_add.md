# 0323 — `GoldenZeroSectorCandidate.B0_eq_A0_add`

## Declaration kind

This is a **`theorem`**.

After 0316–0322 construct the positive natural representatives `A0`, `B0` of `zeroSectorA`, `zeroSectorB` and transport the product identity to `ℕ`, this theorem transports the integer factor difference to a **subtraction-free additive form over natural numbers**.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Additive natural form of the factor difference, avoiding subtraction. -/
theorem B0_eq_A0_add (p : GoldenZeroSectorCandidate) :
    p.B0 = p.A0 + 8 * p.d ^ 5 := by
  have hdiff := p.factor_difference
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith
  exact_mod_cast hcasts
```

The type is

```lean
p.B0 = p.A0 + 8 * p.d ^ 5
```

and both sides live in `ℕ`.

## Mathematical statement

Write the signed integer factors as

$$
A=\operatorname{zeroSectorA}(r,s,d),\qquad
B=\operatorname{zeroSectorB}(r,s,d).
$$

The upstream theorem `factor_difference` proves over `ℤ` that

$$
B-A=8d^5.
$$

By 0318 `A0_cast` and 0319 `B0_cast`, we already have

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B.
$$

Hence over the integers,

$$
(B_0:\mathbb Z)-(A_0:\mathbb Z)=8(d:\mathbb Z)^5.
$$

Rearranging before returning to naturals gives

$$
(B_0:\mathbb Z)=(A_0:\mathbb Z)+8(d:\mathbb Z)^5,
$$

and therefore

$$
B_0=A_0+8d^5.
$$

The crucial point is that natural-number subtraction is truncated. For downstream divisibility, parity, and factorization arguments, the additive equation

$$
B_0=A_0+8d^5
$$

is a safer and stronger API than a natural-number subtraction statement.

## Role in the full proof

0322 `A0_mul_B0` transports the signed product

$$
AB=4Q^5
$$

to

$$
A_0B_0=4Q^5.
$$

The present theorem transports the signed difference

$$
B-A=8d^5
$$

to the natural additive identity

$$
B_0=A_0+8d^5.
$$

At this point the natural factor data needed downstream is complete. Immediately afterwards, `GoldenZeroSectorInversionPacket` stores this theorem directly as

```lean
factor_difference :
  source.B0 = source.A0 + 8 * source.d ^ 5
```

for use by the factorization phase.

Downstream code uses this identity to transfer divisibility between `A0` and `B0`, force common prime factors into `d`, control powers of two in both factors, and build the odd/even fifth-power difference branches.

Thus this theorem is not merely a cosmetic rewrite. It fixes the canonical natural-number API for the factor difference.

## Direct dependencies

### `GoldenZeroSectorCandidate.factor_difference`

The proof begins with

```lean
have hdiff := p.factor_difference
```

The current source states

```lean
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

which is exactly

$$
B-A=8d^5.
$$

### `GoldenZeroSectorCandidate.A0_cast`

0318 proves

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

that is,

$$
(A_0:\mathbb Z)=A.
$$

### `GoldenZeroSectorCandidate.B0_cast`

0319 proves

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

that is,

$$
(B_0:\mathbb Z)=B.
$$

### `linarith`

This tactic transforms the subtraction equation supplied by `factor_difference` into the additive cast equation required for `hcasts`.

### `exact_mod_cast`

This transports the final integer equality

```lean
(p.B0 : ℤ) = (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5
```

back to the corresponding equality in `ℕ`.

## Proof flow

1. Obtain `p.factor_difference` as `hdiff`.
2. State an intermediate integer equality `hcasts` whose terms are casts of the natural representatives.
3. Rewrite with `p.A0_cast` and `p.B0_cast`, converting the casted representatives into the signed factors `A` and `B`.
4. The goal for `hcasts` is then essentially

   ```lean
   zeroSectorB ... = zeroSectorA ... + 8 * (p.d : ℤ) ^ 5
   ```

5. Since `hdiff` states

   ```lean
   zeroSectorB ... - zeroSectorA ... = 8 * (p.d : ℤ) ^ 5
   ```

   `linarith` performs the linear rearrangement from subtraction form to addition form.
6. `exact_mod_cast hcasts` transports the result back to the natural-number equality and closes the theorem.

## Lean-specific processing

### Keeping subtraction in `ℤ`

Lean's `Nat.sub` is truncated subtraction. Therefore, rather than casting an equation containing natural subtraction, the proof first stays in `ℤ` and changes

```lean
B - A = 8 * d ^ 5
```

into

```lean
B = A + 8 * d ^ 5
```

before returning to `ℕ`.

The docstring phrase `avoiding subtraction` precisely captures this type-theoretic design choice.

### Rewrite direction

In 0322, the proof used `← p.A0_cast` and `← p.B0_cast` because it needed to replace signed factors by casts of the natural representatives. Here the intermediate statement `hcasts` already contains `(A0 : ℤ)` and `(B0 : ℤ)`, so the proof uses

```lean
rw [p.A0_cast, p.B0_cast]
```

in the forward direction.

This contrast makes 0322 and 0323 especially useful to read together.

### `linarith`

`linarith` does not analyze the fifth power. It treats `(p.d : ℤ)^5` as an atomic term and performs only the linear transformation

$$
B-A=C
$$

to

$$
B=A+C.
$$

### `exact_mod_cast`

The final cast removal is likewise not new mathematical reasoning. It transports an equality already known to consist of casts of natural-number expressions across the `ℕ` / `ℤ` boundary.

## Redundancy and duplication

The proof is short and has little genuine redundancy.

```lean
have hdiff := p.factor_difference
```

could perhaps be inlined into `linarith [p.factor_difference]`, but naming `hdiff` makes the dependency on the upstream subtraction identity explicit.

The cast-bridge pattern resembles 0322 `A0_mul_B0`, but this theorem additionally requires subtraction-to-addition normalization, so the similarity is structural rather than duplicated proof content.

`A0_pos`, `B0_pos`, and `A_lt_B` are not referenced directly by the proof term. This is not accidental redundancy: the relevant sign and representative information has already been packaged into `A0_cast`, `B0_cast`, and the upstream signed identity.

## Optimization candidates

One possible shorter variant is conceptually

```lean
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith [p.factor_difference]
  exact_mod_cast hcasts
```

which may eliminate the separate `hdiff` binding.

Another design would use an explicit lemma expressing

```lean
x - y = z → x = y + z
```

under the appropriate ordered-ring assumptions, reducing reliance on `linarith` and making the algebraic transformation more explicit.

The current proof is already concise, and `linarith` is used in a tightly controlled way, so the practical gain from further shortening is small. These alternatives are **unverified**, because no Lean build is performed in this task.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The main Mathlib functionality directly used here is

- `rw`
- `linarith`
- `exact_mod_cast`
- coercions between `Nat` and `Int`
- cast normalization for multiplication and powers

Project-local dependencies are

- `GoldenZeroSectorCandidate.factor_difference`
- `GoldenZeroSectorCandidate.A0_cast`
- `GoldenZeroSectorCandidate.B0_cast`

This individual theorem could probably work with imports much narrower than all of `Mathlib`. However, the **exact minimal import set has not been verified without a Lean build**, especially when the dependency closure of the upstream declarations is included. Import reduction is therefore only an optimization candidate.

## Comparator challenge suitability

**Yes. It is a particularly useful small challenge because of the natural-number subtraction issue.**

Possible variants to compare are

1. the current `rw` + `linarith` + `exact_mod_cast` proof,
2. a proof using an explicit subtraction-to-addition lemma instead of `linarith`,
3. an `omega`-centered proof combining integer and natural arithmetic handling,
4. a proof using a generic cast/additive-form helper theorem.

Useful evaluation criteria include

- whether truncated `Nat.sub` is avoided safely,
- whether the `ℤ` / `ℕ` boundary remains visible to readers,
- whether arithmetic automation is proportionate,
- whether the proof preserves the meaning of the upstream theorem,
- whether the resulting API keeps the stable downstream form `B0 = A0 + ...`.

This is representative of a common issue in Lean number-theory formalization, so it also has good pedagogical value.

## PDF cross-check

The target branch contains the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed in this run.

However, the normal GitHub text fetch does not return binary PDF contents. Therefore, the exact page, section, and equation correspondence inside those PDFs is **not verified and is not guessed here**.

The technical content of this explanation is grounded in the actual declaration and surrounding dependencies in the latest `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is **0324 `GoldenZeroSectorInversionPacket`**.

Its kind is not `theorem` but **`structure`**.

```lean
structure GoldenZeroSectorInversionPacket where
  source : GoldenZeroSectorCandidate
  H_pos : 0 < goldenFifthSndFactor source.r source.s
  s_neg : source.s < 0
  c_pos : 0 < source.c
  d_pos : 0 < source.d
  ...
  factor_product :
    source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
  factor_difference :
    source.B0 = source.A0 + 8 * source.d ^ 5
  ...
```

It collects the positivity, coprimality, product, difference, and reconstruction facts that have so far lived as separate facts on the candidate into a certified packet consumed by downstream factorization.
# 0322 — `GoldenZeroSectorCandidate.A0_mul_B0`

## Declaration kind

This is a **`theorem`**.

For the positive natural representatives `A0` and `B0` constructed in 0316–0321, this theorem transports the zero-sector inversion product identity previously proved over `ℤ` into an equality over `ℕ`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Natural product identity inherited from the positive integer factors. -/
theorem A0_mul_B0 (p : GoldenZeroSectorCandidate) :
    p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5 := by
  have hprod := p.factor_product
  rw [← p.A0_cast, ← p.B0_cast] at hprod
  exact_mod_cast hprod
```

Its type is

```lean
p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5
```

and both sides live in `ℕ`.

Here

- `p.A0 : ℕ`,
- `p.B0 : ℕ`,
- `zeroSectorQ p.c : ℕ`.

Thus the conclusion has returned completely to natural-number arithmetic.

## Mathematical statement

Write the signed zero-sector inversion factors as

$$
A=\operatorname{zeroSectorA}(r,s,d),\qquad
B=\operatorname{zeroSectorB}(r,s,d).
$$

Upstream, one already has the integer identity

$$
AB=4Q^5,
$$

where

$$
Q=\operatorname{zeroSectorQ}(c).
$$

On the other hand, 0316–0319 introduced the natural representatives

$$
A_0=|A|,\qquad B_0=|B|
$$

and 0318 `A0_cast` together with 0319 `B0_cast` established

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B.
$$

Replacing `A` and `B` in the signed product identity by the integer casts of `A0` and `B0` gives

$$
(A_0:\mathbb Z)(B_0:\mathbb Z)=4(Q:\mathbb Z)^5.
$$

Since both sides arise from natural-number casts, the equality can be transported back to `ℕ`, yielding

$$
A_0B_0=4Q^5.
$$

The mathematical content is therefore not a new factorization theorem. It is the transport of a known integer factorization through the positivity-correct natural representatives, so that subsequent divisibility, coprimality, two-adic allocation, and fifth-power splitting can be carried out directly in `ℕ`.

## Role in the full proof

This theorem lies exactly on the boundary between the **signed integer phase** and the **natural factorization phase** of zero-sector inversion.

By this point the development has already established

$$
0<A<B,
$$

$$
AB=4Q^5,
$$

$$
B-A=8d^5
$$

over the signed factors.

Then 0316–0321 prepared

$$
A_0,B_0\in\mathbb N_{>0},
$$

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B.
$$

The present theorem is the first substantial payoff of that bridge: it converts the product equation to

$$
A_0B_0=4Q^5.
$$

This natural form is later stored as the `factor_product` field of `GoldenZeroSectorInversionPacket`. In the subsequent factorization module it is used directly in arguments excluding common odd prime divisors, allocating powers of two between the two factors, and splitting the remaining coprime parts into fifth powers.

In particular, later code can simply write expressions such as

```lean
rw [p.factor_product]
```

inside natural-number divisibility arguments. Removing `ℤ` from this API boundary is therefore structurally important.

## Direct dependencies

### `GoldenZeroSectorCandidate.factor_product`

This is the starting theorem of the proof.

```lean
have hprod := p.factor_product
```

retrieves the already-proved product identity for the signed integer factors.

Mathematically it corresponds to

$$
AB=4Q^5.
$$

The current standalone source confirms that this theorem is defined upstream of the present declaration; `A0_mul_B0` reuses it rather than reproving the factorization.

### `GoldenZeroSectorCandidate.A0_cast`

The theorem from 0318 gives

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

that is,

$$
(A_0:\mathbb Z)=A.
$$

The present proof rewrites this equality in the reverse direction, replacing `A` by `(p.A0 : ℤ)`.

### `GoldenZeroSectorCandidate.B0_cast`

The theorem from 0319 gives

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

that is,

$$
(B_0:\mathbb Z)=B.
$$

Again the rewrite is used in reverse.

### `zeroSectorQ`

This supplies the natural-number fifth-power base on the right-hand side. The present theorem does not unfold its definition; it keeps it as an opaque upstream API.

### `exact_mod_cast`

This Lean tactic transports the integer equality, after both factors have been rewritten as casts of natural numbers, back to the target equality in `ℕ`.

## Proof flow

1. Retrieve `p.factor_product` as the local hypothesis `hprod`.
2. Apply

   ```lean
   rw [← p.A0_cast, ← p.B0_cast] at hprod
   ```

   to replace the signed factors `A` and `B` by the integer casts `(A0 : ℤ)` and `(B0 : ℤ)`.
3. At this point `hprod` is essentially

   ```lean
   (p.A0 : ℤ) * (p.B0 : ℤ) = 4 * (zeroSectorQ p.c : ℤ) ^ 5
   ```

4. The target is

   ```lean
   p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5
   ```

   in `ℕ`.
5. `exact_mod_cast hprod` normalizes the casts and transports the integer equality back to the natural-number equality.

The script is only three lines long, but it is a significant type boundary in the overall FLT5 development.

## Lean-specific processing

### `have hprod := ...`

The proof does not restate the full type of the upstream theorem. Lean infers it and stores it as a local hypothesis that can be rewritten without modifying the original theorem.

### Reverse rewriting with `←`

The core line is

```lean
rw [← p.A0_cast, ← p.B0_cast] at hprod
```

The orientation of `A0_cast` is

```lean
(p.A0 : ℤ) = A
```

so a forward rewrite would replace `(p.A0 : ℤ)` by `A`. Here the desired direction is the opposite: the signed expression `A` must be turned back into the cast of the natural representative. Hence the reverse-arrow rewrite is essential.

The same applies to `B0_cast`.

### `exact_mod_cast`

Rather than manually normalizing every coercion between `ℕ` and `ℤ`, `exact_mod_cast` recognizes that the rewritten hypothesis and the goal are the same arithmetic equality across compatible casts.

Although products and fifth powers occur in the expression, the tactic is not proving new nonlinear arithmetic. It is transporting an already-established equality across the type boundary.

## Redundancy and duplication

There is very little redundancy in the current script:

```lean
have hprod := p.factor_product
rw [← p.A0_cast, ← p.B0_cast] at hprod
exact_mod_cast hprod
```

The three lines have a clear separation of responsibilities: retrieve, rewrite into casted representatives, then transport the type.

In principle, combinations of `simpa`, `norm_cast`, or more explicit cast lemmas might compress the script further. However, the current proof exposes the `ℕ`/`ℤ` boundary clearly, which is particularly valuable in a theorem-museum document.

Also note that `A0_pos` and `B0_pos` are not referenced directly in this proof. This is not accidental redundancy. Their positivity has already been consumed upstream when establishing `A0_cast` and `B0_cast`; at this stage the cast equalities themselves are the appropriate API.

## Optimization candidates

One comparison candidate is to avoid creating the local hypothesis `hprod` and use a more direct `simpa` or `norm_cast`-oriented proof.

Conceptually one might investigate forms based on

```lean
norm_cast
```

or a `simpa` that explicitly supplies the two cast equalities.

Another design possibility is a generic helper theorem transporting a product identity of positive integer representatives into naturals. However, `A0` and `B0` have specific semantic meaning in zero-sector inversion, and keeping a dedicated named theorem gives the downstream API a clearer vocabulary.

No Lean build is performed in this task, so these alternatives are **unverified candidates**.

The present `rw` + `exact_mod_cast` proof is already short and semantically transparent, so any optimization would likely be stylistic rather than substantial.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib-side machinery directly relevant to this theorem is chiefly

- `rw`,
- `exact_mod_cast`,
- coercions from `ℕ` to `ℤ`,
- cast normalization for multiplication and powers.

The project-side dependencies are

- `GoldenZeroSectorCandidate.factor_product`,
- `GoldenZeroSectorCandidate.A0_cast`,
- `GoldenZeroSectorCandidate.B0_cast`,
- `zeroSectorQ`.

This individual theorem could almost certainly live under narrower Mathlib imports than the global `Mathlib` import. Modules providing norm-cast / exact-mod-cast infrastructure and the algebraic `Nat`/`Int` cast machinery are the likely core.

However, the **exact minimal import set has not been verified**, because this task explicitly does not run a Lean build, and the full dependency closure of the upstream project declarations must also be taken into account.

## Comparator challenge suitability

**Yes. It is a small but good challenge for comparing Lean type-boundary techniques.**

Useful proof variants to compare would be

1. the current reverse `rw` + `exact_mod_cast` proof,
2. a `norm_cast`-centered proof,
3. a `simpa` proof with explicit cast lemmas,
4. a proof through a reusable generic transport helper.

The evaluation should not look only at line count. Better criteria are

- visibility of the `ℕ`/`ℤ` boundary,
- reuse of the existing API,
- degree of dependence on cast automation,
- quality of error localization when a type no longer matches,
- robustness under future definition changes.

The mathematics remains fixed while only the mechanism for transporting the same equality between types changes, which makes this particularly useful as a Lean learning exercise.

## Cross-check against the PDFs

The current branch repository tree was rechecked and contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the normal GitHub connector text fetch does not return binary PDF contents, and the available retrieval path in this run did not provide analyzable PDF text. Therefore the exact PDF page, section, and equation number corresponding to 0322 `A0_mul_B0` are **unverified**, and no location is guessed here.

The Lean code, declaration order, dependencies on `factor_product`, `A0_cast`, and `B0_cast`, and the immediately following `B0_eq_A0_add` were checked against the latest `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The generation header of the standalone source also confirms that this region belongs to the generated section corresponding to the ordered source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`.

## Next declaration to read

The next declaration is 0323 `GoldenZeroSectorCandidate.B0_eq_A0_add`, also a **`theorem`**.

The Lean source immediately continues with

```lean
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

Where 0322 transports the signed product identity into a natural product, 0323 transports the signed difference

$$
B-A=8d^5
$$

into the subtraction-free natural form

$$
B_0=A_0+8d^5.
$$

Together these give the product and difference identities needed by the natural factorization packet.

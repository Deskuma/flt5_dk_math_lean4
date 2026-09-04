# 0291 — `GoldenZeroSectorCandidate.product_neg`

## Declaration kind

This declaration is a **`theorem`**.

It extracts from the signed zero-sector product equation stored in `GoldenZeroSectorCandidate` the strict negativity of that product.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The signed product in every candidate is strictly negative. -/
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

Mathematically, for `p : GoldenZeroSectorCandidate`, the structure stores

$$
p.s\,H(p.r,p.s)=-5^6p.a^{10},
$$

where

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s),
$$

and also

$$
p.a>0.
$$

The theorem concludes

$$
p.s\,H(p.r,p.s)<0.
$$

## Mathematical meaning

0290 `GoldenZeroSectorCandidate` is the certificate passed from zero-sector arithmetic into the inversion layer. One of its fields is the signed exact product equation

$$
sH(r,s)=-5^6a^{10}.
$$

This theorem merely evaluates the sign of its right-hand side.

From `a_pos`,

$$
a>0,
$$

so for exponent ten,

$$
a^{10}>0.
$$

Also,

$$
-5^6<0.
$$

Therefore

$$
-5^6a^{10}<0,
$$

and `product_eq` transfers this to

$$
sH(r,s)<0.
$$

Thus the theorem does not introduce a new algebraic identity. It is a **projection theorem that converts a stored signed exact equation into order information**.

## Role in the whole proof

0288–0289 established the diagonalization and nonnegativity of the quartic factor:

$$
H(r,s)\ge 0.
$$

0290 then packaged all zero-sector candidate data into a structure.

0291 receives that structure and first fixes the sign of the total product:

$$
sH<0.
$$

This becomes decisive immediately in 0292 `GoldenZeroSectorCandidate.H_pos`. That theorem combines the 0289 fact

$$
H\ge 0
$$

with the present theorem

$$
sH<0
$$

to rule out $H=0$ and strengthen nonnegativity to

$$
H>0.
$$

A later theorem `s_neg` then combines positive $H$ with negative product to obtain

$$
s<0.
$$

Hence 0291 starts the sign-resolution chain

$$
\text{signed product equation}
\longrightarrow
sH<0
\longrightarrow
H>0
\longrightarrow
s<0.
$$

## Direct dependencies

### `GoldenZeroSectorCandidate`

The structure introduced in 0290. This theorem uses in particular the fields

```lean
product_eq :
  s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10

a_pos : 0 < a
```

`product_eq` provides the exact equation, while `a_pos` guarantees positivity of the tenth-power factor on the right.

### `goldenFifthSndFactor`

The second factor in the product,

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

### `pow_pos`

From `ha : 0 < (p.a : ℤ)` it gives

$$
0<(p.a:\mathbb Z)^{10}.
$$

### `mul_neg_of_neg_of_pos`

An order lemma stating that a negative number times a positive number is negative. Here it combines

$$
-(5:\mathbb Z)^6<0
$$

with

$$
(p.a:\mathbb Z)^{10}>0.
$$

### `exact_mod_cast`

The field `p.a_pos : 0 < p.a` is a proposition over natural numbers. This tactic transports it to the integer statement

$$
0<(p.a:\mathbb Z).
$$

### `norm_num`

It closes the fixed numerical inequality

$$
-(5:\mathbb Z)^6<0.
$$

## Proof flow

### 1. Rewrite with `product_eq`

```lean
rw [p.product_eq]
```

The goal

```lean
p.s * goldenFifthSndFactor p.r p.s < 0
```

becomes

```lean
-(5 : ℤ) ^ 6 * (p.a : ℤ) ^ 10 < 0
```

At this point the zero-sector-specific algebra has disappeared behind the structure field, leaving only an integer sign computation.

### 2. Cast positivity of `a` to integers

```lean
have ha : (0 : ℤ) < p.a := by
  exact_mod_cast p.a_pos
```

Since the field `p.a` has type `ℕ`, its positivity is moved to `ℤ` so that `pow_pos` applies to the integer factor occurring in `product_eq`.

### 3. Conclude negative times positive

```lean
exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

`norm_num` proves the first factor negative, `pow_pos ha 10` proves the second factor positive, and `mul_neg_of_neg_of_pos` returns strict negativity of the product.

## Lean-specific processing

The main Lean-specific point is the **coercion boundary from `ℕ` to `ℤ`**.

The structure stores `a : ℕ`, whereas `product_eq` is an integer equation and therefore contains `(a : ℤ)`. Consequently `p.a_pos : 0 < p.a` cannot simply be reused as an integer positivity proof. The proof explicitly inserts

```lean
have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
```

as the bridge.

The proof also uses the projection `p.product_eq` directly as a rewrite rule. This illustrates the advantage of the flat structure introduced in 0290: the long original hypothesis list does not need to be passed again.

No `ring` or `nlinarith` is required. The proof needs only exact rewriting, a cast, fixed numerical evaluation, and an order lemma.

## Redundancy and duplication

The proof is already very short and contains essentially no obvious redundancy.

In principle, the local name `ha` could be avoided by constructing the cast proof inline inside `pow_pos`, but

```lean
have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
```

makes the type boundary explicit and is pedagogically clearer.

Likewise, extracting the fixed fact $-5^6<0$ into a separate lemma would provide little value because `norm_num` handles it immediately.

## Optimization candidates

### 1. A local cast helper

If later theorems repeatedly cast positivity facts such as `p.a_pos`, `p.c_pos`, and `p.d_pos` from `ℕ` to `ℤ`, a small helper lemma could reduce repetition.

For this theorem alone, however, one `exact_mod_cast` line is simpler than introducing an abstraction.

### 2. Alternative proof with `simpa`

One could first prove negativity of the right-hand side in a separate `have`, then conclude with something like `simpa [p.product_eq]`. The current `rw` style is more direct because it immediately transforms the proof state into the arithmetic goal.

### 3. Keep the named theorem as API

Logically, later theorems could re-derive negativity directly from `p.product_eq` every time. Giving it the name `product_neg`, however, hides the concrete expression $-5^6a^{10}$ and exposes only the order fact needed downstream. This is a useful API boundary, so eliminating the theorem would make the later proof structure less clear.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main facilities directly used by this theorem are

- coercions between `ℕ` and `ℤ`,
- `pow_pos` in an ordered ring,
- `mul_neg_of_neg_of_pos`,
- `exact_mod_cast`,
- `norm_num`,
- the existing structure `GoldenZeroSectorCandidate`,
- the existing definition `goldenFifthSndFactor`.

The theorem itself does not require `ring`, `omega`, `positivity`, or `nlinarith`.

This task does not run a Lean build, so the exact minimal import set for the original module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` is **not verified**. No specific replacement for `import Mathlib` is asserted without verification.

## Suitability for a Comparator challenge

**Suitable.**

It is a short theorem, but it combines several useful Lean skills:

1. use the structure projection `p.product_eq`,
2. transport positivity from `ℕ` to `ℤ`,
3. prove positivity of a power,
4. close with a negative-times-positive order lemma.

A natural challenge is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  ...
```

with `product_eq` and `a_pos` available through `p`.

Its difficulty is low, but solutions using `exact_mod_cast` can be compared with solutions using more explicit coercion lemmas, so it works well as a compact Comparator exercise.

Verdict: **suitable**.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The normal GitHub text retrieval path and the direct PDF fetch attempted in this run did not provide the binary PDF bodies in an analyzable form. Therefore the exact PDF page, section, and wording corresponding to this theorem are **unverified**, and no location is guessed.

The technical account here is grounded primarily in `Flt5DkMath/FLT5StandAlone.lean` on the target branch and in the immediately preceding theorem-museum documents.

## Next declaration to read

The next declaration is 0292 `GoldenZeroSectorCandidate.H_pos`, also a **`theorem`**.

In the canonical source it immediately follows this theorem and combines 0289 `goldenFifthSndFactor_nonneg` with 0291 `product_neg` to prove

$$
0<goldenFifthSndFactor\ p.r\ p.s.
$$

Thus 0291 fixes negativity of the whole product, and 0292 strengthens nonnegativity of the quartic factor to strict positivity.

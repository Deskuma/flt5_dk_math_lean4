# 0313 — `GoldenZeroSectorCandidate.B_pos`

## Declaration kind

This is a **`theorem`**.

0312 `GoldenZeroSectorCandidate.W_pos` established

$$
W>0.
$$

Together with 0305 `GoldenZeroSectorCandidate.U_nonneg`, which gives

$$
U\ge0,
$$

this theorem proves that the upper inversion factor

$$
B=U+W
$$

is strictly positive.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The upper inversion factor is strictly positive. -/
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

The conclusion is strict positivity in `ℤ`:

$$
0<B.
$$

`zeroSectorB` is defined by

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

that is,

$$
B(r,s,d)=U(r,s)+W(d).
$$

## Mathematical meaning

The preceding results already give

$$
U\ge0,
\qquad
W>0.
$$

Therefore monotonicity immediately yields

$$
U+W>0,
$$

and hence

$$
B>0.
$$

This theorem introduces no new number-theoretic identity. Instead, it attaches order information to the inversion coordinates constructed earlier.

## Role in the full proof

0309 established

$$
AB=4Q^5,
$$

0310 established

$$
B-A=8d^5,
$$

and 0311 established

$$
A+B=2U.
$$

Those product, difference, and sum identities alone do not automatically determine the signs of the integer factors `A` and `B`.

0312 supplied `W>0`, and the present theorem establishes `B>0`. The immediately following 0314 `GoldenZeroSectorCandidate.A_pos` uses the positive product

$$
AB=20s^4>0
$$

together with this theorem's `B>0` to derive `A>0`.

Thus 0313 is the middle link in the positivity chain needed before the integer inversion factors can be transported to natural-number data later in the proof.

## Direct dependencies

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

The opening `unfold zeroSectorB` turns the goal into positivity of `U+W`.

### `GoldenZeroSectorCandidate.U_nonneg`

0305 proves

```lean
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  positivity
```

and supplies

$$
U\ge0.
$$

### `GoldenZeroSectorCandidate.W_pos`

0312 supplies

$$
W>0.
$$

This is the strict inequality that makes the sum strictly positive.

### `linarith`

`linarith` closes the linear arithmetic implication from `U≥0` and `W>0` to `U+W>0`.

## Proof flow

1. `unfold zeroSectorB` expands the target to

$$
0<U+W.
$$
2. `p.U_nonneg` provides

$$
0\le U.
$$
3. `p.W_pos` provides

$$
0<W.
$$
4. `linarith` combines the two inequalities and closes `0<U+W`.

## Lean-specific handling

Mathematically, the proof is simply “a nonnegative number plus a positive number is positive.” The current Lean proof delegates this elementary order argument to `linarith` rather than invoking a dedicated order lemma directly.

Unlike 0312, this theorem contains no explicit `ℕ`/`ℤ` cast. The conversion of `d : ℕ` into the integer-valued coordinate `W` has already been handled inside `W_pos`, so here both `zeroSectorU ... : ℤ` and `zeroSectorW ... : ℤ` live in the same ordered ring.

No `ring`, `nlinarith`, or `omega` is needed.

## Redundancy and duplication

The proof is only two lines:

```lean
unfold zeroSectorB
linarith [p.U_nonneg, p.W_pos]
```

so there is essentially no local redundancy.

However, its mathematical content is exactly the general order fact

$$
0\le U,\quad 0<W \Longrightarrow 0<U+W.
$$

For such a simple goal, `linarith` is a more general and heavier tactic than strictly necessary. This is not incorrect, but there is room to make the dependency structure more explicit.

## Optimization candidates

A more structural proof could be of the form

```lean
unfold zeroSectorB
exact add_pos_of_nonneg_of_pos p.U_nonneg p.W_pos
```

or use `simpa [zeroSectorB]` together with the corresponding order lemma.

Such a proof would remove the dependency on `linarith` and state directly that the result follows from “nonnegative + positive = positive.”

Because this run is explicitly not allowed to perform a Lean build, whether the exact current Mathlib lemma name and argument order make the snippet compile unchanged is **not verified**. It is therefore recorded only as an optimization candidate.

## Required Mathlib imports and import-minimization candidates

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

The present proof directly needs at least:

- ordered additive arithmetic on `ℤ`,
- `linarith`,
- the project definitions and lemmas `zeroSectorB`, `U_nonneg`, and `W_pos`.

This theorem does not directly use `ring`, `positivity`, or `exact_mod_cast`.

If the proof is replaced by a dedicated order lemma, the direct `linarith` dependency can likely be removed as well, which would make import minimization easier. The exact minimal import set has **not been verified**, because Lean builds are prohibited for this task.

## Comparator challenge suitability

**Suitable. Difficulty: beginner.**

A challenge can ask for the clearest Lean proof that known facts

$$
U\ge0,
\qquad
W>0
$$

imply

$$
B=U+W>0.
$$

Useful comparison points include:

- the current `linarith` proof,
- a direct proof with an order lemma such as `add_pos_of_nonneg_of_pos`,
- a shortened `simpa [zeroSectorB]` form,
- the trade-off between tactic automation, dependency transparency, and import size.

The mathematics is elementary, but it makes a useful small Lean proof-engineering comparator.

## PDF cross-check

The target branch contains the existing bilingual PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the normal GitHub connector text fetch does not return the contents of binary PDF files. Therefore this run has **not** directly matched this declaration to a specific PDF page, section, or equation number, and no such location is inferred.

The Lean code, declaration order, direct dependencies, and relationship to the following declaration were checked against the repository canonical source `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0314 `GoldenZeroSectorCandidate.A_pos`, also a **`theorem`**.

The canonical Lean source continues with

```lean
/-- The lower inversion factor is strictly positive. -/
theorem A_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorA p.r p.s p.d := by
  have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
  have hprod : 0 <
      zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d := by
    rw [p.factor_product_twenty]
    positivity
  exact (mul_pos_iff.mp hprod).resolve_right (by
    exact not_and_of_not_left _ (not_lt_of_ge (le_of_lt p.B_pos)))
```

Using 0313's

$$
B>0
$$

as the sign anchor, it combines the positive product `AB>0` with `B>0` to determine

$$
A>0.
$$
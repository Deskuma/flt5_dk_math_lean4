# 0312 — `GoldenZeroSectorCandidate.W_pos`

## Declaration kind

This declaration is a **`theorem`**.

By 0311, the exact product, difference, and sum identities for the inversion factors `A`,`B` have been established. This theorem begins the order/positivity phase by proving

$$
W=4d^5>0.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The tenth-power square root contribution is strictly positive. -/
theorem W_pos (p : GoldenZeroSectorCandidate) : 0 < zeroSectorW p.d := by
  unfold zeroSectorW
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
```

The conclusion is a strict inequality over `ℤ`:

$$
0 < W(d).
$$

The definition of `zeroSectorW` is

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

so

$$
W(d)=4d^5.
$$

## Mathematical meaning

`GoldenZeroSectorCandidate` stores the hypothesis `d_pos : 0 < d`. After coercing to integers, this gives

$$
0<d.
$$

Since the exponent `5` is positive,

$$
d^5>0,
$$

and the coefficient `4` is also positive, hence

$$
4d^5>0.
$$

Therefore

$$
W>0.
$$

This theorem does not add new number-theoretic content. It transports the already stored positivity of `d` to the inversion coordinate `W`.

## Role in the whole proof

`W` is the half-difference coordinate in

$$
A=U-W,
\qquad
B=U+W.
$$

In 0310 it already appeared through

$$
B-A=2W=8d^5.
$$

Once `W>0` is known, it can be combined with `U\ge0` to obtain

$$
B=U+W>0.
$$

The next theorem in the Lean source, 0313 `GoldenZeroSectorCandidate.B_pos`, uses this theorem directly:

```lean
unfold zeroSectorB
linarith [p.U_nonneg, p.W_pos]
```

Thus 0312 is the first order bridge connecting the exact algebraic phase to the positivity phase for the two inversion factors.

## Direct dependencies

### `GoldenZeroSectorCandidate.d_pos`

The candidate stores

```lean
d_pos : 0 < d
```

This is the only candidate-specific hypothesis used by the proof.

### `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

The theorem unfolds this definition and transfers positivity of the natural number `d` to positivity of the integer expression `4 * (d : ℤ)^5`.

### `exact_mod_cast`

The hypothesis `p.d_pos : 0 < p.d` is a natural-number inequality, while `zeroSectorW` uses `(p.d : ℤ)`. Therefore the proof crosses the type boundary via

```lean
have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
```

### `positivity`

Using `hd`, the tactic closes

$$
0<4(d:ℤ)^5.
$$

## Proof / construction flow

1. `unfold zeroSectorW` changes the goal to

$$
0 < 4 * (p.d : ℤ)^5.
$$

2. `exact_mod_cast` transports `p.d_pos : 0 < p.d` to

$$
0 < (p.d : ℤ).
$$

3. `positivity` recognizes the positive power of a positive base and multiplication by the positive coefficient `4`.
4. The goal `0 < zeroSectorW p.d` is closed.

## Lean-specific processing

Mathematically, the implication from `d>0` to `4d^5>0` is immediate. In Lean, however, `d : ℕ` while `zeroSectorW d : ℤ`, so the coercion boundary must be handled explicitly. This makes `exact_mod_cast` the main Lean-specific step of the proof.

The proof then delegates positivity of powers and products to `positivity` rather than chaining explicit uses of lemmas such as `pow_pos` and `mul_pos`.

No `linarith` or `nlinarith` is needed here, and the goal is not a ring identity, so `ring` is also unnecessary.

## Redundancy and overlap

The proof is only three lines long and has essentially no local redundancy.

Several following lemmas establish positivity of related coordinates, so natural-to-integer positivity transport may recur in the surrounding development. In this theorem, however, that transport occurs only once, and there is not enough evidence here alone to justify a dedicated helper solely for reducing repetition.

## Optimization candidates

It may be possible to avoid the explicit local hypothesis `hd` if `positivity` can consume the cast of `p.d_pos` directly, but this is unverified because Lean builds are forbidden in this task.

A more reusable refactoring would be to introduce a candidate-independent theorem such as

```lean
theorem zeroSectorW_pos {d : ℕ} (hd : 0 < d) : 0 < zeroSectorW d := ...
```

and then make `GoldenZeroSectorCandidate.W_pos` a thin wrapper. Since the present theorem uses only the field `d_pos`, this abstraction would be mathematically natural if the result is reused elsewhere.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

This theorem directly needs at least:

- coercions between `ℕ` and `ℤ`;
- strict order;
- integer powers and multiplication;
- `exact_mod_cast`;
- `positivity`.

The proof does not directly use `ring`, `omega`, `linarith`, or `nlinarith`.

It is therefore very likely that the import can be narrowed substantially from all of `Mathlib`. The exact minimal import set is unverified because this task forbids Lean builds.

## Comparator challenge suitability

**Suitable. Difficulty: beginner to lower-intermediate.**

The mathematics is simple, but the useful comparison point is Lean's type-boundary handling.

Possible proof strategies include:

- the current `exact_mod_cast` + `positivity` proof;
- using an explicit cast lemma such as an integer positivity lemma for naturals;
- constructing the argument manually from `pow_pos` and `mul_pos`;
- extracting a candidate-independent `zeroSectorW_pos` lemma and making this theorem a wrapper.

A good comparator test is whether the solver notices that `d_pos : 0 < d` lives in `ℕ` while the target inequality lives in `ℤ`.

## Cross-check with the PDFs

The target branch contains the existing bilingual PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`;
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

Their presence was confirmed in the repository. However, the GitHub connector's normal text fetch does not return binary PDF contents, so this run could not directly verify the exact page, section, or equation corresponding to this declaration. No such location is guessed here.

The Lean code, declaration order, direct dependencies, and relation to the subsequent theorem were checked against the repository source of truth, `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0313 `GoldenZeroSectorCandidate.B_pos`, again a **`theorem`**.

The Lean source continues with

```lean
/-- The upper inversion factor is strictly positive. -/
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

Thus 0313 combines `W>0` from the present theorem with `U\ge0` from 0305 to obtain

$$
B=U+W>0.
$$

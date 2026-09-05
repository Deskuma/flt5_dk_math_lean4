# 0311 — `GoldenZeroSectorCandidate.factor_sum`

## Declaration kind

This declaration is a **`theorem`**.

While 0310 `GoldenZeroSectorCandidate.factor_difference` fixes the difference of the inversion factors,

$$
B-A=8d^5,
$$

this theorem fixes their exact sum,

$$
A+B=2U.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sum of the two inversion factors. -/
theorem factor_sum (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d + zeroSectorB p.r p.s p.d =
      2 * zeroSectorU p.r p.s := by
  unfold zeroSectorA zeroSectorB
  ring
```

The conclusion is an equality over `ℤ`:

$$
A(r,s,d)+B(r,s,d)=2U(r,s).
$$

Here

$$
A=U-W,
\qquad
B=U+W.
$$

## Mathematical meaning

Substituting the definitions gives

$$
A+B=(U-W)+(U+W).
$$

The two `W` terms cancel, hence

$$
A+B=2U.
$$

Therefore this theorem does not introduce a new number-theoretic constraint. It extracts, as an exact equality, the symmetry already encoded in the definitions of `A` and `B`: the two inversion factors are placed symmetrically around `U`.

Together with 0310,

$$
B-A=2W=8d^5,
$$

this identifies `U` as the midpoint and `W` as the half-difference of the two factors:

$$
U=\frac{A+B}{2},
\qquad
W=\frac{B-A}{2}.
$$

The Lean theorem deliberately avoids division and keeps the integer-safe form `A+B=2U`.

## Role in the whole proof

The zero-sector inversion has already produced the multiplicative constraint

$$
AB=4Q^5
$$

in 0309 and the additive difference constraint

$$
B-A=8d^5
$$

in 0310. The present theorem adds the exact sum constraint

$$
A+B=2U.
$$

Thus the inversion factors `A` and `B` are tied back to the original diagonal coordinate `U` and fifth-power coordinate `W` not only through their product but also through their difference and sum.

The immediately following positivity proofs do not need to invoke this theorem directly, but `factor_sum` makes the symmetric structure of `A` and `B` explicit in the public API. In particular, later arguments can recover `U` from the two factors without unfolding the definitions `A=U-W` and `B=U+W` every time.

In this sense the theorem is a reconstruction API for the inversion construction. This parallels 0306 `square_reconstruction`, which retained the original square coordinate inside `U`; here the pair `A,B` retains the coordinate `U`.

## Direct dependencies

### `zeroSectorA`

The lower inversion factor is defined by

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

that is,

$$
A=U-W.
$$

### `zeroSectorB`

The upper inversion factor is defined by

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

that is,

$$
B=U+W.
$$

### `zeroSectorU`

This is the diagonal coordinate that remains on the right-hand side. It is an integer-valued expression built from `r,s` by an earlier definition. The proof of `factor_sum` does not need to unfold its internal polynomial form.

### `ring`

After unfolding `zeroSectorA` and `zeroSectorB`, the remaining goal is the commutative-ring identity

$$
(U-W)+(U+W)=2U,
$$

which `ring` normalizes and closes.

## Proof / construction flow

1. `unfold zeroSectorA zeroSectorB` expands only the two inversion-factor definitions.
2. The left-hand side becomes

$$
(U-W)+(U+W).
$$

3. `ring` cancels the `W` terms and normalizes the coefficients.
4. The result is exactly

$$
2U.
$$

Neither the internal definition of `zeroSectorU` nor that of `zeroSectorW` is unfolded. Consequently, the theorem depends only on the symmetric definitions `A=U-W` and `B=U+W`, not on the concrete polynomial formulas for `U` and `W`.

## Lean-specific processing

The conclusion lives in `ℤ`, which naturally accommodates the subtraction inside `zeroSectorA`. Although `p.d : ℕ` is cast to `ℤ` inside `zeroSectorW`, that definition is not unfolded in this proof, so no cast manipulation is visible here.

Accordingly, `push_cast`, `exact_mod_cast`, and `norm_cast` are unnecessary. There are no inequalities either, so `omega`, `linarith`, `nlinarith`, and `positivity` are also unnecessary.

The goal presented to `ring` is a pure commutative-ring identity. In this theorem, `ring` communicates the proof intent more clearly than heavier automation.

No hypothesis field of `GoldenZeroSectorCandidate` is used. The candidate `p` serves only as a container from which `r`, `s`, and `d` are projected. This is the same structural feature seen in 0310 `factor_difference`.

## Redundancy and overlap

The proof itself,

```lean
unfold zeroSectorA zeroSectorB
ring
```

is already essentially minimal.

There is structural overlap between 0310 and 0311 because they encode the paired identities

$$
(U+W)-(U-W)=2W,
$$

and

$$
(U-W)+(U+W)=2U.
$$

Nevertheless, the two theorems play clearly different mathematical roles—difference versus sum—so keeping both as separate API lemmas is justified.

## Optimization candidates

Because no candidate-specific hypothesis is used, one possible refactoring is to introduce a candidate-independent lemma of the form

```lean
zeroSectorA r s d + zeroSectorB r s d = 2 * zeroSectorU r s
```

in a more general namespace and make the present theorem a thin wrapper.

A paired general API for both `factor_difference` and `factor_sum` could make the elementary arithmetic laws of `zeroSectorA/B` easier to reuse.

However, the current proof is already only two lines long, so the value of additional abstraction depends on future reuse. Because Lean builds are forbidden in this task, it has not been verified whether an even shorter proof such as `simp [zeroSectorA, zeroSectorB]` closes the goal, nor has the exact minimum import set been tested.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

The present theorem directly needs at least:

- integer addition, subtraction, and multiplication;
- `zeroSectorA`;
- `zeroSectorB`;
- `zeroSectorU`;
- `unfold`;
- the `ring` tactic.

The proof does not directly use `omega`, `linarith`, `nlinarith`, `positivity`, `push_cast`, or `exact_mod_cast`.

It is therefore very likely that the import can be narrowed from all of `Mathlib` to the basic integer algebra and ring-tactic modules. The exact minimal import set is unverified because this task explicitly forbids Lean builds, so this remains an optimization hypothesis rather than a confirmed result.

## Comparator challenge suitability

**Suitable. Difficulty: beginner.**

After unfolding the definitions, the theorem is a very small ring identity, so it is better suited to comparing proof engineering than to difficult proof search.

Useful comparison axes include:

- the current `unfold zeroSectorA zeroSectorB; ring` proof;
- a simplification-based proof such as `simp [zeroSectorA, zeroSectorB]` if it works;
- introducing a candidate-independent general lemma and proving this theorem as a wrapper;
- recognizing the symmetry with 0310 `factor_difference`.

A particularly good evaluation point is whether a solver notices that the internal definitions of `zeroSectorU` and `zeroSectorW` do not need to be unfolded.

## Cross-check with the PDFs

The target branch contains the existing bilingual PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

Their presence was confirmed in the repository. However, the GitHub connector's normal text fetch does not return the contents of binary PDF files, so this run could not directly verify the exact PDF page, section, or equation corresponding to this declaration. No such location is guessed here.

The Lean code, declaration order, direct dependencies, and relation to subsequent declarations were checked against the repository source of truth, `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0312 `GoldenZeroSectorCandidate.W_pos`, again a **`theorem`**.

The Lean source continues with

```lean
/-- The tenth-power square root contribution is strictly positive. -/
theorem W_pos (p : GoldenZeroSectorCandidate) : 0 < zeroSectorW p.d := by
  unfold zeroSectorW
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
```

Thus, after 0311 completes the exact algebraic product/difference/sum information for `A` and `B`, 0312 begins the order/positivity phase: `W>0`, followed by positivity of `B`, positivity of `A`, and finally `A<B`.
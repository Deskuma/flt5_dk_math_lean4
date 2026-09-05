# 0314 — `GoldenZeroSectorCandidate.A_pos`

## Declaration kind

This is a **`theorem`**.

0313 `GoldenZeroSectorCandidate.B_pos` established strict positivity of the upper inversion factor,

$$
B>0.
$$

This theorem combines the product identity from 0308 `factor_product_twenty`,

$$
AB=20s^4,
$$

with the candidate hypothesis $s<0$ to prove that the product is strictly positive, and then uses `B>0` as a sign anchor to conclude that the lower factor satisfies

$$
A>0.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The lower inversion factor is strictly positive. -/
theorem A_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorA p.r p.s p.d := by
  have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
  have hprod : 0 <
      zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d := by
    rw [p.factor_product_twenty]
    positivity
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.1
  · exact (not_lt_of_ge p.B_pos.le h.2).elim
```

The conclusion is strict positivity over `ℤ`:

$$
0<A.
$$

The factor definitions are

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

## Mathematical meaning

From 0308 we have

$$
AB=20s^4.
$$

The candidate carries $s<0$, hence $s\ne0$, and therefore

$$
s^4>0,
\qquad
20s^4>0.
$$

Thus

$$
AB>0.
$$

A positive product over the integers means that the two factors have the same sign:

$$
(A>0\land B>0)
\quad\text{or}\quad
(A<0\land B<0).
$$

But 0313 has already proved $B>0$, so the second alternative is impossible. Therefore

$$
A>0.
$$

## Role in the overall proof

0309–0311 establish exact identities for the product, difference, and sum of the inversion factors. 0312–0314 then determine their signs.

This theorem supplies the remaining positivity statement needed to move toward

$$
0<A<B.
$$

The next theorem, 0315 `GoldenZeroSectorCandidate.A_lt_B`, uses 0310 `factor_difference` together with $d>0$ to prove $A<B$.

Thus 0314 is the final positivity gate before the integer factorization is converted into strictly positive natural-number data downstream.

## Direct dependencies

### `GoldenZeroSectorCandidate.s_neg`

The candidate hypothesis

$$
s<0
$$

yields

```lean
have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
```

This nonzeroness is available to `positivity` when proving strict positivity of $s^4$.

### `GoldenZeroSectorCandidate.factor_product_twenty`

0308 provides

```lean
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4
```

and the proof rewrites the product using this theorem.

### `GoldenZeroSectorCandidate.B_pos`

0313 established

$$
B>0.
$$

It is used to eliminate the negative-negative branch produced by `mul_pos_iff`.

### `mul_pos_iff`

From positivity of the product, this yields

$$
(A>0\land B>0)\lor(A<0\land B<0).
$$

## Proof flow

1. Derive `hsne : p.s ≠ 0` from `p.s_neg`.
2. Rewrite $AB$ as $20s^4$ using `p.factor_product_twenty`.
3. Use `positivity` to prove $20s^4>0`, hence $AB>0$.
4. Split `mul_pos_iff.mp hprod` into the two possible common-sign cases.
5. In the positive-positive branch, `h.1` is exactly the desired $A>0$.
6. In the negative-negative branch, `h.2 : B < 0` contradicts `p.B_pos.le : 0 ≤ B`, so the branch is eliminated.

## Lean-specific processing

The local fact `hsne` does not appear explicitly in the final proof term after its declaration, but it is available to the `positivity` tactic, which can use it to establish strict positivity of the even power $s^4$.

```lean
rcases mul_pos_iff.mp hprod with h | h
```

is the Lean step that exposes the two sign configurations compatible with a positive product.

In the negative-negative branch,

```lean
(not_lt_of_ge p.B_pos.le h.2).elim
```

first weakens `B>0` to `0≤B` via `.le`, then contradicts `h.2 : B<0`.

## Redundancy and overlap

The proof is short and its logical structure is explicit. The only potential simplification is that it expands the positive-product argument into the two cases supplied by `mul_pos_iff` and then eliminates one case. If Mathlib provides a direct lemma saying that a positive product together with positivity of one factor forces positivity of the other, that could shorten the proof.

The theorem intentionally uses 0308 `factor_product_twenty` rather than the normalized fifth-power product from 0309. This is natural here because the candidate hypothesis $s\ne0$ makes strict positivity of $20s^4$ immediate.

## Optimization candidates

A possible optimization is to replace the explicit `mul_pos_iff` case split with a dedicated ordered-ring lemma deriving $A>0$ directly from $AB>0$ and $B>0$, if an appropriate Mathlib lemma is available.

Another possibility is to replace `positivity` with an explicit chain using a power-positivity lemma after deriving $s\ne0$, but that would likely be less concise.

These alternatives are **unverified optimization candidates** because this run does not perform a Lean build.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

This theorem directly relies on at least:

- the ordered-ring structure of `ℤ`,
- `ne_of_lt`,
- `positivity`,
- `mul_pos_iff`,
- `not_lt_of_ge`,
- the project lemmas `factor_product_twenty` and `B_pos`.

The theorem itself does not directly use `ring`, `linarith`, `omega`, or `exact_mod_cast`.

A smaller import set is likely possible, but the exact minimal imports have not been checked because Lean build verification is excluded in this task.

## Comparator challenge suitability

**Suitable. Difficulty: beginner to intermediate.**

A comparator challenge can ask for alternative Lean proofs of

$$
AB>0,
\qquad
B>0
$$

implying

$$
A>0.
$$

Useful comparison axes include:

- the current `mul_pos_iff` sign-case proof,
- a direct ordered-ring lemma, if available,
- how much work is delegated to `positivity`,
- whether to expose or hide the sign-analysis logic,
- proof brevity versus auditability.

## Comparison with the PDFs

The target branch contains the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed in the repository.

However, the normal GitHub text fetch does not return binary PDF contents, so this run cannot directly verify the exact page, section, or equation number corresponding to this theorem. No such location is guessed here.

The Lean code, declaration order, direct dependencies, and relationship to following declarations were checked against `Flt5DkMath/FLT5StandAlone.lean` as the canonical repository source.

## Next declaration to read

The next declaration is 0315 `GoldenZeroSectorCandidate.A_lt_B`, and its kind is **`theorem`**.

The canonical Lean source continues with

```lean
/-- The two factors occur in their forced strict order. -/
theorem A_lt_B (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d < zeroSectorB p.r p.s p.d := by
  have hdiff := p.factor_difference
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
  linarith
```

It combines 0310's

$$
B-A=8d^5
$$

with $d>0$ to show that the difference is strictly positive and therefore

$$
A<B.
$$
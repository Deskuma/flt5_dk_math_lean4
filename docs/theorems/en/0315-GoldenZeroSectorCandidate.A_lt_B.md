# 0315 — `GoldenZeroSectorCandidate.A_lt_B`

## Declaration kind

This declaration is a **`theorem`**.

In 0312–0314, strict positivity of the inversion factors was established:

$$
0 < A,\qquad 0 < B.
$$

This theorem uses the exact difference from 0310 `GoldenZeroSectorCandidate.factor_difference`,

$$
B-A=8d^5,
$$

together with the candidate hypothesis $d>0$ to force the strict order

$$
A<B.
$$

At this point one has

$$
0<A<B,
$$

and the development can move from integer factors $A,B$ to their positive natural representatives `A0`, `B0`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The two factors occur in their forced strict order. -/
theorem A_lt_B (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d < zeroSectorB p.r p.s p.d := by
  have hdiff := p.factor_difference
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
  linarith
```

The conclusion is a strict order statement in `ℤ`:

$$
A<B.
$$

Here

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

## Mathematical meaning

From 0310 `factor_difference`,

$$
B-A=8d^5.
$$

The candidate carries

$$
d>0.
$$

After coercion to the integers,

$$
0<(d:ℤ).
$$

Therefore

$$
0<d^5,
$$

and hence

$$
0<8d^5.
$$

Thus

$$
0<B-A,
$$

which is exactly

$$
A<B.
$$

From the definitions

$$
A=U-W,\qquad B=U+W,
$$

this order could also be viewed as a direct consequence of $W>0$. The current proof instead reuses the already exposed exact API theorem `factor_difference`.

## Role in the overall proof

In 0309–0311, the exact algebraic data of the inversion factors were established:

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U.
$$

In 0312–0314, their signs were fixed:

$$
W>0,\qquad B>0,\qquad A>0.
$$

The present theorem adds

$$
A<B,
$$

thereby turning the signed integer factorization into a positive ordered factorization.

Immediately afterward the source introduces

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs

def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

Because `A_pos`, `B_pos`, and `A_lt_B` are already available, these are not merely absolute values: they can be used as positive ordered natural representatives.

Thus 0315 is the **order gate immediately before the transition from integer inversion factors to natural-number factors**.

## Direct dependencies

### `GoldenZeroSectorCandidate.factor_difference`

The theorem from 0310 is

```lean
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5
```

and is brought into the local context by

```lean
have hdiff := p.factor_difference
```

### `GoldenZeroSectorCandidate.d_pos`

The candidate stores positivity of the natural number $d$:

$$
0<d.
$$

Since the target arithmetic is in `ℤ`, the proof transports it with

```lean
have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
```

### `pow_pos`

From `hd : 0 < (p.d : ℤ)`, the proof obtains

```lean
have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
```

that is, $d^5>0$.

### `linarith`

Finally, `linarith` combines `hdiff` and `hpow` to conclude $A<B$.

## Proof flow

1. Retrieve `p.factor_difference` as `hdiff`, giving $B-A=8d^5$.
2. Coerce `p.d_pos : 0 < p.d` from `ℕ` to `ℤ` with `exact_mod_cast`.
3. Use `pow_pos hd 5` to prove $d^5>0$.
4. Let `linarith` combine the exact difference with that positivity and derive $A<B$.

## Lean-specific processing

### Transport from `ℕ` to `ℤ`

`p.d` is a natural number, but `zeroSectorA`, `zeroSectorB`, and `factor_difference` live in integer arithmetic. The line

```lean
exact_mod_cast p.d_pos
```

performs the formal transport across

$$
\mathbb N\hookrightarrow\mathbb Z.
$$

Mathematically this is routine, but Lean requires the type boundary to be handled explicitly.

### Isolating the nonlinear fact before `linarith`

`linarith` is not responsible for discovering positivity of arbitrary powers. The proof therefore first establishes

```lean
have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
```

and only then passes the resulting positive quantity into linear arithmetic.

This is a clean separation of tactic responsibilities.

## Redundancy and duplication

Mathematically one could unfold

$$
A=U-W,\qquad B=U+W
$$

and derive $A<B$ directly from `W_pos`.

However, because 0310 already exposes the exact difference as a public theorem, reusing `factor_difference` keeps the factor API coherent. This is therefore not meaningful duplication.

The local facts `hd` and `hpow` could perhaps be compressed with `positivity` or a different order lemma, but the current structure is explicit and easy to audit.

## Optimization candidates

One possible alternative is to combine `factor_difference` with a separately proved positivity of its right-hand side using `positivity`, conceptually:

```lean
have hdiff := p.factor_difference
have : 0 < (8 : ℤ) * (p.d : ℤ) ^ 5 := by
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
linarith
```

Another alternative would unfold `A` and `B` and prove the inequality directly from `W_pos`. That may shorten the local proof, but it bypasses the already established `factor_difference` API, so proof length should be weighed against architectural consistency.

The current unannotated

```lean
have hdiff := p.factor_difference
```

is already readable; adding a fully explicit type would likely add noise rather than value.

These alternatives are **unverified optimization candidates**, because no Lean build is performed in this run.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main features used directly by this theorem are:

- the linear ordered ring structure on `ℤ`,
- `exact_mod_cast`,
- `pow_pos`,
- `linarith`,
- the project theorem `GoldenZeroSectorCandidate.factor_difference`,
- the project field/theorem `GoldenZeroSectorCandidate.d_pos`.

This theorem does not directly use `ring`, `omega`, `norm_num`, or `positivity`.

A narrower Mathlib import is probably possible, but the exact minimal import set is not verified because Lean builds are excluded from this task.

## Comparator challenge suitability

**Yes. Difficulty: beginner to intermediate.**

The core challenge is to prove

$$
B-A=8d^5,
\qquad d>0
$$

implies

$$
A<B.
$$

Useful comparison axes are:

- the current `exact_mod_cast` → `pow_pos` → `linarith` pipeline,
- using `positivity` to package positivity of the right-hand side,
- reusing `factor_difference` versus unfolding `A`, `B` and using `W_pos`,
- how much intermediate structure to expose for auditability,
- where to handle the `ℕ` / `ℤ` coercion boundary.

In particular, separating nonlinear positivity via `pow_pos` before calling `linarith` makes this a good small tactic-comparison exercise.

## PDF cross-check

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the normal GitHub text fetch does not return the binary PDF contents, so this run cannot directly verify a page, section, or equation number. No such position is guessed here.

The Lean code, declaration order, direct dependencies, and relation to subsequent declarations were checked against the latest branch version of `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0316 `GoldenZeroSectorCandidate.A0`, whose kind is **`def`**.

The current Lean source continues with

```lean
/-- Natural representative of the positive lower factor. -/
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

After 0314 establishes $A>0$ and 0315 establishes the order $A<B$, the proof moves the signed integer factor $A$ to the natural-number side as

$$
A_0=|A|\in\mathbb N.
$$

The following declaration 0317 is the corresponding definition of `B0`.
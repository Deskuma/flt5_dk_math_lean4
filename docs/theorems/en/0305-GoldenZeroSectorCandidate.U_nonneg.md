# 0305 — `GoldenZeroSectorCandidate.U_nonneg`

## Declaration kind

This declaration is a **`theorem`**.

After 0304 `GoldenZeroSectorCandidate.d_odd` finishes the parity / five-adic constraints on the split base `d`, the proof turns to sign control for the auxiliary zero-sector quantity `U`. This theorem is the first declaration in that transition.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The diagonal sum is nonnegative independently of the candidate hypotheses. -/
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  positivity
```

The conclusion is an order proposition over the integers:

```lean
0 ≤ zeroSectorU p.r p.s
```

## Mathematical meaning

The relevant definitions are

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s

def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

Hence

$$
U(r,s)=X(r,s)^2+5s^2,
$$

where

$$
X(r,s)=2r+s.
$$

A square is always nonnegative, and since $5>0$, the term $5s^2$ is also nonnegative. Therefore

$$
U(r,s)\ge0
$$

for all integers $r,s$.

The important feature is that none of the Fermat-five-specific hypotheses stored in `GoldenZeroSectorCandidate` are used. No coprimality condition, sign condition, tenth-power splitting, or candidate equation enters the proof. The docstring phrase “independently of the candidate hypotheses” is literal: only the coordinates `p.r` and `p.s` are extracted from `p`.

## Role in the full proof

Later zero-sector inversion arguments use the exact reconstruction

$$
U-5s^2=X^2
$$

and then proceed to difference-of-squares and discriminant factorizations.

In that setting, nonnegativity of `U` supplies basic order information needed when `U` is treated as a square-derived quantity or as part of a signed factorization.

This theorem does not contribute a deep new number-theoretic restriction. Its role is infrastructural: it names an obvious positivity fact once, so later proofs can reuse it without reopening the local positivity argument.

It also marks a structural boundary in the development. Up through 0304 the focus is local arithmetic on the split base `d`; from 0305 onward the proof works with reconstructed quantities such as `U`, `W`, and `X` and with exact algebraic identities among them.

## Direct dependencies

### `zeroSectorU`

This is the definition unfolded directly by the proof:

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

Its definition already exposes the nonnegative-sum structure.

### `zeroSectorX`

The diagonal coordinate used inside `zeroSectorU`:

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

The proof does not need to unfold `zeroSectorX`. For `positivity`, the fact that `zeroSectorX p.r p.s` is an arbitrary integer expression is enough, because its square is nonnegative regardless of its internal form.

### `positivity`

The Mathlib positivity tactic. It automatically combines nonnegativity of squares, positivity of the constant `5`, and closure of nonnegativity under multiplication and addition.

There are no direct dependencies on candidate-specific theorems.

## Proof / construction flow

1. `unfold zeroSectorU` changes the goal into

   ```lean
   0 ≤ zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2
   ```

2. `positivity` recognizes that
   - `zeroSectorX p.r p.s ^ 2 ≥ 0`,
   - `p.s ^ 2 ≥ 0`,
   - `5 ≥ 0`,
   - products and sums of nonnegative terms remain nonnegative.
3. The goal is closed without using any hypothesis specific to `GoldenZeroSectorCandidate`.

On paper, the entire proof is simply: “it is a sum of nonnegative square terms.”

## Lean-specific processing

The key Lean-specific design choice is to unfold exactly one definition so that `positivity` sees a standard arithmetic expression.

Keeping the goal as `0 ≤ zeroSectorU p.r p.s` would rely on automation unfolding the definition implicitly. The explicit

```lean
unfold zeroSectorU
```

makes the proof interface stable and obvious.

By contrast, `zeroSectorX` remains folded. Its internal expression is irrelevant: `positivity` only needs to know that its square is nonnegative. This “unfold only what is necessary” pattern is both readable and robust.

## Redundancy and duplication

There is almost no redundancy inside this theorem.

One alternative would be to omit the named theorem entirely and repeat

```lean
unfold zeroSectorU
positivity
```

whenever nonnegativity is needed. If the fact is used more than once downstream, however, the named theorem is cleaner and avoids proof duplication.

There is one structural over-specialization: the argument `p : GoldenZeroSectorCandidate` is mathematically stronger than necessary. The statement actually holds for arbitrary integers:

```lean
theorem zeroSectorU_nonneg (r s : ℤ) : 0 ≤ zeroSectorU r s := by
  unfold zeroSectorU
  positivity
```

Thus the current theorem can be viewed as a specialization chosen to support convenient field-style notation such as `p.U_nonneg` in later proofs.

## Optimization candidates

The most natural refactoring would be to expose the candidate-independent fact as a general lemma:

```lean
theorem zeroSectorU_nonneg (r s : ℤ) :
    0 ≤ zeroSectorU r s := by
  unfold zeroSectorU
  positivity
```

and then define the current theorem by specialization:

```lean
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s :=
  zeroSectorU_nonneg p.r p.s
```

This would state the mathematical generality at the type level and make the lemma reusable outside the candidate namespace. The cost is an additional declaration for a fact whose current proof is only two lines.

There is little reason to replace the present `unfold` + `positivity` proof with a more elaborate `simpa`, `nlinarith`, or hand-written square-nonnegativity argument. The current implementation is already very compact and clear.

These refactoring candidates are **unverified** here because this museum task does not run Lean builds and does not modify the proof source.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The theorem directly needs functionality from at least these areas:

- ordered ring / integer order,
- nonnegativity of powers,
- the `positivity` tactic,
- the definitions `zeroSectorU` and `zeroSectorX`.

It does not directly require `ring`, `omega`, `linarith`, `norm_num`, or `exact_mod_cast`.

The standalone artifact uses the umbrella `Mathlib` import, and this task does not run Lean builds, so the exact minimal Mathlib import set is **not verified**.

An import-optimization pass should inspect the actual import graph of the source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` and experimentally verify whether the umbrella import can be reduced to the relevant algebra/order modules plus the positivity tactic module. No such source change is made here.

## Comparator challenge suitability

**Suitable, but very easy as a standalone challenge.**

Given the statement and the definition of `zeroSectorU`, the expected proof is essentially

```lean
unfold zeroSectorU
positivity
```

A more useful Comparator challenge would therefore compare proof strategies:

- Is it necessary to unfold `zeroSectorX` as well?
- How does a manual proof using square nonnegativity or `nlinarith` compare with `positivity`?
- Can the solver notice that no candidate hypothesis is needed?

The difficulty is beginner level. It is a good micro-exercise for learning `positivity` and minimal unfolding.

## Comparison with the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the normal GitHub text-fetch path does not return the contents of binary PDFs, so this task could not directly verify the exact PDF page, section, or equation number corresponding to 0305. No PDF location is inferred.

The Lean code, declaration order, technical interpretation, and direct dependencies in this note are grounded in the repository's `Flt5DkMath/FLT5StandAlone.lean` canonical source.

## Next declaration to read

The next declaration is 0306 `GoldenZeroSectorCandidate.square_reconstruction`, again a **`theorem`**.

The canonical Lean source places immediately after `U_nonneg`:

```lean
/-- The reconstructed square coordinate is retained exactly. -/
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 := by
  unfold zeroSectorU
  ring
```

Where 0305 records the order property of `U`, 0306 strengthens the picture to the exact identity

$$
U-5s^2=X^2.
$$

This moves the development from mere nonnegativity to an explicit square reconstruction, preparing the later factorization and discriminant manipulations.

# 0003 — `fifth_sub_eq_of_add_eq`

> This document is the English translation of the Japanese canonical edition.

## Lean declaration

```lean
theorem fifth_sub_eq_of_add_eq
    {x y z : ℕ}
    (hEq : Fermat5Equation x y z) :
    z ^ 5 - y ^ 5 = x ^ 5 := by
  unfold Fermat5Equation at hEq
  omega
```

The fully qualified name is `DkMath.FLT.Five.fifth_sub_eq_of_add_eq`.

## Mathematical statement

The hypothesis `hEq` is the exponent-five Fermat equation

$$
x^5+y^5=z^5.
$$

The theorem converts this additive form into

$$
z^5-y^5=x^5.
$$

Over the integers this looks like a routine transposition. The ambient type here is `ℕ`, however, and natural-number subtraction is truncated. One cannot move an additive term across an equality without justification in general. The original equation itself guarantees `y ^ 5 ≤ z ^ 5`, so the subtraction is valid in this case.

## Role in the complete proof

This theorem is the first bridge from the equation interface to the later gap factorization.

The development subsequently expresses `z ^ 5 - y ^ 5` as the product of the natural gap `z-y` and `GN5 (z-y) y`. Thus the route from the counterexample equation to

$$
x^5=(z-y)\,\mathrm{GN5}(z-y,y)
$$

requires the difference of fifth powers to be exposed first.

The theorem does not yet introduce `z-y`; it performs the first algebraic normalization that makes the later difference-of-powers factorization available.

## Direct dependencies

Its only direct project-specific dependency is:

- `DkMath.FLT.Five.Fermat5Equation`

The proof uses:

- definitional unfolding with `unfold`;
- Presburger arithmetic through `omega`;
- natural-number addition, subtraction, and fixed power terms.

A key point is that `omega` is not expanding the fifth powers or proving nonlinear identities. The terms `x ^ 5`, `y ^ 5`, and `z ^ 5` are treated as already formed natural-number expressions, and the tactic solves the linear additive and subtractive relation among them.

## Proof flow

The proof has two steps.

1. `unfold Fermat5Equation at hEq` replaces the named predicate by the raw equality `x ^ 5 + y ^ 5 = z ^ 5`.
2. `omega` derives `z ^ 5 - y ^ 5 = x ^ 5` from that equality.

Conceptually, the hypothesis first yields `y ^ 5 ≤ z ^ 5`. Under that bound, natural subtraction behaves as the expected difference and the additive term can be removed. The implementation leaves this intermediate inequality implicit and lets `omega` solve the complete arithmetic step.

## Lean-specific processing

### Natural-number subtraction

In `ℕ`, for example, `3 - 5 = 0`. Therefore the integer-style phrase “subtract the same term from both sides” is unsafe unless the required order is known.

The theorem is sound because the hypothesis provides

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

and hence implies that the right-hand side is at least `y ^ 5`.

### Targeted unfolding

```lean
unfold Fermat5Equation at hEq
```

unfolds the predicate only in the hypothesis `hEq`. The goal contains no occurrence of `Fermat5Equation`, so no goal-side unfolding is needed.

### Scope of `omega`

Although the exponent is the fixed numeral five, `omega` is not proving a binomial or power theorem. It treats the power terms atomically and solves the natural-number arithmetic pattern

```text
A + B = C  ⟹  C - B = A.
```

## Redundancy and duplication

The proof is already extremely short and contains no obvious local duplication.

If the repository contains many proofs converting `a + b = c` into `c - b = a`, a shared standard lemma could reduce repeated tactic calls. Such a refactoring might also reduce dependence on `omega` in small local lemmas.

This article has not audited the entire repository for identical proof shapes, so it does not claim that such duplication actually exists.

## Optimization candidates

### An explicit readability-oriented proof

The one-line `omega` step is concise and robust. For pedagogical purposes, however, a proof using standard natural-number subtraction lemmas could make the order requirement visible.

The exact Mathlib lemma names and orientations needed for that replacement have not been verified here. Any proposed rewrite must be checked in Lean before adoption.

### Reducing tactic dependence

This isolated theorem may be provable entirely with elementary natural-number lemmas. That matters for import minimization only if the surrounding module does not otherwise require `omega`. If the file already uses the tactic elsewhere, replacing this single call would not reduce module imports.

### Preserving the API boundary

The present theorem accepts `Fermat5Equation` rather than a raw equality. This keeps the foundational API consistent and is worth preserving.

## Required Mathlib imports and optimization candidates

The standalone imports `Mathlib`, and the repository build confirms that the theorem works in that environment.

The principal required features are:

- natural numbers and natural subtraction;
- power notation;
- `unfold`;
- the `omega` tactic.

For import minimization, a tactic module such as `Mathlib.Tactic.Omega`, together with the basic modules for naturals and powers, is a plausible starting point. Whether `Mathlib.Tactic.Omega` alone imports every required definition transitively has not been tested.

A minimal-import audit should use a temporary file, `#min_imports` or explicit candidate imports, and a clean build. No Lean build was performed for this article, so no exact minimal import is asserted.

## Comparator challenge suitability

This theorem is well suited to a small Comparator challenge.

It tests several distinct choices:

- unfolding a named proposition;
- respecting the difference between integer and natural subtraction;
- solving the goal automatically with `omega`;
- replacing automation with explicit standard lemmas.

A challenge can use:

```lean
theorem fifth_sub_eq_of_add_eq_challenge
    {x y z : ℕ}
    (hEq : Fermat5Equation x y z) :
    z ^ 5 - y ^ 5 = x ^ 5 := by
  -- prove without using the project theorem
  sorry
```

Candidate solutions can compare an `omega` proof, an explicit standard-lemma proof, and a proof that first states the necessary inequality. The difficulty is beginner to early intermediate.

## Next theorem to study

The next natural theorem is `DkMath.FLT.Five.right_lt_of_fermat5Equation`.

The current theorem obtains a difference of fifth powers, but the later gap `z-y` must be positive. `right_lt_of_fermat5Equation` derives the strict inequality `y < z` from `0 < x` and the Fermat equation, and directly feeds `gap_pos_of_fermat5Equation`.

## Evidence and inference

The declaration type, two-line proof, direct dependency on `Fermat5Equation`, and use of `unfold` and `omega` are directly supported by the Lean source.

The explanation that `omega` treats the power terms atomically follows from the arithmetic form presented to the tactic. The proposed standard-lemma replacement, exact minimal imports, and possible repository-wide duplication are unverified optimization proposals rather than established facts.

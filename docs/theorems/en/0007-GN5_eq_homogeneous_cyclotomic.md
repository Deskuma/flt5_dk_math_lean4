# 0007 — `GN5_eq_homogeneous_cyclotomic`

> This document is the English translation corresponding to the Japanese canonical edition.

## Lean type

```lean
theorem GN5_eq_homogeneous_cyclotomic (g y : ℕ) :
    GN5 g y =
      (g + y) ^ 4 + (g + y) ^ 3 * y + (g + y) ^ 2 * y ^ 2 +
        (g + y) * y ^ 3 + y ^ 4 := by
  unfold GN5
  ring
```

Its fully qualified name is `DkMath.FLT.Five.GN5_eq_homogeneous_cyclotomic`.

## Mathematical statement

`GN5 g y` agrees with the standard homogeneous factor of a difference of fifth powers

$$
z^4+z^3y+z^2y^2+zy^3+y^4
$$

after substituting $z=g+y$. Thus,

$$
GN5(g,y)=(g+y)^4+(g+y)^3y+(g+y)^2y^2+(g+y)y^3+y^4.
$$

In the standard identity

$$
z^5-y^5=(z-y)(z^4+z^3y+z^2y^2+zy^3+y^4),
$$

setting $g=z-y$, hence $z=g+y$, turns the degree-four factor on the right into `GN5 g y`.

## Role in the complete proof

The previous article introduced `GN5` in expanded positive-coefficient form. This theorem fixes that expanded polynomial as the standard homogeneous cyclotomic factor of the fifth-power difference, rather than an arbitrary auxiliary polynomial.

It allows the development to move between two useful views:

- the expanded form, suited to extracting the gap $g$ or the prime $5$ and reading congruences and divisibility;
- the standard factor form, suited to understanding the classical factorization of the fifth-power difference.

Later lemmas do not all invoke this theorem directly; many unfold `GN5` and prove their identities independently. Nevertheless, this theorem is the semantic reference point connecting the local gap-coordinate polynomial to the classical factorization.

## Direct dependencies

Its only project-specific direct dependency is:

- `DkMath.FLT.Five.GN5`

The proof also uses Mathlib's polynomial normalization tactic `ring`.

Mathematically it requires only binomial expansion and a polynomial identity in a commutative semiring. It does not depend on the FLT5 equation, positivity, or coprimality.

## Proof flow

The proof has two steps.

1. `unfold GN5` replaces the left-hand side by its expanded definition.
2. `ring` normalizes both sides as commutative-semiring polynomials and proves that the normal forms coincide.

The normalization confirms that expanding the powers $(g+y)^k$ on the right collects the coefficients

$$
1,\ 5,\ 10,\ 10,\ 5,
$$

which are exactly those in the definition of `GN5`.

## Lean-specific processing

`ring` is not evaluating particular natural numbers. It proves equality by normalizing expressions built from addition, multiplication, and powers. Although the variables here have type `ℕ`, the mathematical identity itself is not specific to natural numbers; it holds in a commutative semiring.

`unfold GN5` exposes the definition to the tactic. A possible alternative is:

```lean
  simp only [GN5]
  ring
```

The existing two-line proof is already direct and clear.

## Redundancy and duplication

The definition of `GN5` and the right-hand side of this theorem are two presentations of the same polynomial, so they duplicate algebraic information. The duplication is purposeful:

- the definition provides coordinates suited to gap and five-adic decompositions;
- the theorem supplies the semantic identification with the standard cyclotomic factor.

Removing the theorem would leave the implementation possible but would weaken the explanatory and auditing API.

## Optimization candidates

The proof is already short, with little runtime optimization available. Possible design-level changes include:

- proving the identity over an arbitrary commutative semiring and specializing it to `ℕ`;
- naming the standard homogeneous factor separately and making this theorem the bridge between the two definitions;
- using this theorem explicitly as a rewrite API when later proofs need the standard factor form.

Such generalization may increase imports and type-inference overhead, while the current natural-number API remains local and simple. These are unverified design proposals.

## Required Mathlib imports and import-minimization candidates

The standalone currently uses `import Mathlib`. The essential facilities for this theorem are:

- natural-number addition, multiplication, and powers;
- the `ring` tactic.

The exact minimal import was not verified in this run. It should be audited by placing only `GN5` and this theorem in a temporary file, applying `#min_imports` or reducing imports incrementally, and then running a clean build.

`Mathlib.Tactic` is a broad candidate providing `ring`, but it may not be minimal. This is an inference.

## Comparator challenge suitability

This theorem is well suited to a compact Comparator challenge. Candidate proof styles include:

- `unfold GN5; ring`;
- `simp [GN5]; ring`;
- normalization with `ring_nf`;
- a manual proof using binomial-expansion lemmas and arithmetic rewrites.

Useful comparison criteria include proof length, robustness under definition changes, readability of failures, and potential for generalization. The current `unfold GN5; ring` proof is the most direct baseline.

## Next theorem to study

The next theorem is `DkMath.FLT.Five.GN5_eq_gap_mul_add_five_mul_y_pow_four`.

The present theorem establishes the standard-factor meaning of `GN5`; the next theorem collects all terms containing the gap $g$ and obtains

$$
GN5(g,y)=g\,A(g,y)+5y^4.
$$

This is the first divisibility interface exposing $GN5(g,y)\equiv 5y^4\pmod g$.

## Evidence and inference

The Lean type, proof body, definition of `GN5`, and the following gap-decomposition theorem come directly from the repository source. Generalization to arbitrary commutative semirings, the exact minimal imports, and API-refactoring proposals are analysis in this article and were not validated by a Lean build.

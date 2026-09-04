# 0008 — `GN5_eq_gap_mul_add_five_mul_y_pow_four`

> This document is an English translation of the Japanese canonical edition. In case of discrepancy, the Japanese edition is authoritative.

## Lean type

```lean
theorem GN5_eq_gap_mul_add_five_mul_y_pow_four (g y : ℕ) :
    GN5 g y =
      g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) +
        5 * y ^ 4 := by
  unfold GN5
  ring
```

Its fully qualified name is `DkMath.FLT.Five.GN5_eq_gap_mul_add_five_mul_y_pow_four`.

## Mathematical statement

The theorem decomposes the fifth cyclotomic factor in gap coordinates into a multiple of the gap $g$ and the remainder $5y^4$.

$$
GN5(g,y)=g\bigl(g^3+5g^2y+10gy^2+10y^3\bigr)+5y^4
$$

Hence one may read the congruence

$$
GN5(g,y)\equiv 5y^4\pmod g.
$$

## Role in the complete proof

This is the first local decomposition used to study common prime divisors of `GN5 g y` and the gap $g$. If a prime $q$ divides both $g$ and `GN5 g y`, the identity forces $q$ to divide $5y^4$ as well.

At later stages where coprimality of $g$ and $y$ is available, divisibility of $y$ can be excluded, leaving the exceptional prime $5$. The standalone module documentation explicitly explains that this gap decomposition and the following five-adic decomposition expose why five is the only exceptional common prime in the primitive route.

The theorem itself assumes neither primality nor coprimality. It provides only the polynomial identity required by later divisibility arguments.

## Direct dependencies

The only direct project-specific dependency is the definition of `GN5`.

```lean
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4
```

The proof also depends on the `ring` tactic. The preceding theorem `GN5_eq_homogeneous_cyclotomic` supplies mathematical context but is not invoked directly.

## Proof flow

The proof has two steps.

1. `unfold GN5` expands the left-hand side to its defining polynomial.
2. `ring` normalizes both sides as expressions in a commutative semiring and proves equality.

After expansion, the first four terms all contain a factor $g$. Factoring them produces the term $g(\cdots)$, while the final term $5y^4$ remains outside.

## Lean-specific processing

`ring` works over the natural numbers because they form a commutative semiring. No subtraction occurs, so no side condition concerning truncated natural-number subtraction is required.

The conclusion is stated as an equality rather than directly with `%` or `Nat.ModEq`. This stronger algebraic form allows later proofs to choose whichever divisibility or congruence interface best fits the local argument.

## Redundancy and duplication

The theorem is obtained merely by regrouping the defining polynomial, so later proofs could repeatedly unfold `GN5` and reproduce it. A named API is nevertheless valuable because this exact form is central to divisibility arguments.

The preceding theorem `GN5_eq_homogeneous_cyclotomic` also has the proof `unfold GN5; ring`, but the two declarations have different roles:

- `GN5_eq_homogeneous_cyclotomic` identifies the expression with the standard cyclotomic factor.
- The present theorem exposes the coordinate decomposition needed for reduction modulo the gap.

Thus similar proof scripts do not imply redundant mathematical interfaces.

## Optimization candidates

The proof is already close to minimal. Possible improvements concern derived APIs rather than proof performance.

If later code repeatedly needs the congruence, one could consider adding:

```lean
lemma GN5_mod_gap (g y : ℕ) : GN5 g y % g = (5 * y ^ 4) % g := by
  rw [GN5_eq_gap_mul_add_five_mul_y_pow_four]
  omega
```

However, the behavior at $g=0$ and the actual preference of later code for `%`, `Nat.ModEq`, or divisibility lemmas should be audited first. This proposal is unverified.

A direct theorem of type `Nat.ModEq g (GN5 g y) (5 * y ^ 4)` may express the intended congruence more clearly.

## Required Mathlib imports and import optimization

The standalone uses `import Mathlib`, and the repository source confirms that the theorem works in that environment.

The essential ingredients are:

- natural-number addition, multiplication, and powers;
- the `ring` tactic.

The exact minimal import is not established here. A combination involving `Mathlib.Tactic.Ring` and basic natural-number algebra may suffice, but this is an inference requiring `#min_imports` and clean-build verification.

## Comparator challenge suitability

The theorem is suitable for a small Comparator challenge because several proof styles can be contrasted:

- the standard `unfold GN5; ring` proof;
- `simp [GN5]` followed by `ring_nf`;
- a structured proof that explicitly factors the first four terms;
- an unnecessarily indirect route through a congruence theorem.

It is especially useful for comparing concise tactic proofs with human-readable factor extraction.

## Next declaration

The next declaration is `DkMath.FLT.Five.GN5_eq_g_pow_four_add_five_mul`.

Where the present theorem reduces `GN5` modulo the gap and leaves $5y^4$, the next one reduces it modulo $5$ and leaves $g^4$:

$$
GN5(g,y)=g^4+5B(g,y).
$$

Together, these two transverse decompositions reveal the structure of common divisors and the five-adic exceptional case.

## Evidence and inference

The theorem type, proof, definition of `GN5`, following five-adic decomposition, and the module-level explanation of the exceptional prime five come directly from the Lean source.

The congruence interpretation, common-divisor analysis, proposed derived APIs, minimal-import discussion, and Comparator assessment are analysis or unverified proposals. No Lean build was run for this article.

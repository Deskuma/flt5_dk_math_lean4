# 0010 — `add_pow_five_eq_add_mul_GN5`

> This document is the English translation corresponding to the Japanese canonical edition.

## Lean type

```lean
theorem add_pow_five_eq_add_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 = y ^ 5 + g * GN5 g y := by
  unfold GN5
  ring
```

The fully qualified name is `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5`.

## Mathematical statement

The fifth-power binomial expansion is separated into the base term $y^5$ and a residual part carrying the gap $g$ as a factor.

$$
(g+y)^5=y^5+g\,GN5(g,y)
$$

After substituting the definition of `GN5`, the second term on the right collects exactly every term of the binomial expansion except $y^5$.

## Role in the complete proof

This theorem connects the polynomial `GN5`, analyzed in the preceding articles, to an actual fifth power. The previous theorems provided internal representations of `GN5`; this theorem is the first one to expose $g\,GN5(g,y)$ as the fifth-power body by an equality.

Subsequent results derive the natural-number difference form

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

and then substitute $g=z-y$ to connect it to $x^5$ in the Fermat equation.

## Direct dependencies

The only project-specific direct dependency is `DkMath.FLT.Five.GN5`. The proof uses Mathlib's `ring` tactic.

Although the declaration appears after the three representation theorems for `GN5`, it does not invoke them in its proof. Its logical project dependency is therefore only the definition of `GN5`.

## Proof flow

1. `unfold GN5` expands the residual kernel.
2. `ring` converts the fifth power on the left and the polynomial on the right into normal forms over a commutative semiring.
3. Equality follows from coefficient agreement.

Mathematically, this is the binomial identity

$$
(g+y)^5=y^5+5gy^4+10g^2y^3+10g^3y^2+5g^4y+g^5
$$

with every term except $y^5$ factored by $g$.

## Lean-specific processing

The equality is over natural numbers but contains no subtraction, so no truncated-`Nat.sub` issue occurs. This is the design advantage of fixing the additive form before introducing the difference form.

`ring` does not evaluate concrete naturals. It uses the commutative-semiring structure of `ℕ` to normalize a polynomial identity.

## Redundancy and overlap

The proof script is the same `unfold GN5; ring` pattern used by earlier `GN5` identities. Its API role is nevertheless different: it connects the kernel to the fifth power itself rather than merely publishing another internal representation.

The next theorem, `add_pow_five_sub_eq_mul_GN5`, is a thin wrapper deriving the subtraction form. The two results remain usefully distinct because the additive form is unconditional and semiring-friendly, whereas the subtraction form contains natural-number subtraction.

## Optimization candidates

The proof is already close to minimal. One could derive it from `GN5_eq_homogeneous_cyclotomic` and the standard factorization of a fifth-power difference, but that would add dependencies and would likely be longer than the direct `ring` proof.

A `[simp]` attribute may appear tempting if the theorem is used frequently for rewriting. However, automatically expanding a fifth power in this direction can enlarge expressions, so adding such an attribute without testing is not recommended. These are design proposals, not verified changes.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`. The essential requirements here are the natural-number semiring structure, powers, and the `ring` tactic. The exact minimal import cannot be established without a Lean build.

A possible smaller set would involve `Mathlib.Tactic.Ring` and a basic natural-number algebra module, but the generated standalone file also needs the later number-theoretic and algebraic development. No import was changed in this work.

## Comparator challenge suitability

This theorem is suitable for a Comparator challenge. Possible competitors are:

1. the direct `unfold GN5; ring` proof;
2. a proof through `GN5_eq_homogeneous_cyclotomic` and the standard fifth-power factorization;
3. a `ring_nf` or manual binomial-expansion proof.

Useful comparison axes are proof length, dependency count, normalization cost, and explanatory value.

## Next theorem to read

The next declaration is `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5`.

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

It moves from the subtraction-free additive identity to the direct factorization API for a difference of fifth powers.

## Facts versus proposals

The theorem type, proof, declaration order, direct dependency on `GN5`, and next theorem are verified from the Lean source. The `[simp]` discussion, alternative proof, minimal imports, and Comparator evaluation are unverified proposals. No Lean build was run.
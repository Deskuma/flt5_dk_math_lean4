# 0016 — `CleanGN5Channel.dvd_body`

> This document is the English translation of the Japanese canonical article.

## Lean type

```lean
theorem CleanGN5Channel.dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    q ∣ g * GN5 g y := by
  exact dvd_mul_of_dvd_right h.dvd_GN5 g
```

The fully qualified name is `DkMath.FLT.Five.CleanGN5Channel.dvd_body`.

## Mathematical statement

Given `CleanGN5Channel g y q`, the field `h.dvd_GN5` gives $q∣GN5(g,y)$. Therefore $q$ also divides the product obtained by multiplying by $g$ on the left.

$$
q∣GN5(g,y)\Longrightarrow q∣g\,GN5(g,y)
$$

Primality, nondivisibility of the gap, and square nondivisibility are not needed for this conclusion.

## Role in the complete proof

The preceding fifth-power factorization writes the body as $g\,GN5(g,y)$. This theorem is the first consumer API that transfers the local divisor stored by `CleanGN5Channel` to that full body.

Later, `not_fifth_power_body_of_clean` assumes that the body is a fifth power. This theorem supplies that $q$ divides the fifth power. Primality then yields $q∣x`, and the proof eventually contradicts `not_sq_dvd_body`.

## Direct dependencies

- `DkMath.FLT.Five.CleanGN5Channel`
- the projection `CleanGN5Channel.dvd_GN5`
- `dvd_mul_of_dvd_right`
- `DkMath.FLT.Five.GN5`

Mathematically, the theorem uses only closure of divisibility under multiplication. It does not depend on `h.prime`, `h.not_dvd_gap`, or `h.noLift`.

## Proof flow

1. Extract $q∣GN5(g,y)$ from `h.dvd_GN5`.
2. Pass that proof and the additional factor $g$ to `dvd_mul_of_dvd_right`.
3. Obtain $q∣g\,GN5(g,y)$.

The proof term is one line.

```lean
exact dvd_mul_of_dvd_right h.dvd_GN5 g
```

## Lean-specific processing

`dvd_mul_of_dvd_right` lifts divisibility of the right factor to divisibility of the whole product. Here `h.dvd_GN5 : q ∣ GN5 g y` is supplied together with the extra factor `g`.

Although the result is displayed as `g * GN5 g y`, the word `right` in the lemma name refers to the divisible factor being on the right. No commutativity rewrite or `simpa [Nat.mul_comm]` is required.

Because the theorem is declared in namespace `CleanGN5Channel`, it can also be used in method style as `h.dvd_body`.

## Redundancy and duplication

The result can be derived from `h.dvd_GN5` in one line at every use site, so it is logically a thin wrapper. However, it gives a meaningful name to the fact that a clean channel divides the body and localizes the product orientation and standard lemma choice.

It is therefore removable duplication in principle, but worth retaining as a readable public API.

## Optimization candidates

1. A `[simp]` attribute is probably unnecessary; making divisibility propositions automatic rewrite targets may obscure proof search.
2. If the body later receives a dedicated definition, this theorem could be restated through that definition.
3. No further generalization is required: the standard multiplication lemma already expresses the abstract fact.
4. An opposite-orientation wrapper should be considered only if later code repeatedly uses the reversed product.

These are design proposals and were not validated by a Lean build.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. In isolation, this theorem needs basic natural-number divisibility and multiplication, `dvd_mul_of_dvd_right`, and the local declarations `CleanGN5Channel` and `GN5`.

The Mathlib dependency may be reducible to a basic divisibility module. However, the actual file `CleanChannel.lean` also contains later theorems using primes, coprimality, powers, and `ring`, so file-level import minimization cannot be determined from this theorem alone. The minimal import set is unverified.

## Comparator challenge suitability

This theorem is suitable for a small Comparator challenge.

- Use `exact dvd_mul_of_dvd_right h.dvd_GN5 g`.
- Check whether an equivalent opposite-facing multiplication API is available.
- Expand the divisibility witness with `rcases h.dvd_GN5 with ⟨k, hk⟩` and construct the result directly.
- Compare with a proof using `simpa [Nat.mul_comm]`.

Comparison criteria are proof-term size, clarity of product orientation, reliance on standard lemmas, and simplicity of the generated proof term. The judgment that the current proof is probably the most direct is an interpretation.

## Next theorem to read

The next theorem is `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body`.

Where this theorem establishes divisibility of the body by $q$, the next theorem proves

$$
q^2∤g\,GN5(g,y)
$$

It is the first point where the remaining fields `prime`, `not_dvd_gap`, and `noLift` are combined, fixing the local exponent of $q$ in the full body to exactly one.

## Sources versus interpretation

The theorem type, proof, declaration order, and later use of `h.dvd_body` were verified in the generated source for `DkMath/FLT/Five/CleanChannel.lean` contained in `Flt5DkMath/FLT5StandAlone.lean`. Role analysis, API-retention judgment, import minimization, and Comparator proposals include interpretation or unverified suggestions. No Lean build was run.
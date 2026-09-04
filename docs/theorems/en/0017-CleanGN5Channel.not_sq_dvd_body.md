# 0017 — `CleanGN5Channel.not_sq_dvd_body`

> This document is the English translation corresponding to the Japanese canonical edition.

## Lean type

```lean
theorem CleanGN5Channel.not_sq_dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ q ^ 2 ∣ g * GN5 g y := by
  intro hqSqBody
  apply h.noLift
  have hqCoprimeGap : Nat.Coprime q g :=
    (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_gap
  have hqSqCoprimeGap : Nat.Coprime (q ^ 2) g :=
    hqCoprimeGap.pow_left 2
  exact Nat.Coprime.dvd_of_dvd_mul_left hqSqCoprimeGap hqSqBody
```

Its fully qualified name is `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body`.

## Mathematical statement

`CleanGN5Channel g y q` records that $q$ is prime, $q∤g$, and $q^2∤GN5(g,y)$. This theorem combines those facts to show that the square $q^2$ cannot enter the full product either.

$$
q^2∤g\,GN5(g,y)
$$

Assume for contradiction that $q^2∣g\,GN5(g,y)$. Since $q$ is prime and does not divide $g$, $q$ is coprime to $g$, hence $q^2$ is also coprime to $g$. Removing the coprime factor $g$ from the product gives $q^2∣GN5(g,y)$, contradicting `h.noLift`.

## Role in the complete proof

The preceding theorem `CleanGN5Channel.dvd_body` established $q∣g\,GN5(g,y)$. The present theorem establishes $q^2∤g\,GN5(g,y)$ for the same body. Therefore the local exponent of $q$ in the body is exactly one.

The later theorem `not_fifth_power_body_of_clean` assumes that the body is a fifth power $x^5$. From `dvd_body` and primality it obtains $q∣x`; then $q^2∣x^5$, hence $q^2∣g\,GN5(g,y)$, contradicting this theorem. Thus this result is the central square-divisibility form of the local valuation-one obstruction.

## Direct dependencies

- `DkMath.FLT.Five.CleanGN5Channel`
- field `h.prime : Nat.Prime q`
- field `h.not_dvd_gap : ¬ q ∣ g`
- field `h.noLift : ¬ q ^ 2 ∣ GN5 g y`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.dvd_of_dvd_mul_left`
- `DkMath.FLT.Five.GN5`

The field `h.dvd_GN5` is not used here. This theorem proves only the non-divisibility of the body by the square, not the divisibility of the body by $q$.

## Proof flow

1. Introduce the contradictory assumption $q^2∣g\,GN5(g,y)$ as `hqSqBody`.
2. Apply `h.noLift`, changing the goal to constructing $q^2∣GN5(g,y)$.
3. Derive `Nat.Coprime q g` from primality and $q∤g$.
4. Use `pow_left 2` to derive `Nat.Coprime (q ^ 2) g`.
5. Use `Nat.Coprime.dvd_of_dvd_mul_left` to remove the left factor $g$ from the product and obtain $q^2∣GN5(g,y)$.
6. This contradicts `h.noLift`.

## Lean-specific processing

`apply h.noLift` treats the negation `¬ q ^ 2 ∣ GN5 g y` as a function and transforms the contradiction goal into the positive divisibility statement needed as its input.

```lean
have hqCoprimeGap : Nat.Coprime q g :=
  (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_gap
```

This uses the equivalence, for prime $q$, between coprimality of $q$ and $g$ and non-divisibility of $g$ by $q$. The `.mpr` direction moves from the right-hand proposition to the left-hand proposition.

`hqCoprimeGap.pow_left 2` raises only the left component, producing `Nat.Coprime (q ^ 2) g`. Finally, `dvd_of_dvd_mul_left` extracts divisibility of the right factor from divisibility of the product because $q^2$ is coprime to the left factor $g$.

## Redundancy and overlap

This proof expresses a local exponent bound using only divisibility and coprimality, without introducing valuations. The later module `Valuation.lean` repackages the same obstruction as incompatible valuation bounds, so there is mathematical overlap. However, the present theorem is more elementary, has lighter dependencies, and directly supports the square-divisibility contradiction; it is not disposable duplication.

The intermediate facts `hqCoprimeGap` and `hqSqCoprimeGap` could be compressed into one expression, but the current form makes the two stages—prime non-divisibility to coprimality, then coprimality of the square—explicit.

## Optimization candidates

1. The two `have` statements could be inlined, at a possible cost in readability.
2. The argument could be generalized from $q^2$ to $q^n`, yielding a reusable no-lift lemma.
3. Keeping this body-specific wrapper is reasonable because it localizes the direction of `dvd_of_dvd_mul_left` and reduces factor-order mistakes.
4. In a layer where valuation APIs are already available, one could compare this proof with a proof computing the valuation of the product from $v_q(g)=0$ and $v_q(GN5)=1$.
5. A `[simp]` attribute is usually undesirable because it would broadly automate a negative divisibility statement.

These are design observations or unverified proposals. No Lean build comparison was performed.

## Required Mathlib imports and import optimization

The standalone generated artifact uses `import Mathlib`. This theorem directly needs natural-number primality, divisibility, coprimality, powers, and the following lemmas:

- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.dvd_of_dvd_mul_left`

The actual file `CleanChannel.lean` also uses `dvd_of_dvd_pow`, existential witnesses, `ring`, and concrete `norm_num` computations in later declarations. Therefore the file-level minimal import cannot be determined from this theorem alone. Narrowing `Mathlib` to specific prime and divisibility modules may be possible, but remains unverified.

## Comparator challenge suitability

This theorem is a good Comparator challenge. Candidate proofs include:

- the current coprimality-based factor-removal proof;
- a witness-level divisibility proof using an explicit Euclid lemma;
- a proof establishing coprimality of $q^2$ and $g$ directly without `Nat.Coprime.pow_left`;
- a valuation-based proof showing that the $q$-adic exponent of the product is at most one;
- a compressed proof with the intermediate `have` statements inlined.

Comparison criteria include proof-term size, required imports, clarity of factor orientation, generalizability, and locality of error messages. The current proof is strong in exposing the elementary mathematical structure with standard APIs.

## Next theorem to read

The next theorem is `DkMath.FLT.Five.not_fifth_power_GN5_of_clean`.

Before treating the full body, it targets `GN5(g,y)` itself and uses `h.dvd_GN5` together with `h.noLift` to prove

$$
¬\exists x\in\mathbb{N},\ GN5(g,y)=x^5.
$$

It is the first completed no-fifth-power consumer theorem obtained from a clean channel.

## Sources and inference status

The theorem type, proof, declaration order, and later use were verified in the generated source for `DkMath/FLT/Five/CleanChannel.lean` embedded in `Flt5DkMath/FLT5StandAlone.lean`. The assessment of its role, redundancy, import minimization, generalizations, and Comparator variants includes explanatory analysis or unverified proposals. No Lean build was run.
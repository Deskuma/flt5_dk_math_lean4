# 0018 — `not_fifth_power_GN5_of_clean`

> This document is the English translation corresponding to the Japanese canonical edition.

## Lean type

```lean
theorem not_fifth_power_GN5_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    simpa [hx] using h.dvd_GN5
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.noLift
  rw [hx]
  use q ^ 3 * k ^ 5
  ring
```

The fully qualified name is `DkMath.FLT.Five.not_fifth_power_GN5_of_clean`.

## Mathematical statement

Given `CleanGN5Channel g y q`, the value `GN5(g,y)` is not a perfect fifth power in the natural numbers.

$$
¬\exists x\in\mathbb{N},\ GN5(g,y)=x^5
$$

The structure records that $q$ is prime, $q∣GN5(g,y)$, and $q^2∤GN5(g,y)$. If instead $GN5(g,y)=x^5$, then $q∣x^5$ implies $q∣x$, hence $q^2∣x^5=GN5(g,y)$. This contradicts `noLift`.

## Role in the complete proof

This is the first completed consumer theorem converting a clean channel into a perfect-fifth-power obstruction. The preceding theorems `dvd_body` and `not_sq_dvd_body` controlled the local exponent in the full body $g\,GN5(g,y)$; this theorem treats the smaller object `GN5(g,y)` itself.

The following theorem `not_fifth_power_body_of_clean` lifts the same argument to the full body. Later, `GN5_one_one_not_fifth_power` supplies the concrete channel `cleanGN5Channel_one_one_31` to this theorem and immediately concludes that $GN5(1,1)=31$ is not a fifth power.

## Direct dependencies

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.GN5`
- field `h.prime : Nat.Prime q`
- field `h.dvd_GN5 : q ∣ GN5 g y`
- field `h.noLift : ¬ q ^ 2 ∣ GN5 g y`
- `Nat.Prime.dvd_of_dvd_pow`
- `simpa`
- `rintro`
- `obtain`
- `ring`

The field `h.not_dvd_gap` is unused. Since the target is `GN5` alone rather than the full body, no coprimality with the gap is needed.

## Proof flow

1. Assume that there exists $x$ with `GN5 g y = x ^ 5`.
2. Rewrite `h.dvd_GN5` using `hx` to obtain $q∣x^5$.
3. Use `h.prime.dvd_of_dvd_pow` to derive $q∣x$.
4. Replace $x$ by $qk$.
5. Apply `h.noLift`, reducing the contradiction to proving $q^2∣GN5(g,y)$.
6. Rewrite `GN5(g,y)` as $(qk)^5` using `hx`.
7. Provide $q^3k^5$ as the quotient and close $q^2(q^3k^5)=(qk)^5$ with `ring`.

## Lean-specific processing

`rintro ⟨x, hx⟩` opens the negated existential and introduces both the witness $x$ and the equality `hx`.

```lean
have hqDivPow : q ∣ x ^ 5 := by
  simpa [hx] using h.dvd_GN5
```

This changes the dividend in `h.dvd_GN5` from `GN5 g y` to `x^5` via `hx`.

`obtain ⟨k, rfl⟩ := hqDivX` extracts a divisibility witness from $q∣x$ and immediately substitutes $x=qk$. Finally, `use q ^ 3 * k ^ 5` gives the quotient for $q^2$, and `ring` proves the semiring polynomial identity over natural numbers.

## Redundancy and overlap

The following theorem `not_fifth_power_body_of_clean` has the same proof skeleton. The difference is that it uses `h.dvd_body` and `h.not_sq_dvd_body`, and its target is $g\,GN5(g,y)$. A common abstract lemma could factor out the shared argument, but the current pair keeps the target objects and dependencies explicit.

The direct quotient $q^3k^5$ is specialized to exponent five. For a general exponent $n\ge2$, the corresponding quotient would be $q^{n-2}k^n$.

## Optimization candidates

1. Extract a general lemma: if a prime $q$ divides $x^n$ and $n\ge2$, then $q^2∣x^n$.
2. Replace the explicit witness and `ring` with a combination of `dvd_pow` lemmas, if this yields a smaller proof term.
3. The local `simpa [hx]` is preferable to destructively rewriting `h.dvd_GN5`; the current form has good locality.
4. In the valuation layer, express the contradiction as $v_q(GN5)=1$ versus divisibility of the valuation by $5$ for a fifth power.
5. The theorem should not receive `[simp]`; broad automatic rewriting with a negated existential could create undesirable search behavior.

These include unverified design proposals. No Lean build comparison was performed.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. Directly, this theorem needs natural-number primality, divisibility, powers, existential witness extraction, and the semiring `ring` tactic.

The principal lemma and tactics are:

- `Nat.Prime.dvd_of_dvd_pow`
- `ring`
- `simpa`
- `rintro`
- `obtain`

The full `CleanChannel.lean` file also uses coprimality, `norm_num`, and concrete channel construction. Therefore the minimal import for this theorem alone need not equal the minimal import for the whole file. Narrowing to individual Mathlib modules may be possible but was not verified.

## Comparator challenge suitability

This theorem is a good Comparator challenge.

- the current witness-expansion proof using `ring`;
- a proof constructing $q^2∣x^5$ solely from `dvd_pow` lemmas;
- a proof using `Nat.factorization` or valuations;
- a general exponent-$n\ge2$ lemma followed by specialization;
- comparison against alternatives using `omega` or `norm_num`.

Useful comparison axes are proof-term size, import scope, ease of exponent generalization, error locality, and mathematical explanatory power. The current proof is strong because it exposes the elementary divisibility witness and directly displays the collision between local exponent one and a fifth power.

## Next theorem to read

Next is `DkMath.FLT.Five.not_fifth_power_body_of_clean`.

It consumes `dvd_body` and `not_sq_dvd_body` to prove

$$
¬\exists x\in\mathbb{N},\ g\,GN5(g,y)=x^5
$$

This moves from the obstruction for `GN5` alone to the obstruction for the full body occurring in the difference of fifth powers.

## Sources and distinction from inference

The theorem type, proof, declaration order, and later use were verified in the generated source for `DkMath/FLT/Five/CleanChannel.lean` embedded in `Flt5DkMath/FLT5StandAlone.lean`. Discussion of the theorem's role, redundancy, import minimization, generalization, and Comparator variants includes explanatory analysis or unverified proposals. Existing PDFs were treated as secondary narrative context, while the Lean source remained authoritative. No Lean build was run.
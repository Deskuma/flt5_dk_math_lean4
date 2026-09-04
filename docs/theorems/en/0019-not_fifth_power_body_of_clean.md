# 0019 — `not_fifth_power_body_of_clean`

> This document is the English translation of the Japanese canonical article.

## Lean type

```lean
theorem not_fifth_power_body_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, g * GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hx]
    exact h.dvd_body
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.not_sq_dvd_body
  rw [hx]
  use q ^ 3 * k ^ 5
  ring
```

The fully qualified name is `DkMath.FLT.Five.not_fifth_power_body_of_clean`.

## Mathematical statement

If `CleanGN5Channel g y q` holds, then the full body $g\,GN5(g,y)$ is not a perfect fifth power in the natural numbers.

$$
¬\exists x\in\mathbb{N},\ g\,GN5(g,y)=x^5
$$

The clean channel guarantees that the prime $q$ divides the full body while $q^2$ does not. Therefore the exponent of $q$ in the full body is exactly $1$. Every prime exponent in a perfect fifth power must be divisible by $5$, so exponent $1$ is incompatible with a fifth power.

## Role in the complete proof

This theorem is the main consumer that converts the local information in `CleanGN5Channel` into exclusion of a perfect fifth power for the full body appearing in the factorization of a difference of fifth powers.

The previous theorem `not_fifth_power_GN5_of_clean` treated `GN5(g,y)` alone. The present theorem extends the target to the product containing the gap factor $g$. It therefore uses the already constructed APIs

- `h.dvd_body : q ∣ g * GN5 g y`
- `h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y`

rather than only `h.dvd_GN5` and `h.noLift`.

Later in the FLT5 reduction, the factorization

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

is equal to the fifth power $x^5$. Once a suitable clean channel is supplied, this theorem yields the contradiction immediately. It is therefore the bridge from a local valuation-one certificate to a global impossibility of being a fifth power.

## Direct dependencies

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.CleanGN5Channel.dvd_body`
- `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body`
- the field `h.prime : Nat.Prime q`
- `Nat.Prime.dvd_of_dvd_pow`
- `rintro`
- `obtain`
- `rw`
- `ring`

The concrete polynomial definition of `GN5` is not unfolded. The proof needs only the divisibility API supplied by the clean channel.

## Proof flow

1. Assume that the full body equals the fifth power of some natural number $x$.
2. Use `h.dvd_body` and the equality `hx` to obtain $q∣x^5$.
3. By primality of $q$ and `Nat.Prime.dvd_of_dvd_pow`, obtain $q∣x$.
4. Write $x=qk$.
5. Apply `h.not_sq_dvd_body`, reducing the contradiction to proving that the full body is divisible by $q^2$.
6. Rewrite the full body to $(qk)^5$ using `hx`.
7. Give the explicit quotient $q^3k^5$ and prove

$$
(qk)^5=q^2\left(q^3k^5\right)
$$

with `ring`.
8. This contradicts `h.not_sq_dvd_body`.

## Lean-specific processing

```lean
rintro ⟨x, hx⟩
```

opens the negated existential statement in contradiction form and introduces both the witness $x$ and the equality `hx`.

```lean
have hqDivPow : q ∣ x ^ 5 := by
  rw [← hx]
  exact h.dvd_body
```

reverses the equality so that the target `x ^ 5` is rewritten back to the full body. The previous theorem used `simpa [hx] using h.dvd_GN5`; here the proof instead uses `rw [← hx]` together with the named API `h.dvd_body`.

```lean
obtain ⟨k, rfl⟩ := hqDivX
```

extracts a quotient $k$ from the divisibility proof and replaces $x$ by $qk$ in place. The final `use q ^ 3 * k ^ 5` supplies an explicit quotient for division by $q^2$. `ring` closes only the polynomial identity over the natural-number semiring; it performs no primality or divisibility reasoning.

## Redundancy and duplication

The proof skeleton is almost identical to `not_fifth_power_GN5_of_clean`. The difference lies in the target and in the local APIs consumed.

- The `GN5`-only theorem uses `h.dvd_GN5` and `h.noLift`.
- The full-body theorem uses `h.dvd_body` and `h.not_sq_dvd_body`.

Their common part could be extracted into a general lemma for any natural number $N$:

$$
q∣N\land q^2∤N \Longrightarrow ¬\exists x,\ N=x^5
$$

The current implementation nevertheless keeps the semantic target and dependency structure explicit in each theorem name, which improves local readability.

The explicit quotient `q ^ 3 * k ^ 5` also duplicates the preceding theorem. For a general exponent $n\ge2$, this could be abstracted using the quotient $q^{n-2}k^n$.

## Optimization candidates

1. Introduce a general lemma such as `prime_dvd_not_sq_dvd_not_pow` and derive both fifth-power exclusion theorems by specialization.
2. Generalize that lemma to every exponent $n\ge2`, potentially sharing it with local no-lift arguments for FLT3 and FLT7.
3. Compare the current `rw [← hx]; exact h.dvd_body` with `simpa [hx] using h.dvd_body` in proof-term size and error locality.
4. Replace the explicit witness after `obtain ⟨k, rfl⟩` with a composition of `dvd_pow` lemmas if a clearer library-level route exists.
5. In a valuation layer, express the contradiction as $v_q(g\,GN5)=1$ versus divisibility of the valuation of a fifth power by $5$.
6. The theorem should not receive `[simp]`; registering a negated existential globally offers little benefit and may make simplification less predictable.

These optimization proposals are unverified. No Lean build comparison was performed.

## Required Mathlib imports and import optimization

The standalone generated artifact uses `import Mathlib`. The theorem directly needs only:

- primality and divisibility for natural numbers,
- powers of natural numbers,
- `Nat.Prime.dvd_of_dvd_pow`,
- the tactics `rintro`, `obtain`, and `rw`,
- `ring` over a semiring.

The theorem itself does not use `omega`, `norm_num`, `Nat.factorization`, or p-adic valuation. A narrower set of Mathlib modules may suffice, but the whole file `CleanChannel.lean` also uses coprimality, concrete numerical evaluation, and `norm_num`. Therefore the smallest import set for this theorem alone need not equal the smallest import set for the complete file. Import minimization remains unverified.

## Comparator challenge suitability

This theorem is a good Comparator challenge.

Possible competing proofs include:

- the current elementary proof using an explicit divisibility witness and `ring`,
- first proving the general lemma $q∣N\land q^2∤N\Rightarrow N$ is not a fifth power and then specializing it,
- constructing $q^2∣x^5$ only through `dvd_pow` lemmas,
- using `Nat.factorization` and congruence conditions on prime exponents,
- using a valuation API to contradict exponent one with the exponent divisibility of a fifth power,
- comparing `rw [← hx]` with `simpa [hx] using ...`.

Useful comparison axes are proof-term size, import scope, generalizability, error locality, and mathematical transparency. The current proof is strong because it makes the local exponent-one contradiction visible using only elementary divisibility witnesses.

## Next theorem to read

The next declaration is `DkMath.FLT.Five.cleanGN5Channel_one_one_31`.

It constructs

$$
CleanGN5Channel(1,1,31)
$$

concretely, checking with `norm_num` that the prime $31$ occurs exactly once in $GN5(1,1)$ and does not divide the gap $1$. This moves from abstract clean-channel consumers to a concrete finite-prime escape provider.

## Sources versus interpretation

The theorem type, proof, declaration order, and directly used lemmas were verified in the generated source for `DkMath/FLT/Five/CleanChannel.lean` contained in `Flt5DkMath/FLT5StandAlone.lean`. The discussion of its role, duplication, generalization, import minimization, and Comparator alternatives includes explanatory analysis or unverified proposals. Existing PDFs were treated as supporting narrative context, while the Lean source remained primary. No Lean build was run.
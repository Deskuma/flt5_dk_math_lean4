# 0025 — `coprime_gap_GN5_of_coprime_of_five_not_dvd`

## Lean type

```lean
theorem coprime_gap_GN5_of_coprime_of_five_not_dvd
    {g y : ℕ} (hgy : Nat.Coprime g y) (h5g : ¬ 5 ∣ g) :
    Nat.Coprime g (GN5 g y)
```

For arbitrary natural numbers `g` and `y`, the theorem states that if `g` is coprime to `y` and the exceptional prime `5` does not divide `g`, then `g` is also coprime to `GN5 g y`.

## Mathematical statement

The assumptions are

$$
\gcd(g,y)=1,\qquad 5\nmid g.
$$

The conclusion is

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1.
$$

By the preceding lemma, any common prime divisor `q` of `g` and `GN5(g,y)` must satisfy

$$
q\mid 5y^4.
$$

Since `q` is prime,

$$
q\mid 5\qquad\text{or}\qquad q\mid y^4.
$$

In the first branch, `q=5`; together with `q ∣ g`, this gives `5 ∣ g`, contradicting the hypothesis. In the second branch, `q ∣ y`; together with `q ∣ g`, this contradicts the coprimality of `g` and `y`. Therefore no common prime divisor exists.

## Role in the complete proof

This theorem is the factor-separation principle for Branch B in the Reduction layer. For the fifth-power body

$$
g\,GN5(g,y),
$$

it guarantees that the two factors `g` and `GN5(g,y)` are coprime whenever the exceptional prime `5` does not enter the gap `g`.

That coprimality is later used to split a product known to be a fifth power into separate fifth powers. Thus the theorem is the bridge from congruence-based classification of common factors to decomposition of a coprime fifth-power product.

## Direct dependencies

- `GN5`
- `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`
- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`
- `Nat.gcd_dvd_right`
- `Nat.Prime.dvd_mul`
- `Nat.dvd_prime`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`

The central mathematical dependency is the routing lemma from the preceding article. The remaining dependencies are standard APIs for extracting a prime divisor from a nontrivial gcd and routing divisibility through products and powers.

## Proof flow

The Lean body is:

```lean
refine (Nat.coprime_iff_gcd_eq_one).2 ?_
by_contra hg
rcases Nat.exists_prime_and_dvd (n := Nat.gcd g (GN5 g y)) hg with
  ⟨q, hq, hqgcd⟩
have hqg : q ∣ g :=
  hqgcd.trans (Nat.gcd_dvd_left g (GN5 g y))
have hqGN : q ∣ GN5 g y :=
  hqgcd.trans (Nat.gcd_dvd_right g (GN5 g y))
have hq5y : q ∣ 5 * y ^ 4 :=
  dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5 hqg hqGN
rcases hq.dvd_mul.mp hq5y with hq5 | hqy4
· have hqeq : q = 5 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
  exact h5g (hqeq ▸ hqg)
· have hqy : q ∣ y := hq.dvd_of_dvd_pow hqy4
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy
```

1. Convert the `Nat.Coprime` goal into a gcd-equals-one goal.
2. Assume the gcd is not `1` and extract a prime `q` dividing it.
3. Use the standard gcd divisibility projections to obtain `q ∣ g` and `q ∣ GN5 g y`.
4. Apply the preceding lemma to obtain `q ∣ 5*y^4`.
5. Use prime divisibility of a product to split into `q ∣ 5` and `q ∣ y^4`.
6. In the first branch, prove `q=5` and contradict `¬ 5 ∣ g`.
7. In the second branch, prove `q ∣ y` and contradict `Nat.Coprime g y`.

## Lean-specific processing

`Nat.exists_prime_and_dvd` extracts a prime divisor from the assumption that `Nat.gcd g (GN5 g y) ≠ 1`. The library theorem handles the required nontriviality conditions, including edge cases in which the gcd could be zero.

`hq.dvd_mul.mp hq5y` is Euclid's lemma for a prime divisor of a product. Since the second factor is `y ^ 4`, `hq.dvd_of_dvd_pow` then lowers divisibility from the power to the base `y`.

The step from `q ∣ 5` to `q=5` is slightly delicate. `Nat.dvd_prime` yields the alternatives `q=1 ∨ q=5`, so `hq.ne_one` removes the first branch. The proposition `Nat.Prime 5` is supplied by `by decide`.

`hqeq ▸ hqg` rewrites the divisibility fact `q ∣ g` along `q=5`, producing `5 ∣ g`.

## Redundancy and duplication

The derivations of `hqg` and `hqGN` are symmetric: each composes `hqgcd` with one standard gcd projection. They could be packaged into a local pair-producing helper, but the current two lines keep the correspondence with the standard API explicit.

The proof of `q=5` is longer than the mathematical sentence. A DkMath-specific helper such as

```lean
have hqeq : q = 5 := hq.eq_five_of_dvd hq5
```

could improve readability, but adding an abstraction for a single use may be excessive.

## Optimization candidates

- The standard gcd contradiction pattern may be replaceable with a direct characterization of `Nat.Coprime` by absence of common prime divisors.
- The `q ∣ 5` branch could be extracted into a small local lemma so that the main proof exposes the two mathematical branches more clearly.
- The theorem can be generalized to a prime `p` and a remainder term `p*y^n`, but the current specialized declaration is appropriate for reading the `GN5` reduction.
- An alternative proof could first establish common-prime exclusion and then convert that statement to `Nat.Coprime` at the end.

These are unverified refactoring proposals; no Lean build was run for this article.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem directly uses APIs for natural-number gcd, coprimality, primes, divisibility, and powers, together with the DkMath declarations `GN5` and the preceding routing lemma.

The exact minimal import set has not been build-verified. It may be possible to replace `Mathlib` with individual modules for natural-number primes, gcd, and divisibility. The theorem body itself does not use `ring`, `omega`, or `norm_num`; it uses `decide` only to discharge the concrete primality of `5`. File-level import minimization must nevertheless account for neighboring declarations in `Reduction.lean`.

## Comparator challenge suitability

This theorem is highly suitable for a Comparator challenge. The statement is compact, while the proof offers clear alternatives:

- the current gcd contradiction with prime extraction;
- a direct prime-divisor characterization of coprimality;
- a proof organized around `%` and congruences;
- numerical normalization versus structural use of `Nat.dvd_prime` in the `q ∣ 5` branch;
- a readability-oriented decomposition into small lemmas versus a compressed term proof.

Useful evaluation criteria are whether the preceding API is reused, whether the exceptional prime `5` remains explicit, whether the coprimality contradiction is easy to audit, and whether dependence on concrete-number tactics is minimized.

## Evidence and inference

The theorem type, proof body, declaration order, and the immediately following theorem `branchB_coprime_gap_GN5` are grounded in the generated `DkMath/FLT/Five/Reduction.lean` section of `Flt5DkMath/FLT5StandAlone.lean` in the repository.

The existing Japanese and English PDFs provide narrative context for the complete FLT5 proof, but the Lean source is the final formal authority for this local theorem. An independent detailed discussion of this exact declaration name was not confirmed in the PDFs during this article; the role described above is inferred from the Lean declaration order and downstream use. Import minimization and generalization proposals are unverified.

## Next theorem to read

`DkMath.FLT.Five.branchB_coprime_gap_GN5`

It combines

$$
\gcd(z-y,y)=1
$$

from `CounterexamplePack` with the Branch B hypothesis

$$
5\nmid z-y
$$

and applies the present theorem to obtain

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1.
$$

This is a thin connection theorem specializing the general factor-separation principle to the actual gap coordinates of an FLT5 counterexample candidate.

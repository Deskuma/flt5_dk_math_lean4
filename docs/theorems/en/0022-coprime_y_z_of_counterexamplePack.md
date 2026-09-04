# 0022 — `coprime_y_z_of_counterexamplePack`

## Lean type

```lean
theorem coprime_y_z_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime y z
```

The theorem derives coprimality of the second base `y` and the result base `z` from `CounterexamplePack x y z`.

## Mathematical statement

Suppose positive natural numbers satisfy

$$
x^5+y^5=z^5
$$

and $\gcd(x,y)=1$. Then

$$
\gcd(y,z)=1.
$$

Indeed, if a prime $q$ divided both `y` and `z`, the equation would imply $q\mid x^5`; primality would then give $q\mid x`, contradicting the primitivity condition $\gcd(x,y)=1$.

## Role in the complete proof

This theorem recovers a new coprimality fact forced by the equation from the input assumption `Nat.Coprime x y`. It is the basis for the following theorem proving coprimality of the gap $g=z-y$ and `y`. That fact enters the Reduction layer, where common prime divisors of `GN5(g,y)` and the gap are restricted to the exceptional prime $5$.

## Direct dependencies

- `CounterexamplePack` and its fields `hEq`, `hxy`
- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`
- `dvd_pow_self`
- `Nat.dvd_add_left`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`

## Proof flow

1. Convert `Nat.Coprime y z` into `Nat.gcd y z = 1`.
2. Assume the gcd is not $1$ and choose a prime $q$ dividing it.
3. Derive $q\mid y$ and $q\mid z`, then lift both divisibilities to fifth powers.
4. Use $x^5+y^5=z^5$ to derive $q\mid x^5$.
5. Use primality to obtain $q\mid x$.
6. The common prime divisor of `x` and `y` contradicts `hPack.hxy`.

The central Lean segment is:

```lean
have hqsum : q ∣ x ^ 5 + y ^ 5 := by
  rw [hPack.hEq]
  exact hqzp
exact (Nat.dvd_add_left hqyp).mp hqsum
```

## Lean-specific processing

After `by_contra hg`, the hypothesis `hg` has type `Nat.gcd y z ≠ 1`. `Nat.exists_prime_and_dvd` supplies a prime divisor of the non-unit gcd. Lifting divisibility to fifth powers uses `dvd_pow_self` with the nonzero-exponent proof `(by decide : 5 ≠ 0)`.

`Nat.dvd_add_left hqyp` is used as an elimination API: under $q\mid y^5`, divisibility of $x^5+y^5$ is converted into divisibility of $x^5$. Finally, `Nat.not_coprime_of_dvd_of_dvd` turns the common prime divisor into non-coprimality and contradicts `hPack.hxy`.

## Redundancy and duplication

The constructions of `hqyp` and `hqzp` are structurally identical. They nevertheless serve different later roles—the former removes an additive term while the latter rewrites the equation's right-hand side—so keeping separate names improves readability.

Although `hPack.hEq` has the defined proposition `Fermat5Equation`, `rw [hPack.hEq]` works directly; no explicit `unfold Fermat5Equation` is needed here.

## Optimization candidates

- The argument may be generalized to a lemma saying that $a^n+b^n=c^n$ and `Coprime a b` imply `Coprime b c`. The required positivity/nonzero condition on the exponent and the best existing Mathlib API must be checked; this proposal is unverified.
- A version using `dvd_pow`-family lemmas instead of `dvd_pow_self` could be compared, although the current code is explicit and clear.
- Compression into a term proof is possible, but it would obscure the prime-divisor contradiction; the current staged proof is preferable for museum exposition.

## Required Mathlib imports and import optimization

The generated standalone source uses only `import Mathlib`. The observable functional dependencies are Mathlib APIs for natural-number gcd, primes, divisibility, and powers, together with the preceding module defining `CounterexamplePack`.

The minimal import line of the original split `Reduction.lean` module cannot be reconstructed from the generated standalone source. A likely optimization is to import `DkMath.FLT.Five.Basic` plus focused Mathlib modules for gcd, primes, and divisibility. The exact minimal set remains an unverified proposal requiring import auditing and a build check.

## Comparator challenge suitability

This theorem is well suited to a Comparator challenge. Candidate approaches include:

- the current prime-divisor contradiction proving the gcd is $1$;
- a proof driven by coprimality transfer/elimination lemmas;
- a generalized proof for an arbitrary positive exponent.

Useful comparison criteria are lemma count, number of explicit divisibility intermediates, dependence on specialized Mathlib APIs, generalizability, and readability.

## Sources and explicit conjectures

The theorem type, proof body, declaration order, and Reduction-layer description are grounded in `Flt5DkMath/FLT5StandAlone.lean` in the repository. Import minimization and abstraction to a general exponent are unverified optimization proposals. The existing PDFs provide mathematical context for the whole proof, while the Lean source is the formal authority for this article.

## Next theorem to read

`DkMath.FLT.Five.coprime_gap_y_of_counterexamplePack`

It transports the newly obtained `Nat.Coprime y z` to the difference $z-y$ and establishes

$$
\gcd(z-y,y)=1.
$$
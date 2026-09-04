# 0024 — `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`

## Lean type

```lean
theorem dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
    {g y q : ℕ} (hqg : q ∣ g) (hqGN : q ∣ GN5 g y) :
    q ∣ 5 * y ^ 4
```

For arbitrary natural numbers `g`, `y`, and `q`, if `q` divides both the gap `g` and `GN5 g y`, then `q` also divides the exceptional term `5 * y ^ 4`. The theorem itself assumes neither that `q` is prime nor that `g` and `y` are coprime.

## Mathematical statement

Use the previously established gap decomposition

$$
GN5(g,y)=g\left(g^3+5g^2y+10gy^2+10y^3\right)+5y^4.
$$

If `q ∣ g`, then the entire first term is divisible by `q`. Since `q ∣ GN5(g,y)` as well, removing that first summand from the divisible sum shows that the remainder is divisible by `q`:

$$
q\mid 5y^4.
$$

Thus the theorem extracts, for an arbitrary common divisor `q`, the divisibility content of the congruence

$$
GN5(g,y)\equiv 5y^4\pmod g.
$$

## Role in the complete proof

This theorem is the congruence-analysis entry point in the Reduction layer for restricting common divisors of the gap and `GN5` to the exceptional prime `5`.

In the following theorem, `coprime_gap_GN5_of_coprime_of_five_not_dvd`, one assumes that the gcd of `g` and `GN5(g,y)` has a prime divisor `q`. The present theorem yields `q ∣ 5y^4`, and primality then gives two branches.

1. If `q ∣ 5`, then `q=5`, contradicting `¬ 5 ∣ g`.
2. If `q ∣ y^4`, then `q ∣ y`, contradicting `Nat.Coprime g y`.

Therefore, when `g` and `y` are coprime and `5 ∤ g`, the gap and `GN5` are coprime. The present theorem is the local routing lemma that fixes the only possible destinations of a common prime: the factor `5` or the coordinate `y`.

## Direct dependencies

- `GN5`
- `GN5_eq_gap_mul_add_five_mul_y_pow_four`
- `dvd_mul_of_dvd_left`
- `Nat.dvd_add_right`

The mathematical core is `GN5_eq_gap_mul_add_five_mul_y_pow_four`. The remaining lemmas are standard natural-number divisibility APIs for lifting divisibility into a product and removing a known divisible summand from a sum.

## Proof flow

The Lean proof is:

```lean
have hdecomp :
    GN5 g y =
      g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) +
        5 * y ^ 4 := by
  exact GN5_eq_gap_mul_add_five_mul_y_pow_four g y
have hqPrefix :
    q ∣ g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) :=
  dvd_mul_of_dvd_left hqg _
rw [hdecomp] at hqGN
exact (Nat.dvd_add_right hqPrefix).mp hqGN
```

1. Fix the existing decomposition under the local name `hdecomp`.
2. Lift `q ∣ g` to divisibility of the entire polynomial prefix using `dvd_mul_of_dvd_left`.
3. Rewrite `GN5 g y` inside `hqGN` into the decomposed form.
4. Use the forward direction of `Nat.dvd_add_right hqPrefix` to extract divisibility of the right summand `5*y^4`.

## Lean-specific processing

`Nat.dvd_add_right hqPrefix` returns an equivalence of the form

```lean
q ∣ a + b ↔ q ∣ b
```

when divisibility of the left summand is already known. Here `.mp` transforms the rewritten hypothesis `hqGN : q ∣ prefix + 5*y^4` into the goal.

Introducing `hdecomp` may look mathematically redundant, but it makes the rewrite target explicit and keeps `rw [hdecomp] at hqGN` stable. In `dvd_mul_of_dvd_left hqg _`, the underscore asks Lean to infer the second factor from the expected type.

The proof avoids subtraction entirely and removes the prefix by a divisibility equivalence for addition. This is especially robust over natural numbers because it avoids truncated subtraction.

## Redundancy and duplication

`hdecomp` merely restates an existing theorem. A shorter version is possible:

```lean
rw [GN5_eq_gap_mul_add_five_mul_y_pow_four] at hqGN
exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hqg _)).mp hqGN
```

However, with a long polynomial expression, the intermediate name `hqPrefix` improves auditability. The current proof favors transparency over minimum line count, and its actual duplication is small.

The theorem name is long, but it states all hypotheses and the conclusion explicitly. A namespace-based name such as `GN5.dvd_exceptional_term` could be shorter, at the cost of less explicit global searchability.

## Optimization candidates

- Merge `hdecomp` into a direct rewrite to shorten the proof.
- Abstract a general lemma saying that if `n = g*A+r`, `q∣g`, and `q∣n`, then `q∣r`. In practice, `Nat.dvd_add_right` already supplies almost all of this abstraction, so a DkMath-specific wrapper may add little value.
- Add a remainder-form API such as `GN5 g y % g = (5*y^4) % g` if later developments become congruence-centered. For the present prime-divisor contradiction, the divisibility theorem is more direct.
- Keep `q` general rather than adding `Nat.Prime q`; the current type is more reusable and the later theorem supplies primality only where needed.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present theorem directly needs natural-number powers, addition, multiplication, divisibility, `dvd_mul_of_dvd_left`, `Nat.dvd_add_right`, and the DkMath declarations `GN5` and its gap decomposition.

The exact minimal import set for the original split module was not build-tested for this article. It may be possible to replace `Mathlib` with focused modules for natural-number divisibility and elementary algebra, but this remains an unverified import-optimization proposal. The theorem itself does not directly use `ring` or `omega`, although `ring` is used to prove the decomposition on which it depends.

## Comparator challenge suitability

This theorem is suitable for a small and clear Comparator challenge.

Possible competitors are:

- the current structural proof using `Nat.dvd_add_right`;
- a witness-expansion proof that constructs every divisibility witness explicitly;
- a proof that passes through `%` congruences and then returns to divisibility;
- the audit-oriented version with `hdecomp` and `hqPrefix` versus a compressed two-line version.

Evaluation criteria include avoidance of natural-number subtraction, appropriate reuse of existing APIs, readability in the presence of a long polynomial, and ease of connection to the following prime-factor split. Witness-expansion and remainder-based proofs are likely to be more complicated than the current proof.

## Sources and distinction from conjecture

The theorem type, proof body, declaration order, and its immediate use in `coprime_gap_GN5_of_coprime_of_five_not_dvd` are taken from the generated `DkMath/FLT/Five/Reduction.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` in the repository.

The existing Japanese and English PDFs provide narrative context for the complete FLT5 proof, while the formal basis of this article is the Lean source. Import minimization, namespace redesign, and a remainder-form API are unverified proposals.

## Next theorem to read

`DkMath.FLT.Five.coprime_gap_GN5_of_coprime_of_five_not_dvd`

Under

$$
\gcd(g,y)=1,\qquad 5\nmid g,
$$

it proves

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1.
$$

It passes the result `q ∣ 5y^4` from this article into the prime-divides-product split and eliminates both possible sources of a common prime, namely `5` and `y`.
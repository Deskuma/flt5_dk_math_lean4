# 0085 — `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5`

## Lean type

```lean
theorem SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (5 ^ 15 * s.a ^ 20) (s.b ^ 5) := by
  have h5b : Nat.Coprime 5 s.b :=
    (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr s.five_not_dvd_b
  have hscaled : Nat.Coprime (5 ^ 15) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 15 h5b).pow_right 5
  have hab : Nat.Coprime (s.a ^ 20) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 20 s.coprime_a_b).pow_right 5
  exact hscaled.mul_left hab
```

## Mathematical statement

From the facts stored by `SignedFiveAdicPowerSplit`,

$$
\gcd(a,b)=1,
$$

and from 0084,

$$
5\nmid b,
$$

this theorem proves that the enlarged factors needed later,

$$
5^{15}a^{20}
\quad\text{and}\quad
b^5,
$$

are coprime; equivalently,

$$
\gcd(5^{15}a^{20},b^5)=1.
$$

The exponents 15, 20, and 5 are not new arithmetic information derived by this theorem. They are the exponents required by the later ramifier-stripped square / golden factorization.

## Role in the overall proof

Article 0083 established the power split

$$
\mathrm{carrier}=5^4a^5,\qquad
\mathrm{residual}=5b^5,\qquad
\gcd(a,b)=1,
$$

and 0084 established $5\nmid b$. This theorem lifts those two local coprimality facts to the high-power product actually consumed later.

The proof flow is therefore

$$
\gcd(a,b)=1,\ 5\nmid b
\Longrightarrow
\gcd(5^{15},b^5)=1,\ \gcd(a^{20},b^5)=1
\Longrightarrow
\gcd(5^{15}a^{20},b^5)=1.
$$

Thus later factorizations may treat the $5$-power and the $a$-power as a single left factor without introducing any new common divisor with the right factor $b^5$.

## Direct dependencies

- `SignedFiveAdicPowerSplit`
  - especially `s.coprime_a_b : Nat.Coprime s.a s.b`
- `SignedFiveAdicPowerSplit.five_not_dvd_b`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.pow_right`
- `Nat.Coprime.mul_left`
- `decide`
  - used to discharge `Nat.Prime 5`

The theorem does not directly inspect carrier/residual equations or the mod-25 data of `SignedFiveAdicPacket`; those facts have already been compressed into `s.coprime_a_b` and `s.five_not_dvd_b` by 0083–0084.

## Proof flow

1. Use `s.five_not_dvd_b` together with primality of 5 to obtain

$$
\gcd(5,b)=1.
$$

2. Apply `pow_left 15` and `pow_right 5` to obtain

$$
\gcd(5^{15},b^5)=1.
$$

3. Apply `pow_left 20` and `pow_right 5` to `s.coprime_a_b` to obtain

$$
\gcd(a^{20},b^5)=1.
$$

4. Use `hscaled.mul_left hab` to multiply the two left factors, preserving coprimality with the common right factor $b^5$:

$$
\gcd(5^{15}a^{20},b^5)=1.
$$

## Lean-specific processing

The expression

```lean
(show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr s.five_not_dvd_b
```

constructs a proof that 5 is prime via `decide`, then uses the prime API to convert `¬ 5 ∣ b` into `Nat.Coprime 5 b`.

`Nat.Coprime.pow_left` and `pow_right` preserve coprimality through powers without expanding gcds explicitly. Consequently this proof needs neither prime factorization nor gcd computation, and it uses neither `omega` nor `ring`.

Finally,

```lean
exact hscaled.mul_left hab
```

uses closure of `Nat.Coprime` under multiplication on the left. Since both intermediate facts share the same right factor, Lean can combine them directly.

## Redundancy and duplication

The theorem is already short, so there is little local redundancy. However, the pattern

```lean
(Nat.Coprime.pow_left n h).pow_right m
```

may recur in later high-power factorizations.

The exponents 15, 20, and 5 are also hard-coded here, making this theorem application-specific. Its mathematical core is the more general pattern

$$
\gcd(p,b)=1,\quad\gcd(a,b)=1
\Longrightarrow
\gcd(p^r a^s,b^t)=1.
$$

The present theorem is the specialization $p=5$, $r=15$, $s=20$, $t=5$.

## Optimization candidates

A reusable helper could have the conceptual form

```lean
-- conceptual shape
theorem coprime_mul_powers
    (hpb : Nat.Coprime p b)
    (hab : Nat.Coprime a b) :
    Nat.Coprime (p ^ r * a ^ s) (b ^ t) := ...
```

If this pattern appears multiple times later, such a helper would reduce exponent-manipulation boilerplate. For this single occurrence, however, the current four-line proof may be clearer because it exposes the intended factors directly.

Another possible API optimization would be to expose `Nat.Coprime 5 b` as a companion theorem or stored field immediately after `five_not_dvd_b`. Whether that is worthwhile depends on reuse frequency; `¬ 5 ∣ b` is itself the more direct arithmetic obstruction.

## Required Mathlib imports and import optimization

The standalone artifact on the target branch is built with `import Mathlib`, and its manifest places this declaration in `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`.

The proof directly needs the `Nat.Prime` / `Nat.Coprime` bridge between primality and divisibility, the power/product coprimality API, and `decide`. It does not use `ring` or `omega`.

Therefore importing all of `Mathlib` is clearly broader than necessary for this theorem alone. However, the exact import list of the split source module was not independently confirmed on this museum branch, so this article does not assert a specific minimal import set. Import optimization should first inspect the source module's import graph and then be verified with a Lean build. No Lean build is performed in this run.

## Comparator challenge suitability

Yes. This is better suited to API comparison than to hard proof search.

Three candidate approaches are:

1. the current `Nat.Coprime.pow_left` / `pow_right` / `mul_left` construction;
2. proving a generic `coprime_mul_powers` helper first and specializing it;
3. a lower-level proof via gcd or prime-factor characterizations.

Useful comparison axes are proof length, type-inference stability, reuse, required imports, and API consistency with subsequent theorems. The current proof is a good baseline because it uses Mathlib's high-level `Nat.Coprime` API directly.

## PDF correspondence

The existing Japanese and English PDFs remain narrative sources for this museum, but the GitHub code-search endpoint returned a 502 upstream error in this run, so a unique PDF location for this short lemma could not be confirmed. No page number, section number, or PDF-specific claim is therefore guessed.

The formal source of truth for the statement and proof is the actual declaration in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next theorem to read

The next declaration is

```lean
theorem SignedFiveAdicPowerSplit.coprime_b5_scaled_a20
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (s.b ^ 5) (5 ^ 15 * s.a ^ 20) :=
  s.coprime_scaled_a20_b5.symm
```

It is the symmetric companion of the present theorem. The mathematical information is identical, but the later API requires $b^5$ as the left factor, so this one-line adapter supplies the needed argument orientation. It is a typical Lean formalization pattern in which an already-proved mathematical fact is restated with the argument order expected downstream.

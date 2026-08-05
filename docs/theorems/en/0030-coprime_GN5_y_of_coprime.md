# 0030 — `coprime_GN5_y_of_coprime`

## 1. Exhibit

```lean
theorem coprime_GN5_y_of_coprime
    {g y : ℕ} (hgy : Nat.Coprime g y) :
    Nat.Coprime (GN5 g y) y := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hgcd
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd (GN5 g y) y) hgcd with
    ⟨q, hq, hqgcd⟩
  have hqGN : q ∣ GN5 g y :=
    hqgcd.trans (Nat.gcd_dvd_left (GN5 g y) y)
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_right (GN5 g y) y)
  have hdecomp :
      GN5 g y =
        g ^ 4 +
          y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) := by
    unfold GN5
    ring
  have hqTail :
      q ∣ y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) :=
    dvd_mul_of_dvd_left hqy _
  rw [hdecomp] at hqGN
  have hqg4 : q ∣ g ^ 4 := (Nat.dvd_add_left hqTail).mp hqGN
  have hqg : q ∣ g := hq.dvd_of_dvd_pow hqg4
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy
```

The fully qualified declaration name is `DkMath.FLT.Five.coprime_GN5_y_of_coprime`.

## 2. Lean type

```lean
{g y : ℕ} → Nat.Coprime g y → Nat.Coprime (GN5 g y) y
```

The input is coprimality of the gap coordinate $g$ and the second coordinate $y$. The output is coprimality of the residual kernel `GN5 g y` and $y$. No positivity assumption and no condition $5\nmid g$ are required.

## 3. Mathematical statement

$$
\gcd(g,y)=1 \Longrightarrow \gcd\bigl(GN5(g,y),y\bigr)=1.
$$

Rearranging the definition of `GN5` so that the multiple of $y$ is visible gives

$$
GN5(g,y)=g^4+y\left(5g^3+10g^2y+10gy^2+5y^3\right).
$$

Hence modulo $y$,

$$
GN5(g,y)\equiv g^4\pmod y.
$$

If a prime $q$ divides both `GN5(g,y)` and $y$, the congruence gives $q\mid g^4$, and primality gives $q\mid g$. Together with $q\mid y$, this contradicts $\gcd(g,y)=1$.

## 4. Role in the complete proof

This theorem is placed at the entrance of `NormalForm.lean`. It transfers primitivity in local gap coordinates to the `GN5` side.

The preceding Reduction layer established the Branch-B coprimality

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1.
$$

The present theorem establishes the different relation

$$
\gcd\bigl(GN5(g,y),y\bigr)=1.
$$

These statements are not interchangeable. Later normal-form structures and factorization arguments need `GN5` to share no prime factor not only with the gap but also with $y$, so that primitivity is preserved across the coordinates.

## 5. Direct dependencies

### Repository declarations

- `DkMath.FLT.Five.GN5`

The proof does not directly reuse an existing named decomposition theorem. Instead, it unfolds `GN5` and proves the dedicated remainder decomposition modulo $y$ locally.

### Mathlib

- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`
- `Nat.gcd_dvd_right`
- `dvd_mul_of_dvd_left`
- `Nat.dvd_add_left`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `ring`

## 6. Proof flow

1. Convert `Nat.Coprime (GN5 g y) y` into the assertion that the gcd is $1$.
2. Assume the gcd is not $1$.
3. Use `Nat.exists_prime_and_dvd` to choose a prime divisor $q$ of that gcd.
4. Project the gcd divisibility to obtain $q\mid GN5(g,y)$ and $q\mid y$.
5. Expand `GN5` in the form

$$
GN5(g,y)=g^4+yT(g,y).
$$

6. From $q\mid y$, obtain $q\mid yT(g,y)$.
7. Remove the known tail from $q\mid GN5(g,y)$ and derive $q\mid g^4$.
8. Since $q$ is prime, derive $q\mid g$.
9. The divisibilities $q\mid g$ and $q\mid y$ contradict the input `hgy`.

## 7. Lean-specific processing

### From `Coprime` to a gcd contradiction

```lean
refine (Nat.coprime_iff_gcd_eq_one).2 ?_
by_contra hgcd
```

Rather than destructing `Nat.Coprime` directly, the proof follows Mathlib's route: if the gcd is not $1$, choose a prime divisor of it.

### Routing a gcd divisor to both arguments

```lean
hqgcd.trans (Nat.gcd_dvd_left (GN5 g y) y)
hqgcd.trans (Nat.gcd_dvd_right (GN5 g y) y)
```

The proof composes `hqgcd : q ∣ gcd ...` with the standard divisibility projections using transitivity.

### Extracting the remainder without subtraction

```lean
have hqg4 : q ∣ g ^ 4 := (Nat.dvd_add_left hqTail).mp hqGN
```

The proof does not write `GN5 - tail` over natural numbers. It uses the divisibility equivalence for addition to isolate $g^4$, avoiding order obligations caused by truncated subtraction.

### Descending from a power to its base

```lean
have hqg : q ∣ g := hq.dvd_of_dvd_pow hqg4
```

The general prime-divides-a-power lemma avoids expanding the fourth power into repeated products.

## 8. Redundancy and duplication

The local block

```lean
have hdecomp :
    GN5 g y = g ^ 4 + y * (...) := by
  unfold GN5
  ring
```

is mathematically natural, but it reconstructs a congruence decomposition of `GN5` inside the proof. The earlier theorem `GN5_eq_g_pow_four_add_five_mul` also separates $g^4$ from a multiple, but its tail is exposed as a multiple of $5$, not directly as a multiple of $y$. Therefore the current proof is not merely a duplicate of that theorem.

Still, the congruence `GN5(g,y) ≡ g^4 (mod y)` has clear reuse value. If no named lemma exists for it, this local derivation is a candidate for extraction.

## 9. Optimization candidates

### Candidate A: name the remainder decomposition modulo $y$

```lean
theorem GN5_eq_g_pow_four_add_y_mul (g y : ℕ) :
    GN5 g y = g ^ 4 +
      y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) := by
  unfold GN5
  ring
```

This separates polynomial normalization from the coprimality argument and makes the decomposition reusable in later congruence lemmas.

### Candidate B: use gcd invariance under adding a multiple

If a suitable Mathlib lemma is available, one could rewrite

$$
\gcd(g^4+yT,y)=\gcd(g^4,y)
$$

and finish from `hgy.pow_left 4`. The exact lemma name and orientation over natural-number addition have not been verified.

### Candidate C: factor out the common prime-divisor contradiction pattern

The pattern “assume the gcd is not one, choose a common prime divisor, and collide it with the input `Coprime`” occurs elsewhere in the development. A small local abstraction or a more direct gcd API might shorten the proof, although excessive abstraction could reduce readability.

## 10. Required Mathlib imports and import optimization

The standalone file uses `import Mathlib`, so this article alone does not establish the exact minimal imports.

The proof requires at least the following areas:

- natural-number gcd, coprimality, primality, and divisibility;
- prime divisibility of powers;
- `ring` normalization over a commutative semiring.

A plausible reduced import set would combine the relevant gcd/prime-divisibility modules with `Mathlib.Tactic.Ring`. Exact module names and transitive closure must be checked by a Lean build, so this remains an unverified optimization proposal.

## 11. Comparator challenge suitability

This theorem is well suited to a Comparator challenge.

### Challenge

From the definition of `GN5` and `hgy : Nat.Coprime g y`, prove

```lean
Nat.Coprime (GN5 g y) y
```

### Comparison axes

- the current common-prime-divisor contradiction;
- a version using a named remainder decomposition modulo $y$;
- a shorter gcd-invariance proof;
- number of `ring` invocations;
- whether natural-number subtraction is avoided;
- minimal imports.

The theorem has a small type and visibly different proof strategies, making it a good comparator target.

## 12. Verified facts and interpretation

Verified facts:

- The theorem type, proof body, and declaration order come from the generated standalone Lean source in the repository.
- The theorem appears at the entrance of the generated `NormalForm.lean` section.
- The next declaration is `BranchBFifthPowerNormalForm`.

Interpretation and unverified proposals:

- extracting the remainder decomposition modulo $y$ as a separate theorem;
- shortening the proof with gcd invariance;
- reducing the Mathlib imports.

The existing Japanese and English PDFs serve as narrative context for the complete proof. The Lean source remains the final authority for the declaration type and proof.

## 13. Next declaration

The next declaration is

```lean
DkMath.FLT.Five.BranchBFifthPowerNormalForm
```

It packages the coprimality established here, together with the other Branch-B conclusions, into an exact `Prop` normal form that downstream proofs can consume.
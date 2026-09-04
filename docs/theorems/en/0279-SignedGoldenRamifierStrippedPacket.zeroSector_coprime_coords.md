# 0279 — `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords`

## Declaration kind

This is a **`theorem`**.

It proves that the two integer coordinates of the zero-sector fifth-power base `gamma : GoldenInt` are primitive, expressed as coprimality of their natural absolute values.

## Lean type

```lean
/-- The two integer coordinates of a zero-sector fifth-power base are primitive. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqr, hqs⟩
  have hqrZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqr
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqrZ (by decide))
      (dvd_mul_of_dvd_left hqrZ gamma.snd)) (dvd_pow hqsZ (by decide))
  have hqb : q ∣ p.exceptional.powerSplit.b := by
    rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
    · rw [hn] at hqNormZ
      exact_mod_cast hqNormZ
    · rw [hn] at hqNormZ
      exact_mod_cast (Int.dvd_neg.mp hqNormZ)
  have hprod := p.zeroSector_natAbs_product_eq hbeta
  have hqRhs : q ∣ 5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hqs _
  rcases hqPrime.dvd_mul.mp hqRhs with hq5pow | hqapow
  · have hq5 : q ∣ 5 := hqPrime.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left
        hqPrime.ne_one
    exact p.five_not_dvd_b (hqeq ▸ hqb)
  · have hqa : q ∣ p.exceptional.powerSplit.a :=
      hqPrime.dvd_of_dvd_pow hqapow
    exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqa hqb)
      p.exceptional.powerSplit.coprime_a_b
```

Writing `gamma = (r,s)` and abbreviating the packet power-split coordinates by `(a,b)`, the statement is

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
\gcd(|r|,|s|)=1.
$$

Lean expresses this primitive-coordinate condition as

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

so the integer coordinates are transported to natural numbers through `Int.natAbs`.

## Mathematical meaning

The proof is by contradiction. Assume that `r` and `s` share a prime divisor `q`:

$$
q\mid r,
\qquad
q\mid s.
$$

Then every term of the golden norm

$$
N(r,s)=r^2+rs-s^2
$$

is divisible by `q`, hence

$$
q\mid N(\gamma).
$$

By 0273 `zeroSector_gamma_norm_eq_or_eq_neg`,

$$
N(\gamma)=b
\quad\text{or}\quad
N(\gamma)=-b,
$$

so in either sign branch

$$
q\mid b.
$$

On the other hand, 0278 `zeroSector_natAbs_product_eq` gives

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

Since `q | |s|`, we obtain

$$
q\mid 5^6a^{10}.
$$

Because `q` is prime,

$$
q\mid 5^6
\quad\text{or}\quad
q\mid a^{10}.
$$

In the first branch, `q | 5`, hence `q=5`; together with `q | b`, this contradicts the packet field `five_not_dvd_b : ¬ 5 ∣ b`.

In the second branch, primality gives `q | a`. Combined with `q | b`, this contradicts `p.exceptional.powerSplit.coprime_a_b`.

Therefore no common prime divisor exists and the coordinates are coprime.

## Role in the whole proof

The zero-sector descent ultimately needs to split the second-coordinate product into

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Before proving that `s` is coprime to the quartic factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
$$

one first needs the primitive-coordinate statement for the fifth-power base itself.

The next theorem, 0280 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`, uses this result directly. If a prime `q` divided both `s` and `H(r,s)`, then the shape of `H(r,s)-r^4` would imply `q | r^4`, hence `q | r`, contradicting the present theorem.

Thus the dependency chain is

$$
\text{0273, 0278 + packet coprimality}
\longrightarrow
\text{0279: }\gcd(|r|,|s|)=1
\longrightarrow
\text{0280: }\gcd(|s|,|H|)=1
\longrightarrow
\text{tenth-power split}.
$$

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket`

The main input structure. This theorem uses, in particular:

- `p.exceptional.powerSplit.a`
- `p.exceptional.powerSplit.b`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

### `GoldenInt`

The golden-order element carrying the two integer coordinates `gamma.fst` and `gamma.snd`.

### `goldenNorm`

In the canonical source it has the coordinate expression

$$
N(r,s)=r^2+rs-s^2.
$$

The proof unfolds this representation with `simp only [goldenNorm]`.

### 0273 `zeroSector_gamma_norm_eq_or_eq_neg`

Provides `goldenNorm gamma = ±b`, allowing the common prime `q` to be transferred to the packet coordinate `b`.

### 0278 `zeroSector_natAbs_product_eq`

Provides

$$
|s|\,|H|=5^6a^{10},
$$

which transfers the prime divisor of `s` to the right-hand side.

### `Nat.Prime.not_coprime_iff_dvd`

Turns failure of `Nat.Coprime` into an explicit common prime witness `q` together with the two divisibility proofs.

### `Int.natCast_dvd`

Bridges natural-number divisibility of `natAbs` with integer divisibility of the corresponding signed coordinate.

### `Nat.Prime.dvd_mul` and `Nat.Prime.dvd_of_dvd_pow`

Split a prime divisor of a product and then descend divisibility through powers to the underlying base.

### `Nat.dvd_prime`

From `q | 5` and primality of 5, gives `q = 1 ∨ q = 5`; primality of `q` excludes the first branch.

### `Nat.not_coprime_of_dvd_of_dvd`

Turns `q | a`, `q | b`, and `1 < q` into a contradiction with the packet's `Nat.Coprime a b` field.

## Proof flow

### 1. Negate coprimality and obtain a common prime

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqr, hqs⟩
```

This gives

```lean
hqr : q ∣ gamma.fst.natAbs
hqs : q ∣ gamma.snd.natAbs
```

### 2. Move divisibility from `ℕ` to `ℤ`

```lean
have hqrZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqr
have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
```

### 3. Show that `q` divides the golden norm

After unfolding `goldenNorm`, divisibility of `r^2`, `rs`, and `s^2` is assembled with `dvd_add` and `dvd_sub`.

### 4. Transfer the divisor to `b`

The two sign branches of 0273 are handled with `rcases`. In the negative branch, `Int.dvd_neg.mp` removes the sign, and `exact_mod_cast` returns to natural-number divisibility.

### 5. Transfer the divisor to `5^6 a^10`

Using 0278:

```lean
have hprod := p.zeroSector_natAbs_product_eq hbeta
have hqRhs : q ∣ 5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  rw [← hprod]
  exact dvd_mul_of_dvd_left hqs _
```

### 6. Split the prime divisor and derive a contradiction

```lean
rcases hqPrime.dvd_mul.mp hqRhs with hq5pow | hqapow
```

- If `q | 5^6`, then `q | 5`, hence `q=5`, contradicting `five_not_dvd_b`.
- If `q | a^10`, then `q | a`; together with `q | b`, this contradicts `coprime_a_b`.

## Lean-specific processing

### Turning non-coprimality into a common prime witness

Mathematically one often says “if the gcd is not 1, there is a common prime divisor.” In Lean, `Nat.Prime.not_coprime_iff_dvd` gives exactly the explicit witness and proof data needed by the rest of the argument.

### Crossing the `natAbs` / integer boundary

The goal lives in `Nat.Coprime`, but `goldenNorm` is an integer polynomial. The proof therefore moves through

```lean
Int.natCast_dvd.mpr
```

and later returns with `exact_mod_cast`.

### `by decide` for concrete exponent side conditions

The calls to `dvd_pow` need nonzero-exponent evidence. For the concrete exponent 2, the proof discharges this computationally with

```lean
(by decide)
```

### `resolve_left hqPrime.ne_one`

`Nat.dvd_prime` produces the divisor alternatives `q=1` or `q=5`; because `q` itself is prime, `q=1` is eliminated immediately.

## Redundancy and overlap

The theorem is structurally clean and contains no serious local redundancy. Two pieces are, however, recurring proof patterns:

1. constructing divisibility of `goldenNorm gamma` from divisibility of both coordinates;
2. splitting a prime divisor of `5^6 * a^10` into the exceptional-prime branch or the `a` branch.

If the same patterns recur throughout the descent development, helper lemmas could reduce repetition. For this theorem alone, the explicit proof is arguably easier to audit.

## Optimization candidates

### 1. Extract a norm-divisibility helper lemma

A reusable statement of the form

```lean
(q : ℤ) ∣ r → (q : ℤ) ∣ s →
(q : ℤ) ∣ goldenNorm ⟨r,s⟩
```

would hide the coordinate expansion and make the theorem depend on a cleaner `GoldenInt` API.

This is an **unverified optimization candidate**; this run does not perform a Lean build.

### 2. Abstract the `q | 5^6 * a^10` split

If analogous arguments appear often, a dedicated prime-divisor or valuation lemma could package the exceptional-prime-versus-power-base split. The present code, however, has the advantage of making the special role of 5 explicit.

### 3. Avoid unfolding `goldenNorm`

A stronger abstraction barrier would let the theorem use an API lemma about coordinate divisibility rather than the polynomial representation directly. This would reduce coupling to the implementation of the norm.

## Required Mathlib imports and import optimization candidates

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses a global `import Mathlib`.

The main Mathlib facilities used directly by this theorem are:

- `Nat.Coprime`
- `Nat.Prime.not_coprime_iff_dvd`
- `Nat.Prime.dvd_mul`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_prime`
- `Nat.not_coprime_of_dvd_of_dvd`
- `Int.natCast_dvd`
- `Int.dvd_neg`
- `dvd_add`, `dvd_sub`, `dvd_pow`, `dvd_mul_of_dvd_left`
- `exact_mod_cast`
- `norm_num`

Project-side dependencies include at least `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenNorm`, theorem 0273, theorem 0278, and the power-split fields.

The **minimal Mathlib import set is not verified**. Because the canonical standalone artifact imports `Mathlib` wholesale and this run does not execute Lean builds, no reduced import list is claimed as checked.

## Correspondence with the existing PDFs

The target branch repository tree contains:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub repository-content connector does not expose these binary PDFs in an analyzable text form in this run, so the exact page and section corresponding to this theorem are **not verified**.

The theorem-level technical explanation therefore uses the generated `DkMath/FLT/Five/SignedGoldenZeroSector.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` as the primary source. No page-level PDF correspondence is guessed.

## Comparator challenge suitability

**Suitable, with medium difficulty.**

A challenge can provide as known facts:

- `p.zeroSector_gamma_norm_eq_or_eq_neg hbeta`
- `p.zeroSector_natAbs_product_eq hbeta`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

with goal

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

This tests extraction of a common prime witness, transport across `ℕ ↔ ℤ`, and prime-divisor splitting.

A useful comparator pair is:

- a proof attempting to manipulate the gcd directly;
- the common-prime contradiction proof used here.

The latter aligns naturally with the packet API and exposes the arithmetic structure of the argument more clearly.

## Next declaration to read

The next declaration is **0280 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`**.

It uses the primitive-coordinate statement proved here to establish

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

Assuming a common prime `q` divides both `s` and `H(r,s)`, the quartic-factor identity implies `q | r^4`; primality gives `q | r`, contradicting

$$
\gcd(|r|,|s|)=1.
$$

Thus 0279 supplies primitive coordinates, while 0280 upgrades that fact to the actual coprimality of the two factors needed for the zero-sector tenth-power split.
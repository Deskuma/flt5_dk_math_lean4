# 0280 — `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`

## Declaration kind

This declaration is a **`theorem`**.

For a zero-sector fifth-power base `gamma : GoldenInt`, it proves that the second coordinate `gamma.snd` is coprime, after taking natural absolute values, to the quartic factor `goldenFifthSndFactor gamma.fst gamma.snd` occurring in the second coordinate of a fifth power.

## Lean type

```lean
/-- The primitive coordinate condition makes `s` coprime to its quartic factor. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.snd.natAbs
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqs, hqH⟩
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd :=
    Int.natCast_dvd.mpr hqH
  have hqR4 : (q : ℤ) ∣ gamma.fst ^ 4 := by
    have htail : (q : ℤ) ∣
        goldenFifthSndFactor gamma.fst gamma.snd - gamma.fst ^ 4 := by
      rcases hqsZ with ⟨k, hk⟩
      refine ⟨k * (2 * gamma.fst ^ 3 + 4 * gamma.fst ^ 2 * gamma.snd +
        3 * gamma.fst * gamma.snd ^ 2 + gamma.snd ^ 3), ?_⟩
      simp only [goldenFifthSndFactor]
      rw [hk]
      ring
    have h := dvd_sub hqHZ htail
    ring_nf at h
    exact h
  have hqr4 : q ∣ gamma.fst.natAbs ^ 4 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
  have hqr : q ∣ gamma.fst.natAbs := hqPrime.dvd_of_dvd_pow hqr4
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs)
    (p.zeroSector_coprime_coords hbeta)
```

Write `gamma = (r,s)` and abbreviate

```lean
goldenFifthSndFactor r s
```

as `H(r,s)`. The conclusion is

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

Here

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

## Mathematical meaning

The quartic factor is especially simple modulo `s`:

$$
H(r,s)-r^4
= s\bigl(2r^3+4r^2s+3rs^2+s^3\bigr).
$$

Hence

$$
H(r,s)\equiv r^4\pmod{s}.
$$

Assume that `|s|` and `|H(r,s)|` are not coprime. Then there is a prime `q` dividing both:

$$
q\mid s,
\qquad
q\mid H(r,s).
$$

The congruence above implies

$$
q\mid r^4.
$$

Since `q` is prime,

$$
q\mid r.
$$

Thus `q` divides both `r` and `s`. But 0279 `zeroSector_coprime_coords` guarantees

$$
\gcd(|r|,|s|)=1,
$$

which is a contradiction. Therefore

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

## Role in the overall proof

At 0278, the zero-sector product equation has been transferred to natural absolute values:

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

To split this product into tenth powers, the two factors on the left must be coprime. The preceding theorem 0279 first establishes the primitive condition for the fifth-power base itself:

$$
\gcd(|r|,|s|)=1.
$$

The present theorem 0280 transfers that primitive condition to the quartic factor and obtains

$$
\gcd(|s|,|H|)=1.
$$

The immediately following 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split` uses this theorem directly. After moving all six factors of five to the `|s|` side, it writes

$$
|s|=5^6t,
\qquad
tH=a^{10},
$$

and then derives that `t` and `H` are still coprime from the present theorem. Since their coprime product is a tenth power, each factor is itself a tenth power.

Thus the dependency flow is

$$
\text{0278: }|s||H|=5^6a^{10}
\longrightarrow
\text{0279: }\gcd(|r|,|s|)=1
\longrightarrow
\text{0280: }\gcd(|s|,|H|)=1
\longrightarrow
\text{0281: tenth-power split}.
$$

## Direct dependencies

### `goldenFifthSndFactor`

In the repository source it is defined by

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

The proof unfolds this polynomial and uses the fact that every term except `r^4` contains a factor `s`.

### 0279 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords`

This supplies

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

and is the final contradiction target of the present proof.

### `Nat.Prime.not_coprime_iff_dvd`

It turns the negation of `Nat.Coprime` into a common prime divisor `q` of both natural numbers.

### `Int.natCast_dvd`

It transports divisibility of a natural absolute value,

```lean
q ∣ x.natAbs
```

into integer divisibility,

```lean
(q : ℤ) ∣ x,
```

and is used in the reverse direction when transporting `hqR4` back to the natural-number side.

### `dvd_sub`

From `q | H` and `q | (H-r^4)`, it yields `q | r^4` after normalization.

### `Nat.Prime.dvd_of_dvd_pow`

It descends from `q | |r|^4` to `q | |r|`.

### `Nat.not_coprime_of_dvd_of_dvd`

Using `q | |r|`, `q | |s|`, and `1 < q`, it constructs the contradiction to the coprimality supplied by 0279.

## Proof flow

### 1. Negate coprimality and extract a common prime

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqs, hqH⟩
```

This gives

```lean
hqs : q ∣ gamma.snd.natAbs
hqH : q ∣ (goldenFifthSndFactor ...).natAbs
```

### 2. Move natural divisibility to the integers

```lean
have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor ... :=
  Int.natCast_dvd.mpr hqH
```

The quartic factor is an integer polynomial, so the core algebra is carried out in `ℤ`.

### 3. Prove that `q` divides `H-r^4` with an explicit witness

The proof opens the witness for `q | s`:

```lean
rcases hqsZ with ⟨k, hk⟩
```

and directly provides the quotient

```lean
k * (2 * r^3 + 4 * r^2 * s + 3 * r * s^2 + s^3).
```

This is exactly the identity

$$
H-r^4=s(2r^3+4r^2s+3rs^2+s^3)
$$

written as a Lean divisibility witness. The final polynomial equality is closed by `ring`.

### 4. Obtain `q | r^4`

```lean
have h := dvd_sub hqHZ htail
ring_nf at h
exact h
```

`dvd_sub` first gives divisibility of `H-(H-r^4)`, and `ring_nf` normalizes this expression to `r^4`.

### 5. Return from `ℤ` to `ℕ` through `natAbs`

```lean
have hqr4 : q ∣ gamma.fst.natAbs ^ 4 := by
  simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
```

### 6. Descend a prime divisor through the fourth power

```lean
have hqr : q ∣ gamma.fst.natAbs := hqPrime.dvd_of_dvd_pow hqr4
```

### 7. Contradict 0279

```lean
exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs)
  (p.zeroSector_coprime_coords hbeta)
```

The common prime `q` now divides both `|r|` and `|s|`, contradicting the primitive-coordinate theorem 0279.

## Lean-specific processing

### Refuting `Nat.Coprime` by extracting a common prime

On paper one might work directly with a gcd. Lean instead uses `Nat.Prime.not_coprime_iff_dvd` to obtain a prime witness immediately. This representation fits `dvd_of_dvd_pow` particularly well and makes the proof resemble a local valuation argument.

### Crossing the `natAbs` / integer boundary

The conclusion is stated with `Nat.Coprime`, while `goldenFifthSndFactor` is an integer polynomial. The proof therefore transports divisibility along

$$
\mathbb N \to \mathbb Z \to \mathbb N.
$$

`Int.natCast_dvd` and `Int.natAbs_pow` handle this type boundary.

### Hand-written divisibility witness

For `htail`, the proof does not first package the general fact `s | H-r^4`. Instead, after obtaining a witness for `q | s`, it constructs the quotient for `q | H-r^4` directly. The kernel-visible equality is then discharged by `ring`.

### Normalizing subtraction with `ring_nf`

The result of `dvd_sub hqHZ htail` is syntactically divisibility of `H-(H-r^4)`. `ring_nf at h` normalizes this to the desired `r^4` statement.

## Redundancy and repetition

The proof is short and has little logical redundancy. One portion, however, is a reusable arithmetic fact independent of the packet:

```lean
(gamma.snd : ℤ) ∣
  goldenFifthSndFactor gamma.fst gamma.snd - gamma.fst ^ 4
```

Mathematically this is simply

$$
H(r,s)\equiv r^4\pmod{s}.
$$

The current proof waits until it has `q | s` and then constructs the quotient locally, so this congruence does not appear as a named theorem in the API.

## Optimization candidates

### 1. Extract a mod-`s` lemma for `goldenFifthSndFactor`

For example:

```lean
theorem goldenFifthSndFactor_sub_fst_pow_four_dvd_snd (r s : ℤ) :
    s ∣ goldenFifthSndFactor r s - r ^ 4 := by
  refine ⟨2 * r ^ 3 + 4 * r ^ 2 * s + 3 * r * s ^ 2 + s ^ 3, ?_⟩
  simp [goldenFifthSndFactor]
  ring
```

With such a theorem, `htail` could be reduced to essentially a transitivity step from `q | s`. This would also expose the actual mathematical reason for the coprimality transfer directly in the API.

### 2. Generalize the coprimality transfer

In general, if `H(r,s) ≡ r^n (mod s)` and `gcd(r,s)=1`, then `gcd(s,H)=1`. A generic lemma of this form could reduce the present theorem to supplying the polynomial congruence and theorem 0279.

Whether this abstraction would be reused enough elsewhere in the repository was not exhaustively checked in this run, so this remains an **optimization candidate**, not a confirmed improvement.

### 3. Avoid the `dvd_sub` + `ring_nf` normalization pair

Once the mod-`s` lemma is available in an intentional normal form, one could likely replace the present `dvd_sub` plus `ring_nf` sequence with a more direct divisibility or modular-equivalence argument. The current proof is already quite readable, however.

## Required Mathlib imports and import optimization

The canonical standalone file on the target branch, `Flt5DkMath/FLT5StandAlone.lean`, uses

```lean
import Mathlib
```

and bundles all generated source modules containing this theorem.

The Mathlib-side APIs and tactics used directly by this theorem include at least:

- `Nat.Coprime`
- `Nat.Prime.not_coprime_iff_dvd`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `Int.natCast_dvd`
- `Int.natAbs_pow`
- `dvd_sub`
- `ring`
- `ring_nf`

The standalone artifact flattens source-module imports, and the exact import line of the original `DkMath/FLT/Five/SignedGoldenZeroSector.lean` cannot be reconstructed from this repository artifact alone. Therefore the **minimal Mathlib import set has not been verified**.

An import-minimization pass should be performed against the original source module and validated by Lean elaboration or `lake build`. This task explicitly does not run Lean builds, so no specific minimal-import module names are asserted here.

## Comparator challenge suitability

**Suitable, with medium difficulty.**

The final theorem is compact, but a solver must combine three nontrivial Lean interfaces correctly:

1. extract a common prime witness from `¬ Nat.Coprime`;
2. move divisibility from `natAbs` into an integer quartic polynomial;
3. use `H(r,s) ≡ r^4 (mod s)` to transfer the prime divisor back to `r` and contradict the primitive-coordinate theorem.

A natural challenge setup would expose only

```lean
p.zeroSector_coprime_coords hbeta
```

plus the definition of `goldenFifthSndFactor` and standard Mathlib divisibility APIs, and ask for reconstruction of the theorem.

For a more mathematics-focused two-stage challenge, first ask for

```lean
s ∣ goldenFifthSndFactor r s - r ^ 4
```

and then use it to complete the coprimality transfer.

## Relation to the PDFs

The repository tree on the target branch confirms the presence of the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the GitHub connector cannot expose their binary contents as UTF-8 text, and the attempted Web retrieval of the PDF also failed in this run. Therefore the **exact page, section number, or wording in the PDFs corresponding to 0280 has not been verified**. The mathematical and Lean-specific account above is grounded in the canonical branch source `Flt5DkMath/FLT5StandAlone.lean` and the repository's current theorem-museum dependency order.

No PDF content has been inferred or invented.

## Next declaration to read

The next declaration is 0281

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
```

with type

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ∃ c d : ℕ,
      gamma.snd.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = d ^ 10 := by
  ...
```

It consumes the arithmetic prepared through 0280,

$$
|s||H|=5^6a^{10},
\qquad
5\nmid H,
\qquad
\gcd(|s|,|H|)=1,
$$

and constructs the exact split

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}.
$$

This is a major endpoint of the zero-sector arithmetic layer and becomes an input to the following inversion layer.
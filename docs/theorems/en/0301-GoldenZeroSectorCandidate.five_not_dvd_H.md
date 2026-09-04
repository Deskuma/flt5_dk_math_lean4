# 0301 — `GoldenZeroSectorCandidate.five_not_dvd_H`

## Declaration kind

This declaration is a **`theorem`**.

Using the norm information and the exclusion of the prime five stored in a zero-sector candidate, it proves that the quartic factor

$$
H(r,s):=\operatorname{goldenFifthSndFactor}(r,s)
$$

itself is not divisible by 5:

$$
5\nmid H(r,s).
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic factor retains the packet's exclusion of the prime five. -/
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq
    (⟨p.r, p.s⟩ : GoldenInt)
  have hnormSq : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  have hnorm : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  apply p.five_not_dvd_b
  rcases p.norm_eq_or_eq_neg with h | h
  · rw [h] at hnorm
    exact_mod_cast hnorm
  · rw [h] at hnorm
    exact_mod_cast (Int.dvd_neg.mp hnorm)
```

The conclusion is the non-divisibility statement over `ℤ`

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

## Mathematical meaning

The core of this theorem is the congruence between the quartic factor and the square of the golden norm:

$$
H(r,s)\equiv N(r,s)^2\pmod 5.
$$

In Lean, the theorem

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
```

expresses this as

$$
5\mid\bigl(H(r,s)-N(r,s)^2\bigr).
$$

Assume for contradiction that

$$
5\mid H(r,s).
$$

Since the difference is also divisible by 5, one obtains

$$
5\mid N(r,s)^2.
$$

Because 5 is prime,

$$
5\mid N(r,s).
$$

The candidate, however, stores

$$
N(r,s)=b
\quad\text{or}\quad
N(r,s)=-b
$$

as `norm_eq_or_eq_neg`, together with

$$
5\nmid b
$$

as `five_not_dvd_b`.

Therefore, in either sign branch, divisibility of the norm by 5 implies $5\mid b$, contradicting `five_not_dvd_b`. Hence

$$
5\nmid H(r,s).
$$

## Role in the full proof

By 0300 `coprime_c_d`, the tenth-power split bases already satisfy

$$
a=cd,
\qquad
\gcd(c,d)=1.
$$

What is not yet settled is whether the prime 5 can occur on the `d` side.

This theorem first establishes the stronger factor-level statement

$$
5\nmid H(r,s).
$$

The immediately following declaration, 0302 `five_not_dvd_d`, then uses

$$
H(r,s)=d^{10}
$$

to deduce

$$
5\nmid d.
$$

Thus 0301 is the **bridge transporting five-adic exclusion from the norm side to the quartic-factor side**. Once 5 is excluded from `H`, later analysis of the split base `d`, parity, valuations, and the factorization packet can keep five-adic ownership separated.

## Direct dependencies

### `GoldenZeroSectorCandidate`

This structure was introduced at 0290. The present theorem uses at least the following fields:

```lean
p.five_not_dvd_b : ¬ 5 ∣ p.b
p.norm_eq_or_eq_neg :
  goldenNorm ⟨p.r, p.s⟩ = (p.b : ℤ) ∨
    goldenNorm ⟨p.r, p.s⟩ = -(p.b : ℤ)
```

Thus the ultimate source of the prime-five exclusion is not the quartic formula itself, but the stored exclusion for the base `b`.

### `goldenFifthSndFactor`

The quartic factor whose non-divisibility by 5 is proved here.

### `goldenNorm`

The norm on `GoldenInt`. The theorem applies it to `⟨p.r,p.s⟩ : GoldenInt`.

### `five_dvd_goldenFifthSndFactor_sub_norm_sq`

The principal upstream theorem:

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2
```

Equivalently,

$$
H(\gamma)-N(\gamma)^2\equiv0\pmod5.
$$

This congruence is the mathematical core of the present theorem.

### `dvd_sub`

Used to combine `hH : 5 ∣ H` and `hdiff : 5 ∣ H-N^2` and derive divisibility of the norm square.

### `Prime.dvd_of_dvd_pow`

Since 5 is prime and divides $N^2$, this lemma extracts divisibility of $N$ itself.

```lean
(show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

### `Int.dvd_neg`

In the `N=-b` branch, this removes the sign from a divisibility statement.

### `exact_mod_cast`

The contradiction field `five_not_dvd_b` is over `ℕ`, whereas `hnorm` is over `ℤ`. `exact_mod_cast` transfers

```lean
(5 : ℤ) ∣ (p.b : ℤ)
```

to

```lean
5 ∣ p.b
```

## Proof flow

1. Assume for contradiction
   $$
   5\mid H(r,s)
   $$
   as `hH`.
2. Obtain
   $$
   5\mid H(r,s)-N(r,s)^2
   $$
   from `five_dvd_goldenFifthSndFactor_sub_norm_sq`.
3. Use `dvd_sub hH hdiff` to form a divisibility statement for the norm square.
4. Normalize the resulting integer expression with `ring_nf`, yielding
   $$
   5\mid N(r,s)^2.
   $$
5. Prove `Prime (5 : ℤ)` by `norm_num`, then apply `Prime.dvd_of_dvd_pow` to obtain
   $$
   5\mid N(r,s).
   $$
6. Apply `p.five_not_dvd_b`, changing the remaining goal to construction of `5 ∣ p.b`.
7. Split `p.norm_eq_or_eq_neg` into its two sign branches.
8. In the `N=b` branch, rewrite `hnorm` and use `exact_mod_cast`.
9. In the `N=-b` branch, use `Int.dvd_neg.mp hnorm` to remove the sign, then `exact_mod_cast`.
10. Both branches contradict `p.five_not_dvd_b`, so the original assumption is impossible.

## Lean-specific handling

On paper, from

$$
5\mid H,
\qquad
5\mid(H-N^2)
$$

one usually writes $5\mid N^2$ immediately. In Lean, the exact subtraction orientation produced by `dvd_sub` is not necessarily already syntactically equal to `N^2`, so

```lean
ring_nf at h
```

normalizes the integer expression.

The proof also explicitly constructs

```lean
(show Prime (5 : ℤ) by norm_num)
```

rather than a natural-number primality statement. This matters because the divisibility statement lives in the integer ring.

Finally, `exact_mod_cast` is required because the candidate's `five_not_dvd_b` field is a natural-number statement while the norm computation is carried out in `ℤ`.

## Redundancy and overlap

This theorem is structurally close to upstream zero-sector arguments such as `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm`, and the same congruence-to-norm-divisibility pattern appears again for later descent packets.

Consequently, one could factor out a general helper implementing the principle

$$
H\equiv N^2\pmod5,
\qquad
5\nmid N
\quad\Longrightarrow\quad
5\nmid H.
$$

However, the current proof expands the candidate provenance `norm_eq_or_eq_neg` and `five_not_dvd_b` locally. This has an auditing advantage: it remains completely explicit where the exclusion of 5 comes from. Removing duplication through aggressive abstraction could make that provenance less visible.

## Optimization candidates

1. The derivation of `hnormSq` might be expressible with a divisibility-algebra lemma that avoids `ring_nf`; this would need verification.
2. The two branches `N=b` and `N=-b` could potentially be packaged into a helper that converts norm divisibility to divisibility of `b`.
3. If `Prime (5 : ℤ)` is repeatedly reconstructed in nearby declarations, a local reusable lemma could remove repetition, although a one-line `norm_num` proof may be cheaper than the abstraction.
4. A general congruence-level helper of the form
   ```lean
   5 ∣ H - N ^ 2 → ¬ 5 ∣ N → ¬ 5 ∣ H
   ```
   could isolate the purely arithmetic content.

These are **unverified optimization candidates**, because no Lean build is performed in this task.

## Required Mathlib import and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the generated-source manifest places this declaration in the region corresponding to

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The Mathlib facilities directly exercised by this theorem include

- integer divisibility,
- `dvd_sub`,
- `Prime.dvd_of_dvd_pow`,
- `Int.dvd_neg`,
- `ring_nf`,
- `norm_num`,
- `exact_mod_cast`,
- `rw`, `rcases`, and `apply`.

The theorem itself does not use `omega`, `linarith`, or `nlinarith`.

The exact minimal import set is **not confirmed**, because Lean builds are explicitly excluded. It is plausible that `import Mathlib` could be narrowed to modules covering ring normalization, integer divisibility, primes, and norm casts, but imports required by upstream definitions `GoldenInt`, `goldenNorm`, and `goldenFifthSndFactor` would also have to be checked.

## Suitability as a Comparator challenge

**Suitable.** The difficulty is roughly intermediate.

A challenge can provide only

```lean
h5b : ¬ 5 ∣ b
hnorm : N = (b : ℤ) ∨ N = -(b : ℤ)
hdiff : (5 : ℤ) ∣ H - N ^ 2
```

with target

```lean
¬ (5 : ℤ) ∣ H
```

Useful evaluation points are whether the solver can

- interpret the congruence $H\equiv N^2\pmod5$ as divisibility,
- extract $5\mid N$ from $5\mid N^2$ using primality,
- handle the `N=±b` sign split,
- bridge divisibility between `ℤ` and `ℕ` with `exact_mod_cast`, and
- reuse the existing congruence theorem instead of expanding the quartic polynomial unnecessarily.

It is a compact challenge that tests prime divisibility, sign handling, coercions, and theorem selection at once.

## Relation to the PDFs

The repository tree on the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

with blob SHAs `88796012a87abfb348e7c9e529332063288319a3` for the Japanese PDF and `3d85ef047731caa199bc0aef9969f671998eaaab` for the English PDF.

However, the GitHub connector does not expose the binary PDF bodies as analyzable text in this run, so the exact PDF page, section, or wording corresponding to this theorem **could not be confirmed**. No guessed page or quotation is supplied.

For the technical meaning and Lean code, the current branch's `Flt5DkMath/FLT5StandAlone.lean` is treated as the authoritative source.

## Next declaration to read

The next declaration is **0302 `GoldenZeroSectorCandidate.five_not_dvd_d`**, also a `theorem`.

The current Lean source gives

```lean
/-- The quartic tenth-power base is not divisible by five. -/
theorem five_not_dvd_d (p : GoldenZeroSectorCandidate) : ¬ 5 ∣ p.d := by
  intro h5d
  apply p.five_not_dvd_H
  rw [p.H_eq_tenth]
  exact dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

It combines the present result

$$
5\nmid H(r,s)
$$

with 0297 `H_eq_tenth`,

$$
H(r,s)=d^{10},
$$

to conclude

$$
5\nmid d.
$$
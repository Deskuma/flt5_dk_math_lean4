# 0302 — `GoldenZeroSectorCandidate.five_not_dvd_d`

## Declaration kind

This declaration is a **`theorem`**.

From the fact that the zero-sector candidate's quartic factor is not divisible by 5 and that the quartic factor is exactly the tenth power `d^10`, it proves that the base `d` itself is not divisible by 5:

$$
5\nmid d.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic tenth-power base is not divisible by five. -/
theorem five_not_dvd_d (p : GoldenZeroSectorCandidate) : ¬ 5 ∣ p.d := by
  intro h5d
  apply p.five_not_dvd_H
  rw [p.H_eq_tenth]
  exact dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

The conclusion is non-divisibility over the naturals:

```lean
¬ 5 ∣ p.d
```

whereas the preceding theorem `five_not_dvd_H` is an integer non-divisibility statement:

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

so the proof contains an explicit divisibility cast from `ℕ` to `ℤ`.

## Mathematical meaning

The preceding declaration 0301 `GoldenZeroSectorCandidate.five_not_dvd_H` establishes

$$
5\nmid H(r,s).
$$

Declaration 0297 `GoldenZeroSectorCandidate.H_eq_tenth` establishes

$$
H(r,s)=d^{10}.
$$

Assume, for contradiction, that

$$
5\mid d.
$$

Then certainly

$$
5\mid d^{10},
$$

and hence

$$
5\mid H(r,s),
$$

contradicting 0301. Therefore

$$
5\nmid d.
$$

Thus this theorem is a simple but important descent of the prime-five exclusion from the whole quartic factor to its tenth-power base.

## Role in the full proof

In the zero-sector inversion beginning at 0290, the absolute-value split

$$
|H(r,s)|=d^{10}
$$

is first converted by 0297 into the signed identity

$$
H(r,s)=d^{10}.
$$

Then 0301 uses the norm channel to prove

$$
5\nmid H(r,s).
$$

Declaration 0302 composes those two facts and converts them into the base-level condition that later code actually wants:

$$
5\nmid d.
$$

This information is retained later as the field

```lean
five_not_dvd_d : ¬ 5 ∣ source.d
```

of `GoldenZeroSectorInversionPacket`. In the subsequent factorization layer it is used directly when proving coprimality between `zeroSectorQ c` and `d`, ensuring that the prime-five contribution cannot leak into the `d` factor.

Accordingly, this theorem is the **boundary lemma that deterministically pushes five-adic ownership from the quartic factor down to the split base `d`**.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The input `p` of the theorem. In particular, the proof uses `p.d : ℕ` and the coordinates `p.r`, `p.s`.

### `GoldenZeroSectorCandidate.five_not_dvd_H`

Declaration 0301:

```lean
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

This is the contradiction target used by the theorem.

### `GoldenZeroSectorCandidate.H_eq_tenth`

Declaration 0297:

```lean
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

It replaces the quartic-factor problem with the tenth power of the integer cast of `d`.

### `Int.natCast_dvd`

The expression

```lean
Int.natCast_dvd.mpr h5d
```

transports

```lean
h5d : 5 ∣ p.d
```

into

```lean
(5 : ℤ) ∣ (p.d : ℤ).
```

### `dvd_pow`

The theorem uses the fact that divisibility of the base implies divisibility of every positive power:

```lean
dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

which yields

$$
5\mid(d:\mathbb Z)^{10}.
$$

### `decide`

The closed decidable proposition

```lean
(by decide : 10 ≠ 0)
```

supplies the nonzero-exponent side condition required by `dvd_pow`.

## Proof flow

1. To prove `¬ 5 ∣ p.d`, assume
   ```lean
   h5d : 5 ∣ p.d
   ```
   via `intro h5d`.
2. Use
   ```lean
   apply p.five_not_dvd_H
   ```
   so the new goal becomes
   ```lean
   (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s.
   ```
3. Rewrite the quartic factor using
   ```lean
   rw [p.H_eq_tenth]
   ```
   to obtain the target `(5 : ℤ) ∣ (p.d : ℤ)^10`.
4. Lift `h5d` from natural-number divisibility to integer divisibility with `Int.natCast_dvd.mpr`.
5. Apply `dvd_pow`, supplying `(by decide : 10 ≠ 0)`, to prove divisibility of the tenth power.
6. This contradicts `p.five_not_dvd_H`, eliminating the assumption `5 ∣ p.d`.

## Lean-specific processing

Mathematically the proof is essentially the single implication

$$
5\mid d
\Rightarrow
5\mid d^{10}=H.
$$

The main Lean issue is the **type boundary**.

The field `p.d` lives in `ℕ`, while the right-hand side of `H_eq_tenth` is

```lean
(p.d : ℤ) ^ 10.
```

Therefore `h5d : 5 ∣ p.d` cannot be fed directly into the integer `dvd_pow` goal. The proof first transports divisibility with

```lean
Int.natCast_dvd.mpr h5d
```

and only then raises the divisor relation to the tenth power.

Moreover, `dvd_pow` requires a proof that the exponent is nonzero, which is discharged for the concrete exponent 10 by

```lean
(by decide : 10 ≠ 0).
```

## Redundancy and duplication

This theorem itself is extremely short and contains almost no local redundancy.

One could formulate a general helper expressing a pattern such as

```lean
¬ p ∣ x ^ n → n ≠ 0 → ¬ p ∣ x
```

or, under primality assumptions, use a contrapositive form of `Prime.dvd_of_dvd_pow`. The current implementation deliberately does not need primality at all: it only uses the forward fact that if `d` is divisible by 5, then `d^10` is divisible by 5.

This is a good separation of concerns. All five-specific arithmetic has already been completed in 0301; 0302 is only a divisibility transport step and does not reintroduce prime arithmetic unnecessarily.

If many later proofs repeatedly descend non-divisibility from powers to bases, a helper may become worthwhile. For this isolated four-line proof, abstraction would likely cost more than it saves.

## Optimization candidates

1. The explicit `dvd_pow` proof is already concise and transparent.
2. If the pair `Int.natCast_dvd.mpr` + `dvd_pow` becomes common, a cast-aware helper theorem could reduce repetition.
3. A separate API exposing the tenth-power identity directly in a natural-number divisibility form could remove the cast, but since the quartic factor itself is integer-valued the present design is more natural.
4. `(by decide : 10 ≠ 0)` could likely be replaced by `by norm_num`, but `decide` is lighter and more direct for this closed proposition.

These alternatives are **unverified**, because no Lean build is performed in this task.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the manifest places this theorem in the generated-source region corresponding to

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The Mathlib functionality directly visible in this theorem is mainly

- divisibility `∣`
- `Int.natCast_dvd`
- `dvd_pow`
- `decide`
- `rw`, `intro`, `apply`

The theorem body itself does not use `ring`, `ring_nf`, `omega`, `linarith`, `nlinarith`, `norm_num`, or `exact_mod_cast`.

Therefore a standalone version of this theorem could almost certainly use much narrower imports than all of `Mathlib`. However, the import closure required for `GoldenZeroSectorCandidate`, `goldenFifthSndFactor`, `H_eq_tenth`, and `five_not_dvd_H` must also be respected. Since no Lean build is allowed here, the exact minimal import set is **not verified**.

## Comparator challenge suitability

**Suitable.** The difficulty is around the boundary between beginner and intermediate Lean.

A compact challenge can provide

```lean
hH : ¬ (5 : ℤ) ∣ H
heq : H = (d : ℤ) ^ 10
```

and ask for

```lean
¬ 5 ∣ d.
```

Good evaluation points are whether the solver can

- choose the contradiction direction cleanly,
- cast divisibility from `ℕ` to `ℤ`,
- satisfy the nonzero-exponent premise of `dvd_pow`, and
- rewrite with `heq` so that the constructed divisibility contradicts the existing non-divisibility theorem.

Compared with 0301, the number theory is lighter, but it is a clean test of coercions and theorem application in Lean.

## Relation to the PDFs

The target branch repository tree contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the normal GitHub text connector does not return the contents of binary PDFs, so this run could not directly verify the exact page or section in either PDF. Any one-to-one mapping to a PDF section or wording is therefore **unverified** rather than inferred.

For the Lean side, the declaration body on the target branch was checked directly in `Flt5DkMath/FLT5StandAlone.lean`, together with the preceding 0301 theorem and the following `H_odd` declaration.

## Next declaration to read

The next declaration is

```lean
GoldenZeroSectorCandidate.H_odd
```

and its kind is **`theorem`**.

The canonical Lean source immediately continues with

```lean
/-- The primitive-coordinate quartic is odd. -/
theorem H_odd (p : GoldenZeroSectorCandidate) :
    Odd (goldenFifthSndFactor p.r p.s) := by
  ...
```

After 0302 has pushed the five-adic exclusion down to the base level,

$$
5\nmid d,
$$

the proof next performs a parity split on the primitive coordinates and proves that the quartic factor itself is odd. The following declaration `d_odd` then combines

$$
H=d^{10}
\qquad\text{and}\qquad
H\text{ odd}
$$

to conclude

$$
d\text{ odd}.
$$

Thus `H_odd → d_odd` is the parity analogue of the `five_not_dvd_H → five_not_dvd_d` descent performed by 0301–0302.

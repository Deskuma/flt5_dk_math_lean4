# 0339 — `GoldenZeroSectorInversionPacket.eight_dvd_factors`

## Declaration kind

This declaration is a **`theorem`**.

```lean
/-- In the even-`c` branch, both inversion factors contain at least three
factors of two. -/
theorem GoldenZeroSectorInversionPacket.eight_dvd_factors
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0 := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  have hs8 : (8 : ℤ) ∣ p.source.s := by
    refine ⟨-((2 : ℤ) ^ 7 * 5 ^ 6 * (k : ℤ) ^ 10), ?_⟩
    rw [p.s_eq, hk]
    push_cast
    ring
  have hsEven : Even p.source.s :=
    even_iff_two_dvd.mpr ((by norm_num : (2 : ℤ) ∣ 8).trans hs8)
  have hrOdd : Odd p.source.r := by
    rw [← Int.natAbs_odd, ← Nat.not_even_iff_odd]
    intro hrEven
    have hsEvenAbs : Even p.source.s.natAbs := hsEven.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num)
      hrEven.two_dvd hsEvenAbs.two_dvd) p.source.coprime_coords
  rcases hrOdd with ⟨rh, hrh⟩
  rcases hs8 with ⟨st, hst⟩
  let z : ℤ := 2 * rh + 1 + 4 * st
  let u : ℤ := z ^ 2 + 80 * st ^ 2
  let w : ℤ := (p.source.d : ℤ) ^ 5
  have hzOdd : Odd z := by
    dsimp [z]
    exact (odd_two_mul_add_one rh).add_even
      (even_iff_two_dvd.mpr ⟨2 * st, by ring⟩)
  have huOdd : Odd u := by
    dsimp [u]
    exact hzOdd.pow.add_even
      (even_iff_two_dvd.mpr ⟨40 * st ^ 2, by ring⟩)
  have hwOdd : Odd w := by
    exact p.source.d_odd.natCast.pow
  have hAform : zeroSectorA p.source.r p.source.s p.source.d =
      4 * (u - w) := by
    simp only [zeroSectorA, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hBform : zeroSectorB p.source.r p.source.s p.source.d =
      4 * (u + w) := by
    simp only [zeroSectorB, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hEvenSub : Even (u - w) := by
    simp [Int.even_sub', huOdd, hwOdd]
  have hEvenAdd : Even (u + w) := huOdd.add_odd hwOdd
  have h8AZ : (8 : ℤ) ∣ zeroSectorA p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenSub with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hAform, ht]
    ring
  have h8BZ : (8 : ℤ) ∣ zeroSectorB p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenAdd with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hBform, ht]
    ring
  constructor
  · apply Int.natCast_dvd.mp
    exact h8AZ
  · apply Int.natCast_dvd.mp
    exact h8BZ
```

## Lean type

The theorem has type

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0
```

Thus, for a zero-sector inversion packet `p`, if the tenth-power base `c` is even, then both natural-number factors `A0` and `B0` contain at least $2^3$.

## Mathematical statement

The hypothesis is

$$
2\mid c.
$$

Substituting `c=2k` into `p.s_eq` shows that `s` has a large 2-adic factor, in particular

$$
8\mid s.
$$

Since `r` and $|s|$ are coprime by `p.source.coprime_coords`, the evenness of `s` forces `r` to be odd.

The proof then introduces the auxiliary quantities

$$
z=2r_h+1+4s_t,
$$

$$
u=z^2+80s_t^2,
$$

$$
w=d^5.
$$

Both `u` and `w` are odd, hence

$$
u-w
$$

and

$$
u+w
$$

are even.

The zero-sector factors are rewritten as

$$
A_0=4(u-w),
$$

$$
B_0=4(u+w).
$$

Combining the external factor $4$ with the additional factor $2$ in each parenthesis gives

$$
8\mid A_0,
\qquad
8\mid B_0.
$$

## Role in the full FLT5 proof

Where 0338 `nonempty_odd_factorData` constructs the exact factor certificate for the odd-`c` branch, this theorem is the **entry point of the 2-adic analysis for the even-`c` branch**.

The next theorem, `GoldenZeroSectorInversionPacket.even_factor_eighths`, removes the common factor $8$ from `A0` and `B0` and proves that the remaining two factors have opposite parity. This then leads to the `GoldenZeroSectorFactorData.evenLeftLow` / `.evenRightLow` split and eventually to fifth-power factorization in the even branch.

The structural flow is

```text
c even
  │
  ▼
8 ∣ s
  │
  ▼
r odd
  │
  ▼
u,w odd
  │
  ▼
u-w and u+w even
  │
  ▼
A0 = 4(u-w), B0 = 4(u+w)
  │
  ▼
8 ∣ A0 and 8 ∣ B0
```

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

The input packet. Through `source` it exposes `r,s,c,d,A0,B0` together with the identities, coprimality facts, and parity information used here.

### `p.s_eq`

Provides the exact relation between `source.s` and `c`. After substituting `c=2k`, it is used to construct an explicit witness for $8\mid s$.

### `p.source.coprime_coords`

Provides coprimality of `r` and $|s|$. If `r` were also even, then both coordinates would be divisible by $2$, contradicting this fact.

### `p.source.d_odd`

Provides oddness of $d$. After casting to integers and raising to the fifth power, it gives

```lean
hwOdd : Odd ((p.source.d : ℤ) ^ 5)
```

### `zeroSectorA`, `zeroSectorB`, `zeroSectorU`, `zeroSectorX`, `zeroSectorW`

These definitions are unfolded to normalize `A0` and `B0` into

```lean
4 * (u - w)
4 * (u + w)
```

using the local auxiliary variables.

### `even_iff_two_dvd`, `Int.natAbs_odd`, `Nat.not_even_iff_odd`

These bridge parity and divisibility facts across natural numbers and integers.

### `Nat.not_coprime_of_dvd_of_dvd`

Used to contradict `coprime_coords` under the temporary assumption that both `r` and $|s|$ are divisible by $2$.

### `Int.natCast_dvd`

The final bridge from integer divisibility

```lean
(8 : ℤ) ∣ zeroSectorA ...
(8 : ℤ) ∣ zeroSectorB ...
```

to the natural-number conclusions `8 ∣ A0` and `8 ∣ B0`.

## Proof flow

### 1. Extract `c=2k`

```lean
rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
```

turns the parity hypothesis into a concrete quotient witness.

### 2. Prove `8 ∣ s`

Using `p.s_eq` and `hk`, the proof expands `s` and supplies the explicit quotient

```lean
-((2 : ℤ) ^ 7 * 5 ^ 6 * (k : ℤ) ^ 10)
```

before closing the identity with `ring`.

### 3. Force `r` to be odd

From `8 ∣ s` the proof obtains evenness of `s`. If `r` were even as well, then `r` and $|s|$ would share the factor $2$, contradicting `coprime_coords`.

### 4. Build an odd normal form

The witnesses `r=2rh+1` and `s=8st` are unpacked, and `z`, `u`, `w` are introduced. Then `z` is shown odd, hence `u` is odd, while oddness of `d` gives oddness of `w`.

### 5. Rewrite `A0` and `B0` as `4(u±w)`

The zero-sector definitions are unfolded with `simp only`; `rw [hrh, hst]` and `ring` then establish the exact polynomial identities.

### 6. Prove `u±w` even

A sum and a difference of odd integers are both even.

### 7. Construct divisibility by 8 over the integers

Writing `u±w=2t`, the proof checks

$$
4(u\pm w)=8t
$$

with `ring`.

### 8. Return to natural numbers

`Int.natCast_dvd.mp` transports the integer divisibility results back to `A0,B0 : ℕ`.

## Lean-specific processing

### Crossing the integer/natural-number boundary

Although `A0` and `B0` are natural numbers, the zero-sector algebra is performed over the integers. The proof therefore establishes `(8 : ℤ) ∣ ...` first and only converts back with `Int.natCast_dvd.mp` at the end.

### Extracting parity witnesses with `rcases`

`Even n` contains an existential witness of the form `n=2k`. The proof extracts those quotients explicitly and reuses them in polynomial normalization.

### Local compression with `let`

The names `z`, `u`, and `w` compress otherwise large formulas and separate the parity argument from the expansion of `zeroSectorA/B`.

### `simp only` plus `ring`

The proof deliberately restricts definitional unfolding with `simp only`, then delegates only polynomial normalization to `ring`. This keeps proof search narrow and responsibilities clear.

### `push_cast`

After moving the natural-number witness `k` into an integer formula, `push_cast` normalizes casts into a form suitable for `ring`.

## Redundancy and duplication

The constructions of `h8AZ` and `h8BZ` are fully symmetric; only `u-w` versus `u+w`, and `hAform` versus `hBform`, differ.

Likewise, the transition from `hzOdd`, `huOdd`, and `hwOdd` to `hEvenSub` and `hEvenAdd` is a repeated instance of the common pattern “odd ± odd is even.”

That said, aggressively abstracting these two symmetric branches could obscure the concrete zero-sector structure, so the current explicit form is also defensible for readability.

## Optimization candidates

1. The common body of `h8AZ` / `h8BZ` could be extracted into a small helper lemma turning `hform : X = 4*t` plus `Even t` into `8 ∣ X`.

2. The proof of oddness of `r` could become a local reusable lemma: if `s` is even and `Coprime r |s|`, then `r` is odd. This is worthwhile if the same parity pattern occurs elsewhere.

3. If `z` and `u` recur in later declarations, they could be promoted to named definitions or a local structure. If they are used only here, the present `let` bindings are lighter.

4. If natural-number normal forms for `A0` and `B0` become available, the final integer-to-natural conversion could potentially be shortened. Whether this actually improves the proof is **unverified** because the current zero-sector definitions are integer-centered.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main facilities used directly here are parity APIs, `Nat.Coprime`, integer casts, `ring`, `norm_num`, `simp`, and `push_cast`.

The generated-source boundary in the standalone file identifies the original module as `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean`.

A narrower Mathlib import set is likely possible, but no Lean build is run in this task, so the exact minimal import set is **unverified**. In particular, the minimal combination covering `ring`, parity, and integer-cast lemmas should not be asserted without a build check.

## Comparator challenge suitability

**Yes; medium-to-high suitability.**

This theorem naturally separates into two comparison layers:

- Mathematical layer: derive $8\mid A_0,B_0$ from even `c`, the exact formula for `s`, coprimality of `r` and $|s|$, and oddness of `d`.
- Lean layer: manage `Nat`/`Int` casts, parity witnesses, `simp only`, `ring`, and `Int.natCast_dvd` cleanly.

In particular, the path “natural parity → integer polynomial divisibility → natural divisibility” is a good target for comparing alternative Lean proof designs.

For a standalone Comparator challenge, however, requiring all the repository-specific zero-sector definitions would make the task too local. A reduced version that assumes the exact identities, followed by the repository-integrated version, would be more effective.

## Next declaration to read

Next is **0340 `GoldenZeroSectorInversionPacket.even_factor_eighths`**, also a `theorem`.

```lean
theorem GoldenZeroSectorInversionPacket.even_factor_eighths
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 8 * A1 ∧ p.source.B0 = 8 * B1 ∧
      ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)) := by
```

It uses the divisibility by $8$ established here to extract the eighth factors `A1` and `B1`, then proves that they have opposite parity. This is the first declaration that explicitly exposes the `evenLeftLow` / `evenRightLow` split of the even branch.

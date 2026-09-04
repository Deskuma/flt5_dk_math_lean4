# 0303 — `GoldenZeroSectorCandidate.H_odd`

## Declaration kind

This declaration is a **`theorem`**.

It proves that the quartic second-coordinate factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

is odd from the coprimality of the primitive zero-sector coordinates `r` and `s`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The primitive-coordinate quartic is odd. -/
theorem H_odd (p : GoldenZeroSectorCandidate) :
    Odd (goldenFifthSndFactor p.r p.s) := by
  have hterm2 : Even (2 * p.r ^ 3 * p.s) :=
    (even_two.mul_right (p.r ^ 3)).mul_right p.s
  have hfour : Even (4 : ℤ) := ⟨2, by norm_num⟩
  have hterm3 : Even (4 * p.r ^ 2 * p.s ^ 2) :=
    (hfour.mul_right (p.r ^ 2)).mul_right (p.s ^ 2)
  rcases Int.even_or_odd p.r with hr | hr <;>
    rcases Int.even_or_odd p.s with hs | hs
  · exfalso
    have hrNat : Even p.r.natAbs := hr.natAbs
    have hsNat : Even p.s.natAbs := hs.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega)
      hrNat.two_dvd hsNat.two_dvd) p.coprime_coords
  · unfold goldenFifthSndFactor
    have hterm1 : Even (p.r ^ 4) :=
      hr.pow_of_ne_zero (by decide : 4 ≠ 0)
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hr.mul_left 3).mul_right (p.s ^ 3)
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add hterm2).add hterm3).add hterm4).add_odd hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hs.pow_of_ne_zero (by decide : 3 ≠ 0)).mul_left (3 * p.r)
    have hterm5 : Even (p.s ^ 4) :=
      hs.pow_of_ne_zero (by decide : 4 ≠ 0)
    exact (((hterm1.add_even hterm2).add_even hterm3).add_even hterm4).add_even hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hthree : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have hterm4 : Odd (3 * p.r * p.s ^ 3) :=
      (hthree.mul hr).mul hs.pow
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add_even hterm2).add_even hterm3).add_odd hterm4).add_odd hterm5
```

The conclusion is the integer parity proposition

```lean
Odd (goldenFifthSndFactor p.r p.s)
```

## Mathematical meaning

The quartic factor unfolded by the Lean proof is

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

The two middle terms

$$
2r^3s,\qquad 4r^2s^2
$$

are always even, independently of the parities of `r` and `s`. Thus the parity is controlled mainly by

$$
r^4,\qquad 3rs^3,\qquad s^4.
$$

The candidate stores

$$
\gcd(|r|,|s|)=1
$$

as `p.coprime_coords`, so `r` and `s` cannot both be even. The remaining three cases are as follows.

1. If `r` is even and `s` is odd, then `r^4` and `3rs^3` are even while `s^4` is odd, hence $H$ is odd.
2. If `r` is odd and `s` is even, then `r^4` is odd while `3rs^3` and `s^4` are even, hence $H$ is odd.
3. If both `r` and `s` are odd, then `r^4`, `3rs^3`, and `s^4` are all odd. The sum of three odd terms is odd, and adding the two universally even terms does not change parity.

Therefore every primitive-coordinate case satisfies

$$
H(r,s)\equiv1\pmod2.
$$

## Role in the full proof

The sequence 0301→0302 descends the prime-five exclusion

$$
5\nmid H(r,s)
$$

from the quartic factor to the tenth-power base `d`, obtaining

$$
5\nmid d.
$$

Declaration 0303 begins a parallel parity channel. It first establishes at the factor level that

$$
H(r,s)\text{ is odd}.
$$

The immediately following 0304 `GoldenZeroSectorCandidate.d_odd` combines this result with 0297

$$
H(r,s)=d^{10}
$$

to descend oddness to the base:

$$
d\text{ is odd}.
$$

Later inversion arguments track the 2-adic structure of `W=4d^5` and of the two factors `A`,`B`, so the oddness of `d` becomes an important input. In particular, in the even-`c` branch, the fact that `d^5` is odd helps fix the parity pattern of the factor difference and distinguish the relevant 2-adic valuations.

Thus 0303 is the **entry point converting primitive-coordinate coprimality into the 2-adic unit property of the quartic factor**.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The theorem takes a candidate `p` and uses in particular

```lean
p.r : ℤ
p.s : ℤ
p.coprime_coords : Nat.Coprime p.r.natAbs p.s.natAbs
```

### `goldenFifthSndFactor`

This is the quartic polynomial whose parity is proved. Each valid branch unfolds `goldenFifthSndFactor` and combines the parity of its monomials explicitly.

### `Int.even_or_odd`

This gives the exhaustive even/odd split for each integer. Applying it to both `r` and `s` creates four parity branches.

### `Even.natAbs` and `Nat.not_coprime_of_dvd_of_dvd`

In the even-even branch, integer evenness is transported to the evenness of the natural absolute values. The proof then obtains

```lean
hrNat.two_dvd : 2 ∣ p.r.natAbs
hsNat.two_dvd : 2 ∣ p.s.natAbs
```

and contradicts `p.coprime_coords`.

### Algebraic APIs for `Even` and `Odd`

Methods such as `mul_left`, `mul_right`, `pow`, `pow_of_ne_zero`, `add_even`, and `add_odd` assemble the parity of the polynomial monomials at the proposition level.

### `norm_num`, `omega`, and `decide`

These discharge closed arithmetic facts such as the evenness of `4`, the oddness of `3`, the nontriviality of the common divisor `2`, and the nonzeroness of exponents `3` and `4`.

## Proof flow

1. Prove once that `2 * r^3 * s` is always even and store this as `hterm2`.
2. Prove that `4` is even and use it to establish that `4 * r^2 * s^2` is always even, stored as `hterm3`.
3. Split `r` and `s` independently with `Int.even_or_odd`, producing four parity branches.
4. In the even-even branch, transport evenness through `natAbs`; both natural absolute values are divisible by `2`, contradicting `p.coprime_coords`.
5. In the even-odd branch, unfold the quartic. Only the final term `s^4` is odd, so the whole sum is odd.
6. In the odd-even branch, only the first term `r^4` is odd, so the whole sum is odd.
7. In the odd-odd branch, `r^4`, `3*r*s^3`, and `s^4` are odd while the other two terms are even; composing these facts yields an odd total.

## Lean-specific processing

Mathematically, the argument can be compressed into a short calculation modulo two. The Lean implementation instead uses the algebraic API of the propositions `Even` and `Odd` explicitly.

A particularly Lean-specific boundary appears when excluding the even-even branch. The primitive condition is stored over naturals as

```lean
Nat.Coprime p.r.natAbs p.s.natAbs
```

whereas the case split produces `Even p.r` and `Even p.s` over integers. The proof therefore passes through `.natAbs` before using natural-number divisibility.

There is also an API asymmetry for powers. Evenness of a power is proved with a nonzero-exponent side condition, for example

```lean
hr.pow_of_ne_zero (by decide : 4 ≠ 0)
```

whereas odd powers can be handled directly with expressions such as `hs.pow`.

Finally, the proof does not delegate the whole parity calculation to a general arithmetic simplifier. It composes `add_even` and `add_odd` explicitly, making visible which monomials preserve or flip the running parity.

## Redundancy and duplication

Hoisting `hterm2` and `hterm3` outside the case split is already a useful optimization. Those two monomials are even in every branch, so their proofs are not repeated.

The three valid branches each perform

```lean
unfold goldenFifthSndFactor
```

and reconstruct `hterm1`, `hterm4`, and `hterm5`. This is syntactic repetition, but their parity patterns differ by branch, so aggressive helper extraction could reduce readability rather than improve it.

Mathematically one could first derive from primitiveness that at least one coordinate is odd and then use a mod-2 normal form such as

$$
H(r,s)\equiv r+s+rs\pmod2
$$

or an equivalent Boolean parity computation. Such a proof might be shorter, but the current proof is easier to audit monomial by monomial.

## Optimization candidates

1. Extract a reusable lemma saying that coprime integer coordinates cannot both be even; this would shorten the contradiction branch.
2. Add an independent mod-2 normal-form lemma for `goldenFifthSndFactor`; later parity uses of the same quartic could then be much shorter.
3. It may be possible to compress the three valid branches with `simp`/`norm_num` plus parity normalization, but this has **not been verified** because no Lean build is performed in this task.
4. For Comparator and audit purposes, the current explicit proof has substantial pedagogical value, so line-count reduction alone is not a strong reason to replace it.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its generated-source manifest places this theorem in

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The theorem body directly relies mainly on integer/natural `Even` and `Odd`, `natAbs`, `Nat.Coprime`, divisibility, parity APIs for products/sums/powers, and the tactics `norm_num`, `omega`, and `decide`.

A substantially narrower import closure than all of `Mathlib` is therefore likely possible for this theorem in isolation. However, the project definitions `GoldenZeroSectorCandidate` and `goldenFifthSndFactor` and their upstream dependencies must also be available. The exact minimal Mathlib module set is **unverified** because the requested workflow forbids a Lean build.

## Comparator challenge suitability

**Suitable.** This is a good intermediate-level challenge, somewhat richer than 0302.

One can provide

```lean
hrs : Nat.Coprime r.natAbs s.natAbs
```

and the definition of `goldenFifthSndFactor r s`, with the target

```lean
Odd (goldenFifthSndFactor r s)
```

Useful comparison criteria are whether a solution can:

- construct an exhaustive split with `Int.even_or_odd`;
- eliminate the even-even branch from `Nat.Coprime`;
- connect the product/sum/power APIs for `Even` and `Odd` correctly;
- hoist universally even monomials outside the branch split to avoid duplication;
- handle the type boundary between parity over `ℤ` and coprimality of `natAbs` over `ℕ`.

The task tests proof decomposition and API selection rather than mere automated arithmetic, which makes it a strong Comparator example.

## Correspondence with the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed from the repository tree.

The GitHub connector's normal text retrieval does not return the binary PDF body, so the exact page or section containing this theorem could not be directly checked in this run. The precise one-to-one correspondence with a PDF section is therefore **unverified**, and no page mapping is inferred.

For the Lean source, the declaration itself, the preceding `five_not_dvd_d`, and the following `d_odd` were all checked in the target branch's `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is

```lean
GoldenZeroSectorCandidate.d_odd
```

and its kind is **`theorem`**.

The canonical Lean source immediately continues with

```lean
/-- Consequently the tenth-power base `d` is odd. -/
theorem d_odd (p : GoldenZeroSectorCandidate) : Odd p.d := by
  have hH := p.H_odd
  rw [p.H_eq_tenth] at hH
  have hdZ : Odd (p.d : ℤ) :=
    (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
  exact_mod_cast hdZ
```

Declaration 0303 establishes at the factor level that

$$
H(r,s)\text{ is odd},
$$

and 0304 uses

$$
H(r,s)=d^{10}
$$

to descend this to

$$
d\text{ is odd}.
$$

This is the second half of the parity descent, exactly parallel in structure to the five-adic descent 0301→0302.
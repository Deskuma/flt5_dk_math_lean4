# 0276 — `five_dvd_goldenFifthSndFactor_sub_norm_sq`

## Declaration kind

This is a **`theorem`**.

It is an integer congruence lemma in `DkMath.FLT.Five.SignedGoldenZeroSector`. It shows that the quartic factor `goldenFifthSndFactor`, which occurs in the second coordinate of a fifth power in `GoldenInt`, agrees modulo 5 with the square of the golden norm.

## Lean type

```lean
/-- The quartic factor is the square of the golden norm modulo five. -/
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

Write `gamma = (r,s)`. By definition,

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

and

$$
N(r,s)=r^2+rs-s^2.
$$

The theorem states

$$
5\mid\bigl(H(r,s)-N(r,s)^2\bigr).
$$

More strongly, the witness exhibited in the proof shows the exact identity

$$
H(r,s)-N(r,s)^2
=5rs^2(r+s).
$$

Hence

$$
H(r,s)\equiv N(r,s)^2\pmod 5.
$$

## Mathematical meaning

`goldenFifthSndFactor` is the quartic factor that appears when the second coordinate of

$$
(r+s\varphi)^5
$$

is factored as

$$
5s\,H(r,s).
$$

The golden norm is

$$
N(r+s\varphi)=r^2+rs-s^2.
$$

At first sight, the fifth-power coordinate polynomial $H$ and the norm square $N^2$ are unrelated quartic expressions. Their difference, however, is always divisible by 5, and in fact has the particularly simple correction term

$$
H-N^2=5rs^2(r+s).
$$

This congruence matters because divisibility by 5 can be transferred between $H$ and $N$. In particular, if

$$
5\mid H,
$$

then the present theorem and `dvd_sub` imply

$$
5\mid N^2.
$$

Since 5 is prime, this yields

$$
5\mid N.
$$

In the zero sector, the immediately preceding theorem 0274 provides

$$
5\nmid N(\gamma),
$$

so one obtains

$$
5\nmid H(r,s).
$$

Thus 0276 is the **mod-5 bridge** that transfers the packet-side five-adic exclusion on the norm to the quartic factor arising from the fifth-power coordinate.

## Role in the full proof

0275 `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq` established the exact signed product equation

$$
sH(r,s)=-5^6a^{10}
$$

in the zero sector.

To split this product for descent, the proof must show that the factor $H$ does not absorb any factor of 5. The present theorem provides

$$
H\equiv N^2\pmod 5,
$$

which can be combined with 0274, namely $5\nmid N$.

The theorem immediately following 0276 in the canonical source,

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
```

performs exactly this combination. It assumes `hH : 5 ∣ H`, uses 0276 to obtain $5\mid N^2$, descends through the primality of 5 to $5\mid N$, and contradicts 0274.

The canonical source also shows that this theorem is not confined to this one packet argument. It is reused later by `GoldenZeroSectorCandidate.five_not_dvd_H`, `GoldenZeroSectorDescentPacket.five_not_dvd_H`, and the fifth-root theorem `fifthRoot_five_not_dvd_H`. Therefore it is a reusable base congruence for the broader Golden fifth-power arithmetic rather than a one-off local lemma.

## Direct dependencies

### `GoldenInt`

The two-coordinate representation of the golden order. This theorem only uses `gamma.fst` and `gamma.snd`.

### `goldenFifthSndFactor`

The canonical source defines the quartic polynomial by

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

This is the factor $H(r,s)$ appearing in the second coordinate of a fifth power.

### `goldenNorm`

The canonical source defines

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

so for `gamma = (r,s)`,

$$
N(\gamma)=r^2+rs-s^2.
$$

### Integer divisibility

The goal is not an equality but

```lean
(5 : ℤ) ∣ expression
```

so Lean expects a witness `k` with the appropriate multiplication equality.

### `ring`

After the two definitions are unfolded, the remaining task is a polynomial identity over the integers, which `ring` closes by normalization.

## Proof flow

### 1. Give an explicit quotient witness

```lean
refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
```

A divisibility proposition `a ∣ b` asks for an integer $k$ with $b=ak$. Here the chosen witness is

$$
k=rs^2(r+s).
$$

So the proof does not merely reason abstractly modulo 5; it knows the stronger exact factorization

$$
H-N^2=5rs^2(r+s).
$$

### 2. Unfold exactly the two relevant definitions

```lean
simp only [goldenFifthSndFactor, goldenNorm]
```

This expands $H$ and $N$ into coordinate polynomials. The use of `simp only` deliberately avoids unrelated simplification and restricts the proof dependency to these two definitions.

### 3. Close the polynomial identity with `ring`

```lean
ring
```

After unfolding, the goal is a polynomial identity with integer coefficients. `ring` normalizes both sides and proves equality.

No primality fact, packet data, or zero-sector hypothesis is used in 0276 itself. The theorem is a pure algebraic identity valid for every `GoldenInt`.

## Lean-specific processing

### Constructing a divisibility witness

Lean's `a ∣ b` carries existential data, so

```lean
refine ⟨..., ?_⟩
```

allows the quotient to be supplied directly. In this theorem the witness is mathematically informative because it exposes the exact factorization of the difference.

### `simp only`

Using

```lean
simp only [goldenFifthSndFactor, goldenNorm]
```

rather than unrestricted `simp` keeps the simplification stable and makes the dependency surface explicit. This is a good design choice for a small algebraic lemma.

### `ring`

`ring` is more appropriate here than `nlinarith`. No arithmetic hypothesis is being exploited; the goal after unfolding is an unconditional polynomial identity.

## Redundancy and duplication

The proof is only three lines long and has essentially no local redundancy.

The main structural observation is that the public statement exposes only divisibility, while the proof internally establishes the stronger exact identity

$$
H-N^2=5rs^2(r+s).
$$

If later code never needs the quotient itself, the current API is appropriately small. If the exact difference formula is rederived elsewhere, it could be promoted to a named theorem and 0276 could become a short corollary.

## Optimization candidates

### 1. Expose the exact identity as a base API

For example,

```lean
theorem goldenFifthSndFactor_sub_norm_sq_eq (gamma : GoldenInt) :
  goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 =
    5 * gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd) := by
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

could serve as the stronger base theorem, with 0276 derived from it. This would be useful if downstream code ever needs the quotient $rs^2(r+s)$ itself.

At present, however, the downstream uses identified in the canonical source only need modulo-5 divisibility, so the existing theorem keeps the API surface smaller.

### 2. Factor out the repeated divisibility-transfer pattern

Later proofs repeatedly use

$$
5\mid H,
\qquad
5\mid(H-N^2)
$$

to obtain $5\mid N^2$. This is not redundancy inside 0276, but a dedicated transfer lemma or a congruence API could shorten the repeated `dvd_sub` + `ring_nf` sequence.

### 3. Consider an `Int.ModEq` formulation

The direct mathematical statement is

```lean
Int.ModEq 5
  (goldenFifthSndFactor gamma.fst gamma.snd)
  (goldenNorm gamma ^ 2)
```

This could make the congruence semantics more explicit. On the other hand, the current downstream code is already written in the divisibility API, so `5 ∣ H - N²` is presently the more convenient interface.

## Required Mathlib imports and import optimization

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

and its manifest places this theorem in `DkMath/FLT/Five/SignedGoldenZeroSector.lean`, after earlier modules including `GoldenOrder.lean` and `GoldenFifthPowerCoordinates.lean`.

The mechanisms directly needed by 0276 from Mathlib are the integer ring and divisibility infrastructure, `simp only`, and the `ring` tactic. On the project side it requires `GoldenInt`, `goldenNorm`, and `goldenFifthSndFactor`.

The **minimal Mathlib import set for the original module is unverified**. A safe reduction would require separating the import needed for `ring` from the transitive imports supplying the project-side golden arithmetic and then checking the result with Lean. No Lean build is performed in this task, so a concrete replacement for `import Mathlib` would be only speculative.

## Relation to the existing PDFs

The target branch contains

- `FLT5-main-ja-v0-r1.pdf`
- `FLT5-main-en-v0-r1.pdf`

under `docs/pdf`.

The GitHub connector does not provide these PDF binaries in a form suitable for direct content analysis in this run. Therefore the exact page number, section number, and whether the identity

$$
H-N^2=5rs^2(r+s)
$$

appears verbatim in the PDFs are **unverified**. This document does not guess a PDF location; the technical account is grounded primarily in the canonical Lean source on the target branch.

## Comparator challenge suitability

**Highly suitable, with low-to-medium difficulty.**

A challenge can provide the definitions

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4

def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

and ask for

```lean
(5 : ℤ) ∣
  goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2
```

The useful evaluation points are whether the solver can

1. recognize that a divisibility goal should be solved by constructing a quotient witness,
2. discover the witness $rs^2(r+s)$ from the polynomial structure, and
3. close the resulting identity cleanly with `ring`.

Although the theorem statement looks like a modular-arithmetic problem, the shortest proof comes from recognizing an exact algebraic factorization. That makes it a good Comparator exercise in structural algebraic recognition.

## Next declaration to read

The next declaration should be **0277 `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`**.

The canonical source gives the following proof shape:

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  apply p.zeroSector_five_not_dvd_gamma_norm hbeta
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

0276 supplies the transfer bridge $H\equiv N^2\pmod5$, while 0277 combines it with the earlier 0274 `zeroSector_five_not_dvd_gamma_norm` to conclude

$$
5\nmid H(r,s).
$$

Thus the dependency chain is naturally

$$
\text{0274: }5\nmid N
\quad\longrightarrow\quad
\text{0276: }H\equiv N^2\pmod5
\quad\longrightarrow\quad
\text{0277: }5\nmid H.
$$

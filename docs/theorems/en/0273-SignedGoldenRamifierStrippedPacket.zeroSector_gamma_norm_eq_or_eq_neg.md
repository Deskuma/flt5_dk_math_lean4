# 0273 — `SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg`

## Declaration kind

This is a **`theorem`**.

It is an entry-point lemma for `SignedGoldenZeroSector.lean`. It specializes the already-proved general theorem `SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg`, which applies to a unit-times-fifth-power factorization, to the pure fifth-power case where the unit factor is `1`.

## Lean type

```lean
/-- The zero-sector base has norm equal to the packet base up to sign. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

Mathematically, if the packet field `beta` is a pure fifth power

$$
\beta=\gamma^5,
$$

then the golden norm of `gamma` is equal, up to sign, to the integer coercion of the packet parameter `b`:

$$
N(\gamma)=b
\qquad\text{or}\qquad
N(\gamma)=-b,
$$

where

$$
b:=p.exceptional.powerSplit.b.
$$

## Meaning of the mathematical statement

At the general factorization layer, the packet has a representation

$$
\beta=\epsilon\gamma^5
$$

with `epsilon` a golden unit. The already-established theorem `gamma_norm_eq_or_eq_neg` uses the fact that a unit has norm $\pm1$ to conclude that the norm of `gamma` is the packet quantity `b`, up to sign.

In the zero sector, the unit representative is

$$
\varphi^0=1,
$$

so the hypothesis simplifies to

$$
\beta=\gamma^5.
$$

This theorem merely re-expresses that as

$$
\beta=1\cdot\gamma^5
$$

and invokes the general theorem with `goldenOne` as the unit.

Thus, no new norm arithmetic is proved here. The theorem is a **specialization bridge** that imports already-proved general information into the zero-sector API.

## Role in the overall proof

Up through 0272, the proof has classified golden units into finitely many fifth-power sectors, eliminated the nonzero sectors, and routed the remaining sector $0$ into a separate arithmetic analysis.

Starting with 0273, `SignedGoldenZeroSector.lean` studies the remaining case

$$
\beta=\gamma^5.
$$

The zero-sector descent needs to connect both coordinates of `gamma`, as well as its norm, to the packet's five-adic and power-split data. This theorem is the first norm-side bridge.

Later in the standalone source it is used directly through

```lean
rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
```

in order to transfer divisibility information from `goldenNorm gamma` to `p.exceptional.powerSplit.b`.

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg`

This is the general theorem that contains the real norm argument:

```lean
theorem SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  ...
```

0273 is its specialization with `epsilon := goldenOne`.

### `goldenUnit_one`

This theorem states that `goldenOne` is a `GoldenUnit`:

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

It is consumed directly by

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

in the proof.

### `goldenOne`

This is the project-side concrete representation of the multiplicative identity in the golden integer ring. At the end of the proof, `simp [goldenOne, goldenMul]` unfolds it to its coordinate representation.

### `goldenMul`, `goldenPow`

These are the project-side golden multiplication and power APIs. The hypothesis is

```lean
p.beta = goldenPow gamma 5
```

whereas the general theorem expects

```lean
p.beta = goldenMul goldenOne (goldenPow gamma 5).
```

The final extensionality argument bridges that representational difference.

### `goldenNorm`

This is the norm on `GoldenInt`. It is the subject of the conclusion, but it is not unfolded in this theorem. All norm arithmetic is delegated to the general theorem.

## Proof flow

### 1. Apply the general norm theorem

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

After this step, the only remaining goal is to turn the zero-sector hypothesis into the factorization hypothesis expected by the general theorem.

Conceptually, one only needs to show

$$
\beta=\gamma^5
\Longrightarrow
\beta=1\cdot\gamma^5.
$$

### 2. Rewrite `p.beta` using `hbeta`

```lean
rw [hbeta]
```

This replaces the left-hand occurrence of `p.beta` by `goldenPow gamma 5`.

The remaining goal is essentially the unit law

$$
\gamma^5=1\cdot\gamma^5.
$$

### 3. Reduce equality of `GoldenInt` values to coordinate equalities

```lean
ext <;> simp [goldenOne, goldenMul]
```

`ext` turns the equality of two `GoldenInt` values into equalities of their components. Then `goldenOne` and `goldenMul` are unfolded and `simp` closes each coordinate goal.

No norm computation occurs at this stage.

## Lean-specific processing

### Specialization through `apply`

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

uses the namespace theorem as if it were a method on the packet `p`. The implicit parameter `epsilon` is inferred as `goldenOne` from the supplied unit proof `goldenUnit_one`.

### Rewrite direction

`rw [hbeta]` replaces `p.beta` by the pure fifth power. The reverse direction is not used, because this orientation reduces the remaining factorization goal to a simple identity law.

### `ext`

`ext` decomposes equality of `GoldenInt` values into equality of their components. Rather than relying directly on an abstract `one_mul`, the proof closes through the project-side concrete coordinate representation.

### `<;>`

The combinator applies

```lean
simp [goldenOne, goldenMul]
```

to every goal created by `ext`.

## Redundancy and duplication

The proof is only three lines long, so there is no major redundancy.

Mathematically, however, the final line

```lean
ext <;> simp [goldenOne, goldenMul]
```

reconstructs the fact that `goldenOne` is a left identity for `goldenMul` at the coordinate level.

If the project API exposed a stable lemma such as

```lean
goldenMul_one_left : goldenMul goldenOne x = x
```

or convenient rewrite lemmas connecting `goldenOne` to `1` and `goldenMul` to `(*)`, the proof could potentially be expressed more semantically.

The current proof is nevertheless concrete, local, and robust in the standalone artifact.

## Optimization candidates

### 1. Use a multiplicative-identity API

Potentially, the final two lines could be compressed to something conceptually like

```lean
simpa [golden_mul_eq] using hbeta
```

or a proof based on `one_mul`.

Whether the exact supporting rewrite lemmas are available in the current source/import environment has **not been verified**, because no Lean build is performed in this run.

### 2. Factor out the common zero-sector specialization pattern

The next theorem, `zeroSector_five_not_dvd_gamma_norm`, uses exactly the same shape:

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
rw [hbeta]
ext <;> simp [goldenOne, goldenMul]
```

Therefore one could introduce a helper witnessing

$$
\beta=\gamma^5
\Rightarrow
\beta=1\cdot\gamma^5
$$

and reuse it across the zero-sector specialization lemmas.

Because each proof is already only two or three lines, however, such abstraction may cost more navigation than it saves. The priority is low.

## Required Mathlib import and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

at the top level.

This theorem itself directly uses only structural extensionality, rewriting, simplification, and previously proved project theorems. It does not invoke a heavy Mathlib theorem directly.

The exact minimal import set of the generated source module `SignedGoldenZeroSector.lean` cannot be determined from the standalone artifact alone. Since no Lean build is performed in this run, any attempt to replace `import Mathlib` with a precise set of narrower imports remains **unverified**.

A proper import-minimization pass should inspect the import graph in the source `Deskuma/dkmath` repository for the modules providing:

- the norm/fifth-power bridge,
- `SignedGoldenRamifierStrippedPacket`,
- golden unit definitions and arithmetic,

and then validate the reduced set with Lean.

## Comparator challenge suitability

**Yes, but the difficulty is low.**

A useful challenge would provide the general theorem

```lean
p.gamma_norm_eq_or_eq_neg
```

and

```lean
goldenUnit_one
```

and ask the solver to derive the zero-sector result from

```lean
hbeta : p.beta = goldenPow gamma 5.
```

The challenge tests whether the solver can:

1. reuse the general theorem instead of reproving the norm argument,
2. select `goldenUnit_one` as the unit witness,
3. align `p.beta = gamma^5` with `p.beta = 1 * gamma^5`, and
4. close the `GoldenInt` identity using `ext` and `simp`.

It is therefore better viewed as an **API-specialization / representation-alignment challenge** than as a deep number-theory challenge.

## Relation to the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the GitHub connector does not return the binary PDF body, and the public raw PDF fetch also failed in this run. Therefore the exact PDF page, section, or wording corresponding to this theorem could not be verified, and no such correspondence is guessed here.

The technical explanation in this document is grounded directly in the generated source contained in `Flt5DkMath/FLT5StandAlone.lean` on the target branch and in the verified project theorem APIs around it.

## Next declaration to read

The next declaration is 0274:

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  apply p.five_not_dvd_gamma_norm goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

Whereas 0273 fixes the **magnitude of the zero-sector base norm up to sign** as the packet quantity `b`, 0274 specializes the complementary fact that **five does not divide that norm**.

Together these facts prepare the downstream divisibility and coprimality arguments that connect the coordinates of `gamma` to the packet's power-split data.

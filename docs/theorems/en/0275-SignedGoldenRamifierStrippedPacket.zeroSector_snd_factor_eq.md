# 0275 — `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq`

## Declaration kind

This is a **`theorem`**.

It is a zero-sector coordinate-arithmetic lemma in `DkMath.FLT.Five.SignedGoldenZeroSector`. When the packet value `beta` is a pure fifth power `gamma^5`, the theorem factors its second coordinate into `gamma.snd` times the quartic factor `goldenFifthSndFactor`, and connects that product exactly to the five-adic power-split data stored in the packet.

## Lean type

```lean
/-- Exact signed second-coordinate equation in the zero sector. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
      -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  have hsnd := congrArg (fun x : GoldenInt => x.snd) hbeta
  change p.beta.snd = (goldenPow gamma 5).snd at hsnd
  rw [p.beta_snd, goldenPow_five_snd, goldenFifthSndPoly_eq] at hsnd
  nlinarith
```

Write `gamma = (r,s)` and set

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s).
$$

Then the hypothesis

$$
\beta=\gamma^5
$$

implies

$$
s\,H(r,s)=-5^6 a^{10},
$$

where $a$ is `p.exceptional.powerSplit.a`.

Thus the theorem gives not merely a divisibility statement, but an **exact signed product equation** preserving the sign, the exponent of 5, and the tenth-power component.

## Mathematical meaning

In the zero unit sector, the unit factor has disappeared and `beta` is simply the fifth power

$$
\beta=\gamma^5.
$$

On the other hand, the packet already stores an exact formula for `beta.snd` through `p.beta_snd`.

The theorem compares these two descriptions after projecting to the second coordinate. One side is the packet's known five-adic value; the other side is the fifth-power coordinate formula. Factoring the latter exposes the second coordinate $s$ and the quartic factor $H(r,s)$, yielding the equation

$$
sH=-5^6a^{10}.
$$

This form is crucial because taking natural absolute values later produces

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

Combined with coprimality, this allows all powers of 5 to be forced onto the $|s|$ side and the remaining coprime factors to be separated into tenth powers, which is exactly the normal form required by the later inversion and descent layers.

## Role in the full proof

0273 transports the norm of the zero-sector base to the packet parameter `b`, up to sign. 0274 transports the nondivisibility of that norm by 5 into the zero-sector API.

0275 is the first theorem in this block that **factors the second coordinate of the zero-sector fifth power itself**.

In the canonical source, it is followed by

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq ...
```

and then by `zeroSector_five_not_dvd_sndFactor`, which proves that the quartic factor $H$ is not divisible by 5. Later, `zeroSector_natAbs_product_eq` applies `Int.natAbs` to the present theorem to obtain

$$
|s|\,|H|=5^6a^{10}.
$$

Therefore 0275 is a **major bridge** from a packet-level five-adic invariant to coordinate-level coprime factorization.

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket`

The packet structure. This theorem uses in particular `beta`, `exceptional.powerSplit.a`, and `beta_snd`.

### `p.beta_snd`

This supplies the exact formula for the second coordinate `p.beta.snd`. The present theorem compares that stored value with the second coordinate of `gamma^5`; it does not reprove the packet invariant.

The exact origin of this field/theorem lies in the earlier `SignedGoldenRamifierStripped.lean` layer.

### `goldenPow_five_snd`

This expands the second coordinate of a fifth power in `GoldenInt` into the project-side polynomial expression.

```lean
rw [..., goldenPow_five_snd, ...] at hsnd
```

moves the fifth-power coordinate to that polynomial form.

### `goldenFifthSndPoly_eq`

This rewrites the second-coordinate polynomial into a factorized form involving

$$
s
\qquad\text{and}\qquad
H(r,s).
$$

That factorization is the key shape needed by the downstream zero-sector arithmetic.

### `goldenFifthSndFactor`

The quartic factor appearing in the second coordinate of a fifth power. Later the proof studies its congruence with the square of the golden norm, its coprimality with `s`, and its tenth-power splitting.

### `congrArg`

Lean's general congruence principle, used to apply the projection `(fun x => x.snd)` to the equality `hbeta`.

## Proof flow

### 1. Project `hbeta` to the second coordinate

```lean
have hsnd := congrArg (fun x : GoldenInt => x.snd) hbeta
```

The original equality is an equality of full `GoldenInt` values, but only the second coordinate is needed. The proof therefore projects immediately.

Mathematically,

$$
\beta=\gamma^5
\Longrightarrow
\beta_2=(\gamma^5)_2.
$$

### 2. Normalize the hypothesis into the expected syntax

```lean
change p.beta.snd = (goldenPow gamma 5).snd at hsnd
```

This changes only the presentation of the proposition up to definitional equality, placing it in a syntactic form on which the following rewrite lemmas match directly.

### 3. Rewrite both sides to exact formulas

```lean
rw [p.beta_snd, goldenPow_five_snd, goldenFifthSndPoly_eq] at hsnd
```

The left-hand side becomes the packet invariant. The right-hand side becomes the fifth-power coordinate formula and then its factorization.

After this step, `hsnd` is an integer polynomial equation involving only `gamma.snd`, `goldenFifthSndFactor`, `5`, and `powerSplit.a`.

### 4. Close the coefficient arithmetic with `nlinarith`

```lean
nlinarith
```

What remains is polynomial arithmetic and fixed-coefficient normalization, so `nlinarith` derives the target form

$$
sH=-5^6a^{10}.
$$

No new number-theoretic input enters at this final step.

## Lean-specific processing

### Projection via `congrArg`

Instead of decomposing a structure equality with `ext`, the proof extracts only the coordinate it needs by applying congruence to the second-coordinate projection. This is especially direct here.

### `change ... at hsnd`

The hypothesis is reshaped within definitional equality so that the rewrite matcher can apply the project lemmas cleanly. This is representational rather than mathematical work.

### Dot notation in `p.beta_snd`

The packet argument `p` is supplied through dot notation, making the packet invariant read like a method attached to `p`.

### `nlinarith`

The rewritten equality is already polynomial in the relevant integer expressions. `nlinarith` is appropriate because it uses `hsnd` as an arithmetic hypothesis to derive the target equality; a bare `ring` would normalize identities but would not by itself exploit the hypothesis in the same way.

## Redundancy and duplication

The proof is only four lines long, so there is almost no local redundancy.

The line

```lean
change p.beta.snd = (goldenPow gamma 5).snd at hsnd
```

may become unnecessary if the project definitions or simplifier attributes are strengthened enough for the rewrite sequence to match directly.

Likewise, the consecutive use of `goldenPow_five_snd` and `goldenFifthSndPoly_eq` could be collapsed if the public API provided a direct factorized fifth-coordinate theorem of the schematic form

```lean
(goldenPow gamma 5).snd = 5 * gamma.snd * goldenFifthSndFactor ...
```

Whether such a helper is worthwhile depends on how often this two-step rewrite pattern recurs.

## Optimization candidates

### 1. Direct factorized fifth-coordinate API

If `goldenPow_five_snd` followed by `goldenFifthSndPoly_eq` is a common pattern, a theorem exposing the factorized second coordinate directly would shorten downstream proofs and make the intended arithmetic structure more explicit.

### 2. Make the final scalar arithmetic explicit

For Comparator or pedagogical use, it may be preferable to name the rewritten exact equation and use `ring_nf` or an explicit cancellation lemma rather than a final `nlinarith`. This could make the transition from the packet's power of 5 to the final $5^6$ factor more visible.

The current proof, however, is compact and robust, so this is a readability trade-off rather than a correctness issue.

### 3. Test whether `change` can be removed

It may be possible to replace the `change` step by `simpa`, or let `rw` work directly, depending on the present reducibility and simp setup. This was **not verified**, because no Lean build is performed in this task.

## Required Mathlib imports and import optimization

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

and its manifest places the source theorem in `DkMath/FLT/Five/SignedGoldenZeroSector.lean`, after earlier modules including `SignedGoldenRamifierStripped`, `SignedGoldenFifthPower`, `GoldenFifthPowerCoordinates`, and `SignedGoldenSectorArithmetic`.

The proof mechanisms directly used by 0275 are structure projection, `congrArg`, rewriting, integer polynomial arithmetic, and `nlinarith`.

However, the **minimal Mathlib import set for the original module cannot be determined from the concatenated standalone artifact alone**. In particular, the import chain for `nlinarith` must be separated from the project-side golden arithmetic dependencies and then checked with Lean. Since this run does not perform a Lean build, any concrete replacement of `import Mathlib` would remain unverified.

## Relation to the existing PDFs

The target branch contains

- `FLT5-main-ja-v0-r1.pdf`
- `FLT5-main-en-v0-r1.pdf`

under `docs/pdf`.

In this run, the PDF binaries could not be retrieved in a form suitable for content analysis, so the exact page number, section number, and whether the same equation appears verbatim in the PDFs are **unverified**. Accordingly, this document does not guess a PDF location; the technical account is grounded primarily in the canonical Lean source in the repository.

## Comparator challenge suitability

**Suitable, with low-to-medium difficulty.**

A useful challenge would provide

- `hbeta : p.beta = goldenPow gamma 5`,
- `p.beta_snd`,
- `goldenPow_five_snd`,
- `goldenFifthSndPoly_eq`,

and ask for the goal

```lean
gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
  -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

The challenge tests whether the solver can

1. extract exactly the required coordinate from a `GoldenInt` equality,
2. use the coordinate-expansion and factorization lemmas in the correct order, and
3. close the final polynomial arithmetic without unnecessary expansion.

Because recognizing `congrArg` as the right projection tool is part of the task, this is more informative than a pure rewrite exercise.

## Next declaration to read

The next declaration should be **0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq`**.

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

After 0275 establishes the exact product equation, 0276 shows that the quartic factor $H(r,s)$ agrees modulo 5 with the square of the golden norm. Combining this with 0274, which gives $5\nmid N(\gamma)$, leads naturally to the next exclusion $5\nmid H(r,s)$.

Thus the dependency order is naturally 0275 → 0276 → `zeroSector_five_not_dvd_sndFactor`.

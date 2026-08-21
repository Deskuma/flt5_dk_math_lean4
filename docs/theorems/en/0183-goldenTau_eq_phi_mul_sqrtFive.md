# 0183 — `goldenTau_eq_phi_mul_sqrtFive`

## Lean type

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

This is a `theorem` identifying the distinguished ramified element `goldenTau`, defined in 0178, with the product of 0161 `goldenPhi` and 0177 `goldenSqrtFive`.

## Mathematical statement

The relevant definitions are

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
def goldenTau : GoldenInt := ⟨2, 1⟩
```

and mathematically represent

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\sqrt5=2\varphi-1,\qquad
\tau=2+\varphi.
$$

The theorem states

$$
\tau=\varphi\sqrt5,
$$

or equivalently

$$
2+\varphi=\varphi(2\varphi-1).
$$

Using the defining relation

$$
\varphi^2=\varphi+1,
$$

one obtains

$$
\varphi(2\varphi-1)=2\varphi^2-\varphi
=2(\varphi+1)-\varphi
=\varphi+2.
$$

## Role in the full proof

Declarations 0177–0182 prepare two concrete elements carrying the ramification above five.

- `goldenSqrtFive = 2φ - 1` has square `5` and norm `-5`.
- `goldenTau = 2 + φ` is the distinguished ramifier whose norm is shown immediately afterward to be `5`.

The present theorem shows that these are not unrelated elements: they differ by multiplication by `φ`.

$$
\tau=\varphi\sqrt5.
$$

Thus the two concrete representatives belong to the same ramified associate picture over `5`. Combined with `goldenNorm_tau`, `goldenNorm_sqrtFive`, and `goldenNorm_phi`, the signs of their norms become structurally consistent through the factor of norm `-1` contributed by `φ`.

Later, `exists_goldenTau_factor_of_five_dvd` extracts an actual `goldenTau` factor from the integer condition `5 ∣ 2*M+N`. The present theorem therefore explains how that distinguished factor is related to the square-root representative of the same ramified phenomenon.

## Direct dependencies

The declarations appearing directly are:

- 0161 `goldenPhi`
- 0177 `goldenSqrtFive`
- 0178 `goldenTau`
- 0124 `goldenMul`

The mathematical explanation also uses 0165 `golden_phi_sq`, namely

$$
\varphi^2=\varphi+1.
$$

However, the Lean proof does not rewrite with `golden_phi_sq`; it closes the concrete coordinate equality directly by `decide`.

Conceptually,

$$
\texttt{goldenPhi},\ \texttt{goldenSqrtFive},\ \texttt{goldenTau},\ \texttt{goldenMul}
\longrightarrow
\texttt{goldenTau_eq_phi_mul_sqrtFive}.
$$

## Proof flow

The Lean proof is a single line:

```lean
by
  decide
```

After unfolding the definitions, the right-hand side becomes

```lean
goldenMul ⟨0, 1⟩ ⟨-1, 2⟩
```

and `goldenMul` is defined by

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

Hence

$$
(0,1)(-1,2)
=
(0\cdot(-1)+1\cdot2,
 0\cdot2+1\cdot(-1)+1\cdot2)
=(2,1),
$$

which is exactly `goldenTau = ⟨2,1⟩`.

Therefore the kernel is checking a completely closed integer-coordinate equality rather than an abstract algebraic-number argument.

## Lean-specific processing

`decide` is available because the proposition reduces to equality of two fully concrete `GoldenInt` values and that equality is decidable.

There are no variables or hypotheses, so after definitional reduction Lean can delegate the closed arithmetic equality to the decision procedure.

A more explicit coordinate proof could plausibly be written as

```lean
  ext <;> norm_num [goldenTau, goldenPhi, goldenSqrtFive, goldenMul]
```

but no Lean build is performed in this museum pass, so that exact alternative is not verified.

Another style would use standard multiplication notation together with `golden_phi_sq` to expose the mathematical derivation from `φ² = φ + 1`. The current proof instead favors the explicit coordinate model and minimum proof overhead.

## Redundancy and duplication

Since both `goldenTau` and `goldenSqrtFive` are already explicit coordinates, the theorem adds almost no computational information: it is a closed equality that can be decided directly.

Its API role is nevertheless substantial. It names the fact that the two ramifier presentations are related by multiplication by `φ`, which is more informative than repeatedly unfolding coordinates.

A possible duplication is that one could define

```lean
def goldenTau : GoldenInt := goldenMul goldenPhi goldenSqrtFive
```

and make the present theorem essentially definitional. That design would then require a separate theorem exposing the useful coordinate identity `goldenTau = ⟨2,1⟩`.

The current design chooses the coordinate form as the definition and records the algebraic provenance as a theorem.

## Optimization candidates

Three design families are worth considering.

1. **Keep the current design**
   - `goldenTau := ⟨2,1⟩`.
   - Prove `τ = φ√5` separately.
   - Downstream integer-coordinate factor extraction remains simple.

2. **Make the algebraic formula primary**
   - Define `goldenTau := goldenPhi * goldenSqrtFive`.
   - Prove the coordinate form `⟨2,1⟩` separately.
   - Provenance is stronger, but coordinate computations gain an extra unfolding layer.

3. **Expose the associate structure explicitly**
   - Once `φ` is available as a unit, formulate that `goldenTau` and `goldenSqrtFive` are associated.
   - From the divisibility / valuation viewpoint, the associate class may be more fundamental than this specific equality.

In particular, after `goldenUnit_phi` is established, a theorem expressing

$$
\mathrm{Associated}(\tau,\sqrt5)
$$

could connect the ramification discussion more directly to Mathlib's standard factorization language.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself needs only a small surface:

- `GoldenInt` and decidable equality
- `goldenMul`
- `goldenPhi`
- `goldenSqrtFive`
- `goldenTau`
- `decide`

No advanced analytic or number-theoretic theorem is directly invoked.

The full `GoldenOrder` module, however, also uses ring structures, `Zsqrtd`, `omega`, `ring`, and `norm_num`, so the true minimal module import set is governed by the wider file rather than this theorem alone. Because no Lean build is run here, an exact minimal import list remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. This is a compact closed theorem that supports several sharply different implementations.

Possible contestants are:

- A: current `by decide`
- B: explicit coordinate proof using `ext` and `norm_num`
- C: algebraic proof using `φ² = φ + 1`
- D: redefine `goldenTau` algebraically so the equality becomes definitional

Useful metrics include:

- proof-term simplicity
- visibility of mathematical provenance
- robustness under definition changes
- downstream coordinate-computation cost
- dependence on `simp`, `ring`, or `decide`

The current proof is extremely short and robust, but the mathematical reason for `τ = φ√5` is carried mainly by the declaration names and surrounding definitions rather than by the proof script itself.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on `docs/flt5-theorem-museum-v2`. It contains the sequence

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide

theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

The branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small Lean theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

that is, **0184 `goldenNorm_tau`**.

After 0183 establishes

$$
\tau=\varphi\sqrt5,
$$

the next step makes the distinguished ramifier's norm explicit:

$$
N(\tau)=5.
$$

This promotes `goldenTau` from a useful coordinate representative to an explicit norm-five element for the subsequent divisibility and ramification machinery.

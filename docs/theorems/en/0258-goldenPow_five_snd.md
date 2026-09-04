# 0258 — `goldenPow_five_snd`

## Lean type

```lean
/-- Exact second coordinate of `gamma^5`; it contains the visible factor `5*q`. -/
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

This is a `theorem`. It states that when the fifth power of a golden integer `gamma` is computed through the raw API `goldenPow`, its second coordinate is exactly the polynomial introduced in 0256 as `goldenFifthSndPoly`.

## Mathematical statement

Write `gamma = p + qφ`. Since the golden order satisfies

$$
\varphi^2=\varphi+1,
$$

the fifth power reduces in the basis `1,φ` to

$$
\gamma^5=(p+q\varphi)^5=A(p,q)+B(p,q)\varphi.
$$

Declaration 0256 defines the second-coordinate polynomial by

$$
B(p,q)=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right).
$$

The present theorem proves that this is not merely a candidate formula: it is exactly the `.snd` coordinate of the actual raw fifth power `goldenPow gamma 5`.

Thus

$$
(\gamma^5)_{\mathrm{snd}}
=
\mathrm{goldenFifthSndPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

In particular, the right-hand side is definitionally of the form `5 * q * (...)`, so the second coordinate of every fifth power has a visible factor `5`.

## Role in the full proof

Declarations 0255 and 0256 name the two coordinate polynomials of a fifth power. Declarations 0257 and 0258 connect those polynomials to the actual object `goldenPow gamma 5`. Declaration 0257 handles the first coordinate, and 0258 handles the second, so the explicit representation

$$
\gamma^5
\longleftrightarrow
\bigl(A(p,q),B(p,q)\bigr)
$$

is now complete.

The second-coordinate formula is especially important because `goldenFifthSndPoly` visibly contains the factor

$$
5q.
$$

Later five-adic sector arguments can therefore read divisibility by `5` directly from the second coordinate of a fifth power.

In the source, later theorems such as `golden_unit_zero_mul_fifth_snd`, `golden_unit_one_mul_fifth_snd`, `golden_unit_two_mul_fifth_snd`, `golden_unit_three_mul_fifth_snd`, and `golden_unit_four_mul_fifth_snd` rewrite with `goldenPow_five_fst` and this theorem to express the second coordinate of `φ^i * gamma^5` as linear combinations of the two named coordinate polynomials.

Further downstream, `five_dvd_goldenFifthSndPoly` exposes

$$
5\mid B(p,q),
$$

which becomes an input to the exclusion of nonzero unit sectors and to the zero-sector factorization arguments.

## Direct dependencies

The Lean proof directly refers to:

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- `goldenOne`
- 0256 `goldenFifthSndPoly`
- `simp`
- `ring`

Mathematically, the defining relation

$$
\varphi^2=\varphi+1
$$

from 0165 `golden_phi_sq` is the background reason the fifth power reduces to two coordinates. The proof does not explicitly rewrite with that named theorem, because the coordinate definition of `goldenMul` already incorporates the reduction rule.

## Proof flow

The proof is structurally identical to 0257:

```lean
by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

1. `simp [goldenPow]` unfolds the recursion at the fixed exponent `5`.
2. `goldenMul` is unfolded into its explicit two-coordinate multiplication rule.
3. `goldenOne` and `goldenFifthSndPoly` are unfolded.
4. The goal becomes an integer polynomial identity in `gamma.fst` and `gamma.snd`.
5. `ring` normalizes both sides and closes the equality.

So the mathematical content of the proof is exactly the coefficient calculation for the second coordinate of `(p+qφ)^5` in the golden basis.

## Lean-specific processing

`goldenPow` is a project-specific raw recursion rather than Mathlib's standard `^`. Because the exponent is fixed to `5`, fully unfolding it with `simp [goldenPow]` is practical.

The statement is already a scalar equality involving `.snd`, so no `GoldenInt.ext` step is needed; the proof works directly on the second coordinate.

Declaration 0160 `golden_pow_eq` already proves `goldenPow gamma 5 = gamma ^ 5`, but the present theorem deliberately stays in the raw coordinate API. This makes the connection with the explicit implementation of `goldenMul` easy to audit.

After unfolding, all expressions lie in the integer polynomial ring, which is why `ring` can finish the proof.

## Redundancy and duplication

Declaration 0257 `goldenPow_five_fst` and the present theorem have almost identical proof patterns:

- 0257: `.fst` and `goldenFifthFstPoly`
- 0258: `.snd` and `goldenFifthSndPoly`

One possible redesign would introduce a single coordinate-pair theorem such as

```lean
theorem goldenPow_five_coords (gamma : GoldenInt) :
    goldenPow gamma 5 =
      ⟨goldenFifthFstPoly gamma.fst gamma.snd,
        goldenFifthSndPoly gamma.fst gamma.snd⟩ := by
  ext <;> simp [goldenPow, goldenMul, goldenOne,
    goldenFifthFstPoly, goldenFifthSndPoly] <;> ring
```

and derive 0257 and 0258 as projection corollaries.

However, the current scalar split is convenient downstream because proofs often rewrite only one coordinate. This is particularly useful in the unit-sector block, where the second coordinate is repeatedly inspected in isolation.

## Optimization candidates

1. **Use a single two-coordinate theorem as the canonical source**
   - this would reduce proof duplication and make 0257/0258 thin projection lemmas.

2. **Expose a standard-power version using `gamma ^ 5`**
   - 0160 `golden_pow_eq` could bridge the result into ordinary algebra notation.

3. **Expose the visible factor `5` directly**
   - together with `five_dvd_goldenFifthSndPoly`, a theorem such as `5 ∣ (goldenPow gamma 5).snd` could shorten consumer proofs.

4. **Generalize through a coordinate recurrence for arbitrary exponents**
   - this would increase reuse, although the explicit fifth-degree formula is arguably clearer for an FLT5-specific development.

5. **Clarify the raw/standard API boundary**
   - the development currently carries both `goldenPow`/`goldenMul` and standard `^`/`*`; additional bridge lemmas could reduce repeated representation changes.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The external functionality used directly by this theorem is mainly:

- polynomial arithmetic over `ℤ`
- `simp`
- `ring`

So the declaration in isolation likely needs substantially less than all of `Mathlib`.

However, the surrounding `GoldenFifthPowerCoordinates.lean` module later uses divisibility, `Fin 5`, `fin_cases`, `omega`, `grind`, and related arithmetic machinery, so the minimal import set at module scope will be broader than the surface required by 0258 alone.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Natural contestants include:

- A: current `simp` + `ring`
- B: prove one two-coordinate theorem with `ext` and project `.snd`
- C: use 0160 `golden_pow_eq` and prove the statement through standard `^`
- D: derive the exponent-five formula from a general coordinate recurrence
- E: compare alternative normalization tactics such as `ring_nf`

Useful metrics are proof length, unfolding volume, raw API dependence, compatibility with standard algebra notation, duplication with 0257, and downstream rewrite ergonomics.

The comparison between A and B is especially useful for evaluating whether consumer-friendly scalar theorems should remain primary, or whether a pair theorem should be the canonical source of truth.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In the source, the present theorem appears immediately after 0257 `goldenPow_five_fst`, and the next declaration is `goldenPhi_pow_zero`.

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is **0259 `goldenPhi_pow_zero`**:

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
```

Declarations 0257 and 0258 complete the explicit polynomial description of the two coordinates of `gamma^5`. Declaration 0259 begins the block preparing the concrete unit representatives `1,φ,φ^2,φ^3,φ^4`: it first fixes the exponent-zero representative `1`, after which the source develops the second-coordinate formulas for each unit sector.
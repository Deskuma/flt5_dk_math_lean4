# 0257 — `goldenPow_five_fst`

## Lean type

```lean
/-- Exact first coordinate of `gamma^5`. -/
theorem goldenPow_five_fst (gamma : GoldenInt) :
    (goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

This is a `theorem`. It states that when the fifth power of a golden integer `gamma` is computed through the explicit raw API `goldenPow`, its first coordinate is exactly the polynomial introduced in 0255 as `goldenFifthFstPoly`.

## Mathematical statement

Write

$$
\gamma=p+q\varphi.
$$

Since the golden order satisfies

$$
\varphi^2=\varphi+1,
$$

the fifth power reduces to the basis `1, φ` as

$$
\gamma^5=(p+q\varphi)^5=A(p,q)+B(p,q)\varphi.
$$

Declaration 0255 defines the first-coordinate polynomial

$$
A(p,q)=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

as `goldenFifthFstPoly p q`.

The present theorem proves that this is not merely a candidate expansion but the actual `.fst` coordinate of the raw fifth power `goldenPow gamma 5`:

$$
(\gamma^5)_{\mathrm{fst}}
=
\mathrm{goldenFifthFstPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

## Role in the full proof

Declarations 0255 and 0256 name the two coordinate polynomials of a fifth power, but by themselves they do not yet connect those polynomials to the actual `goldenPow` computation. Declaration 0257 and the following 0258 `goldenPow_five_snd` provide exactly that bridge.

After this theorem, downstream proofs no longer need to repeatedly unfold the raw recursion of `goldenPow` when reasoning about the first coordinate. They can rewrite directly to `goldenFifthFstPoly` and continue with ordinary integer polynomial arithmetic.

This is especially important in the unit-sector block. The second coordinates of

$$
\varphi^i\gamma^5,
\qquad i=0,1,2,3,4,
$$

become linear combinations of the first-coordinate polynomial `A` and the second-coordinate polynomial `B`. Those proofs use rewrites such as

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

to move completely from raw fifth-power coordinates to the named polynomial API.

Later modulo-five arguments analyze `goldenFifthFstPoly` through congruence information of the form

$$
A(p,q)\equiv p^5+3q^5 \pmod 5,
$$

which contributes to the elimination of the nonzero unit sectors. The present theorem is the formal gateway from `gamma^5` into that arithmetic layer.

## Direct dependencies

The Lean proof directly refers to:

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- `goldenOne`
- 0255 `goldenFifthFstPoly`
- `simp`
- `ring`

Mathematically, the underlying identity is governed by 0165 `golden_phi_sq`, namely

$$
\varphi^2=\varphi+1.
$$

However, the proof does not rewrite by that named theorem. The coordinate definition of `goldenMul` already incorporates the reduction rule, so unfolding `goldenPow` directly produces an integer polynomial in the `1, φ` coordinates.

## Proof flow

The proof has only two tactic stages:

```lean
by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

1. `simp` unfolds the recursive definition of `goldenPow` at the fixed exponent `5`.
2. Each multiplication is expanded through the explicit coordinate formula `goldenMul`.
3. `goldenOne` and `goldenFifthFstPoly` are unfolded as well.
4. The remaining goal is an integer polynomial identity in `gamma.fst` and `gamma.snd`.
5. `ring` normalizes both sides and closes the equality.

Thus the mathematical content of the proof is exactly the coefficient computation obtained by expanding the fifth power in the explicit golden-order coordinates.

## Lean-specific processing

`goldenPow` is not merely standard `^`; it is the raw recursive power operation defined by this development. Since the exponent is the concrete numeral `5`, `simp [goldenPow]` can unfold the recursion a finite number of times.

Likewise, `goldenMul` encodes

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi.
$$

Repeated multiplication creates a large expression, but it remains an ordinary polynomial over `ℤ`, which is exactly the setting where `ring` is effective.

The proof does not need `GoldenInt.ext`, because the theorem statement is already a scalar equality about `.fst` rather than an equality of complete golden integers.

Declaration 0160 `golden_pow_eq` already identifies `goldenPow gamma 5` with the standard notation `gamma ^ 5`, but the current proof deliberately stays in the raw coordinate API. This keeps the expansion close to the explicit implementation and makes the coordinate audit straightforward.

## Redundancy and duplication

Declaration 0257 and the following 0258 `goldenPow_five_snd` have nearly identical proof shapes:

- 0257 handles `.fst`;
- 0258 handles `.snd`.

Both use

```lean
simp [goldenPow, goldenMul, goldenOne, ...]
ring
```

so there is some proof-pattern duplication.

A possible alternative is a paired theorem such as

```lean
theorem goldenPow_five_coords (gamma : GoldenInt) :
    goldenPow gamma 5 =
      ⟨goldenFifthFstPoly gamma.fst gamma.snd,
        goldenFifthSndPoly gamma.fst gamma.snd⟩ := by
  ext <;> simp [...] <;> ring
```

and then derive 0257 and 0258 as projection corollaries.

The current scalar split nevertheless has a practical advantage: downstream arithmetic often rewrites only one coordinate at a time. In particular, the unit-sector formulas use the first and second coordinate polynomials with different coefficients, so separate scalar rewrite lemmas are convenient.

## Optimization candidates

1. **Add a theorem for both coordinates at once**
   - make `goldenPow_five_coords` the canonical theorem and derive 0257/0258 as projections.

2. **Expose a standard-power version**
   - using 0160 `golden_pow_eq`, provide

```lean
(gamma ^ 5).fst = goldenFifthFstPoly gamma.fst gamma.snd
```

   for downstream code written in Mathlib's standard notation.

3. **Derive the result from a general coordinate recurrence**
   - define the two-coordinate recurrence for `(p+qφ)^n` and specialize to `n=5`.
   - this improves generality but is less transparent for an FLT5-specific audit.

4. **Reduce the size of the expansion before `ring`**
   - intermediate coordinate lemmas could make the proof term more local.
   - however, the current proof is already short and robust.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The external functionality directly needed by this theorem is mainly:

- integer ring arithmetic;
- `simp`;
- `ring`.

Therefore the theorem in isolation likely needs much less than all of `Mathlib`.

The surrounding `GoldenFifthPowerCoordinates.lean` module, however, later uses divisibility, primality, `Fin 5`, `fin_cases`, `omega`, and `grind`, so the minimal import set for the whole module is necessarily broader than the surface used by 0257 alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current `simp` + `ring` proof;
- B: prove a two-coordinate theorem with `ext` and project `.fst`;
- C: rewrite through 0160 `golden_pow_eq` and work with standard `^`;
- D: derive from a general coordinate recurrence and specialize to `n=5`;
- E: control the explicit expansion using `ring_nf` or smaller helper lemmas.

Useful comparison axes are proof-term size, dependence on the raw API, compatibility with standard algebra notation, auditability of the coordinate expansion, duplication with 0258, and downstream rewrite ergonomics.

The contrast between A and B is particularly useful for measuring the trade-off between separate consumer-friendly coordinate lemmas and a single paired theorem as the canonical source of truth.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, 0255 `goldenFifthFstPoly` and 0256 `goldenFifthSndPoly` are immediately followed by this theorem, and then by 0258 `goldenPow_five_snd`.

The target branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small coordinate theorem was not identified in this run, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0258 `goldenPow_five_snd`**:

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

Declaration 0257 connects the first coordinate of the fifth power to its named polynomial API; 0258 completes the same bridge for the second coordinate. Together they fully reduce the coordinates of `gamma^5` to the explicit polynomial pair introduced in 0255 and 0256.
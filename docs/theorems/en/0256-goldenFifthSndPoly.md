# 0256 — `goldenFifthSndPoly`

## Lean type

```lean
/-- Second-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthSndPoly (p q : ℤ) : ℤ :=
  5 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 +
    3 * p * q ^ 3 + q ^ 4)
```

This is a `def`, not a theorem. It gives a named integer polynomial for the second coordinate obtained when the fifth power of the golden integer

$$
\gamma=p+q\varphi
$$

is reduced to the basis `1, φ`.

## Mathematical statement and meaning of the declaration

In the golden order one has

$$
\varphi^2=\varphi+1,
$$

so the fifth power can be written uniquely as

$$
(p+q\varphi)^5=A(p,q)+B(p,q)\varphi.
$$

Declaration 0255 `goldenFifthFstPoly` defines the first coordinate $A(p,q)$. The present definition gives the second coordinate

$$
B(p,q)
=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right).
$$

The most important feature is visible already in the syntax: the second coordinate contains the explicit factor

$$
5q.
$$

Therefore the second coordinate of every fifth power in the golden order is divisible by `5`.

This is not merely an expansion formula. It exposes the five-adic structure needed by the later unit-sector arithmetic directly in the definition.

## Role in the full proof

The declarations beginning at 0255 in `GoldenFifthPowerCoordinates.lean` convert a factorization of the form

$$
\beta=\varepsilon\gamma^5
$$

into explicit coordinate congruences.

The present definition is the central second-coordinate quantity in that block. The source immediately follows it with

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

which identifies the actual second coordinate of `goldenPow gamma 5` with this polynomial.

Later the source proves

```lean
theorem five_dvd_goldenFifthSndPoly (r s : ℤ) :
    (5 : ℤ) ∣ goldenFifthSndPoly r s := by
  ...
```

and combines that fact with the formulas for the second coordinate in the five representative unit sectors. This supplies the five-adic obstruction used to eliminate nonzero sectors.

The source also later isolates the quartic factor

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

as `goldenFifthSndFactor`, rewriting the present definition as

$$
goldenFifthSndPoly(r,s)=5s\,H(r,s).
$$

That factorization is reused in the later zero-sector descent.

## Direct dependencies

Because this declaration is a `def`, it has no proof script. Its direct Lean dependency surface is just basic integer arithmetic:

- `ℤ`
- addition and multiplication
- natural-number powers `^`

Conceptually it is paired with 0255 `goldenFifthFstPoly`, and its mathematical derivation relies on the golden-order relation

$$
\varphi^2=\varphi+1.
$$

Relevant upstream objects include:

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- 0165 `golden_phi_sq`

These do not appear directly in the body of the definition. The next coordinate theorem `goldenPow_five_snd` establishes the connection to the actual golden fifth power.

## Construction flow

The definition fixes the second coordinate obtained after expanding the fifth power and repeatedly reducing powers of `φ` using `φ² = φ + 1`.

Before factoring, the second coordinate can be written as

$$
5p^4q+10p^3q^2+20p^2q^3+15pq^4+5q^5.
$$

Factoring out `5q` gives

$$
5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right).
$$

The current definition deliberately chooses this factored form so that the five-adic information is visible immediately.

## Lean-specific processing

The declaration itself uses no tactics:

```lean
def goldenFifthSndPoly (p q : ℤ) : ℤ := ...
```

It is a pure integer polynomial, so later evaluation and normalization can be handled by standard tools such as `ring`, `norm_num`, and `simp`.

In the following theorem `goldenPow_five_snd`, Lean unfolds `goldenPow`, `goldenMul`, and `goldenOne`, then closes the resulting polynomial identity by `ring`. The named definition therefore hides a large raw coordinate expansion behind a compact rewrite surface.

The syntactic factorization `5 * q * (...)` is also useful proof engineering: later divisibility proofs can construct a witness for `5 ∣ ...` directly, without first performing a large polynomial normalization.

## Redundancy and duplication

Declaration 0255 `goldenFifthFstPoly` and the present definition store the two coordinates of the same fifth-power expansion as separate scalar functions.

In principle they could be bundled as a pair, for example:

```lean
def goldenFifthCoords (p q : ℤ) : ℤ × ℤ :=
  (goldenFifthFstPoly p q, goldenFifthSndPoly p q)
```

There are, however, good reasons for the current separation:

- the first and second coordinates have very different five-adic behavior;
- the second coordinate needs its explicit `5*q` factor repeatedly;
- the unit-sector formulas combine the two coordinates with different coefficients;
- scalar coordinate lemmas are easy to rewrite independently.

Thus there is API-level duplication, but the separation is well aligned with downstream arithmetic.

## Optimization candidates

1. **Bundle both coordinates into a pair definition**
   - this could allow the common fifth-power derivation to be proved once.

2. **Define `goldenFifthSndFactor` first**
   - later source introduces the quartic factor separately and proves

$$
goldenFifthSndPoly(r,s)=5s\,goldenFifthSndFactor(r,s).
$$

   - defining the present function as `5 * q * goldenFifthSndFactor p q` from the start would reduce duplication.

3. **Introduce a general coordinate recurrence in the exponent**
   - the relation `φ² = φ + 1` yields a recurrence for the two coordinates of `(p+qφ)^n`, with `n=5` as a specialization.
   - for an FLT5-specific development, however, the current explicit polynomial is easier to audit.

4. **Move to a polynomial-level abstraction**
   - one could encode the expansion with `MvPolynomial` or a related API, but this may be excessive for a downstream development dominated by concrete integer arithmetic.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This definition alone requires only a very small surface: integers together with basic ring and power notation. It therefore almost certainly admits a much smaller import set than all of `Mathlib`.

The surrounding module, however, soon uses `ring`, divisibility lemmas, finite case splits over unit sectors, and other arithmetic tools. The practical minimal import set must therefore be measured at module scope rather than from this declaration alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current explicitly factored polynomial
- B: the fully expanded form `5p^4q + 10p^3q² + ...`
- C: define `goldenFifthSndFactor` first and set the polynomial to `5*q*H`
- D: bundle first and second coordinates into one pair
- E: omit a named polynomial and repeatedly expand `goldenPow` directly

Useful comparison axes are proof length, ease of proving `5 ∣ snd`, rewrite ergonomics, auditability of the expression, duplication, and readability of the later unit-sector arithmetic.

The contrast between A and B is especially instructive: the formulas are mathematically identical, but A tests how much formal proof engineering benefits from making the five-adic factor visible syntactically.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order this definition follows 0255 `goldenFifthFstPoly`, and is followed by the coordinate theorems `goldenPow_five_fst` and `goldenPow_five_snd`.

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0257 `goldenPow_five_fst`**:

```lean
theorem goldenPow_five_fst (gamma : GoldenInt) :
    (goldenPow gamma 5).fst =
      goldenFifthFstPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

With the two coordinate polynomials now defined by 0255 and 0256, declaration 0257 begins proving that they are exactly the coordinates of the actual term `goldenPow gamma 5`.
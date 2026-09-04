# 0255 — `goldenFifthFstPoly`

## Lean type

```lean
/-- First-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

This is a `def`, not a theorem. It gives a named integer polynomial for the first coordinate of the fifth power of the golden integer

$$
\gamma=p+q\varphi.
$$

## Mathematical statement and meaning of the declaration

In the golden order one has

$$
\varphi^2=\varphi+1.
$$

Therefore the ordinary binomial expansion of `(p+qφ)^5` can be reduced repeatedly to the basis `1,φ`, giving

$$
(p+q\varphi)^5=A(p,q)+B(p,q)\varphi.
$$

The present definition names the first coordinate

$$
A(p,q)
=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

as `goldenFifthFstPoly p q`.

This declaration does not yet prove that the polynomial agrees with `(goldenPow gamma 5).fst`. That bridge is supplied by the later theorem `goldenPow_five_fst`. Thus 0255 is the declaration that fixes the explicit first-coordinate formula itself.

## Role in the full proof

By 0254, the ramifier-stripped packet has been connected to a generic coprime-factor theorem capable of producing

$$
\beta=\varepsilon\gamma^5.
$$

The next module, `GoldenFifthPowerCoordinates.lean`, converts this abstract fifth-power representation back into explicit integer coordinates so that arithmetic divisibility information can be read off.

Its module comment states that for `gamma=p+q*φ` it names the two coordinate polynomials of `gamma^5`, then computes the second coordinate after multiplication by the five representative units

$$
1,\varphi,\ldots,\varphi^4.
$$

These formulas turn unit classes modulo fifth powers into five explicit arithmetic sectors. Here “sector” is an algebraic unit class, not a geometric or analytic region.

Downstream, `goldenFifthFstPoly` is used to:

- identify the exact first coordinate of `gamma^5` in `goldenPow_five_fst`;
- express second-coordinate formulas after multiplication by `φ^i`;
- prove the congruence `goldenFifthFstPoly r s ≡ r + 3s (mod 5)`;
- derive divisibility of `goldenNorm gamma` from divisibility of the first fifth-power coordinate;
- drive the five-adic contradiction excluding nonzero unit sectors.

Thus the definition is the coordinate-level interface between abstract fifth-power extraction and the later explicit five-adic sector arithmetic.

## Direct dependencies

The direct dependency surface is very small because this is simply an integer polynomial definition:

- `ℤ`
- integer addition and multiplication
- natural-number powers `(^)`

Neither `GoldenInt`, `goldenPow`, nor `goldenMul` occurs in the type of the definition. Its mathematical origin is the fifth power in the golden order, but the API deliberately extracts the result as a pure bivariate integer polynomial.

Conceptually, the background relation

$$
\varphi^2=\varphi+1
$$

and the binomial expansion explain the coefficients, but they are not theorem dependencies of this `def` itself.

## Construction flow

The declaration is a single explicit definition:

```lean
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

Mathematically the construction is:

1. expand `(p+qφ)^5` by the binomial theorem;
2. repeatedly reduce powers of `φ` using `φ²=φ+1`;
3. collect the coefficient of the basis vector `1`;
4. name the resulting integer polynomial.

Lean does not encode that derivation inside the definition. Instead, the following theorem `goldenPow_five_fst` unfolds the coordinate implementation and proves agreement using `simp` and `ring`.

## Lean-specific processing

There is no tactic proof in this declaration. The right-hand side of the `def` is the computational rule.

Because `p q : ℤ` are explicit, the coefficients `10`, `3`, and all powers are elaborated in the integer ring. Downstream proofs can unfold the definition with code of the form

```lean
simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
ring
```

and reduce the goal to polynomial normalization over `ℤ`.

The choice to accept raw integer coordinates instead of a `GoldenInt` also matters: modular statements can be formulated for arbitrary integers `r,s` without going through structure projections.

## Redundancy and duplication

In principle, downstream theorems could repeatedly expand `(goldenPow gamma 5).fst`, so the named polynomial is not logically necessary.

The dedicated definition is nevertheless useful:

- it hides the large fifth-power expansion from theorem statements;
- modular and divisibility arguments can be carried out as pure integer polynomial arithmetic;
- the unit-sector formulas remain compact;
- arithmetic lemmas are insulated from changes in the implementation of `goldenPow`.

The first- and second-coordinate polynomials form a natural pair, so another design could bundle them into one pair-valued coordinate function. That would improve structural cohesion, but individual divisibility arguments might become less convenient because of added projections.

## Optimization candidates

1. **Keep the current explicit bivariate polynomial**
   - direct, auditable, and well suited to modular arithmetic and `ring`.

2. **Bundle both coordinates in one function**
   - for example, define `goldenFifthCoords : ℤ × ℤ → ℤ × ℤ` and derive the two projections.
   - improves coordinate consistency but adds projection overhead in scalar arithmetic lemmas.

3. **Introduce a general coordinate recurrence for `n`-th powers**
   - derive the fifth-power formulas as the specialization `n=5`.
   - increases generality but may over-abstract a proof dedicated specifically to FLT5.

4. **Represent the formulas through polynomial objects**
   - a `Polynomial` or multivariate-polynomial formulation could expose coefficient and modular-map APIs.
   - it may also increase proof overhead compared with the current integer arithmetic tactics.

For the present development, the explicit fifth-power polynomial is very well matched to downstream five-adic calculations, so there is little local pressure to replace it.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This `def` in isolation needs only integers, powers, and basic ring operations, so importing all of Mathlib is much broader than necessary. The surrounding `GoldenFifthPowerCoordinates.lean` module later uses `ring`, `norm_num`, `Int.ModEq`, primality, and divisibility APIs, so the true minimal import set at module scope is larger than what 0255 alone needs.

No Lean build is run in this museum pass, so the exact minimal import set is unverified. A likely optimization direction is to replace the blanket import with modular imports for integer algebra, ring tactics, modular arithmetic, and divisibility.

## Comparator challenge suitability

Yes. Useful competitors include:

- A: the current explicit `def goldenFifthFstPoly`;
- B: repeatedly expand `(goldenPow gamma 5).fst` directly;
- C: bundle first and second coordinates in one pair-valued function;
- D: derive the formula from a general `n`-th power coordinate recurrence;
- E: use polynomial or multivariate-polynomial objects.

Useful comparison axes are:

- theorem statement size downstream;
- `ring` / `simp` proof cost;
- ease of proving modulo-five results;
- robustness under coordinate implementation changes;
- balance between generality and FLT5 specialization;
- elaboration and generated proof-term cost.

The A-versus-C comparison is especially useful for measuring local scalar API readability against structural consistency of the two coordinates.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The module comment states that this layer names the two coordinate polynomials of `gamma=p+q*φ` raised to the fifth power and then uses the representatives `1,φ,...,φ^4` to produce five explicit arithmetic unit sectors.

The target branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact page or section corresponding to this small `def` was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0256 `goldenFifthSndPoly`**:

```lean
/-- Second-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthSndPoly (p q : ℤ) : ℤ :=
  5 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 +
    3 * p * q ^ 3 + q ^ 4)
```

Declaration 0255 fixes the first coordinate of the fifth power; 0256 fixes the second coordinate. The second coordinate visibly contains the factor

$$
5q,
$$

and this built-in divisibility by five becomes important in the later exclusion of nonzero unit sectors.

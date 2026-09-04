# 0242 — `goldenNorm_sub_conj`

## Lean type

```lean
/-- The norm of the conjugate difference is `-5` times the square coordinate. -/
theorem goldenNorm_sub_conj (x : GoldenInt) :
    goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2 := by
  rw [golden_sub_conj_eq_snd_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_sqrtFive]
  simp [goldenNorm, goldenOfInt]
  ring
```

This is a `theorem` stating that the norm of the difference between a golden integer `x` and its conjugate is exactly `-5` times the square of the second coordinate `x.snd`.

## Mathematical statement

Write `x = a + bφ`. Declaration 0241 already proves

$$
x-\overline{x}=b\sqrt5.
$$

The golden norm is multiplicative, and

$$
N(\sqrt5)=-5.
$$

Therefore

$$
N(x-\overline{x})
=N(b\sqrt5)
=N(b)N(\sqrt5).
$$

The norm of the embedded integer `b` is `b^2`, hence

$$
N(x-\overline{x})
=b^2(-5)
=-5b^2.
$$

The Lean statement records exactly this identity:

```lean
goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2
```

## Role in the full proof

Declaration 0241 factors the conjugate difference as

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5.
$$

The present theorem converts that factorization into an **explicit integer norm-mass formula**.

For a `SignedGoldenRamifierStrippedPacket`, the element `beta` carries the coordinate certificate

$$
\beta_{\mathrm{snd}}=-5^7a^{10}.
$$

Specializing the present theorem to `x = beta` therefore gives, in the next declaration 0243,

$$
N(\beta-\overline\beta)
=-5\,(-5^7a^{10})^2
=-5^{15}a^{20}.
$$

On the other hand, the stripped packet also stores

$$
N(\beta)=b^5.
$$

A common divisor `d` of `beta` and `conj beta` also divides their difference by 0191 `goldenDivides_sub`. Applying 0192 `goldenNorm_dvd_of_goldenDivides` then forces `N(d)` to divide both

$$
b^5
$$

and

$$
5^{15}a^{20}.
$$

The coprimality information from the power-split layer together with `5 ∤ b` then forces the absolute norm of the common divisor to be `1`; the unit criterion from 0201/0202 turns this into `GoldenUnit d`.

Thus 0242 is a central bridge from an internal golden-order conjugate difference to an explicit integer quantity that can be used by the downstream divisibility and coprimality argument.

## Direct dependencies

The proof directly uses three named theorems:

- 0241 `golden_sub_conj_eq_snd_mul_sqrtFive`
- 0174 `goldenNorm_mul`
- 0182 `goldenNorm_sqrtFive`

It also unfolds the definitions:

- 0164 `goldenNorm`
- 0162 `goldenOfInt`

The statement itself additionally depends on:

- `GoldenInt`
- 0163 `goldenConj`

Conceptually, the theorem is the composition of

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5
$$

with

$$
N(xy)=N(x)N(y),\qquad N(\sqrt5)=-5.
$$

## Proof flow

The proof has three stages.

### 1. Factor the conjugate difference

```lean
rw [golden_sub_conj_eq_snd_mul_sqrtFive]
```

The left-hand side becomes

```lean
goldenNorm (goldenMul (goldenOfInt x.snd) sqrtFiveElement)
```

### 2. Apply norm multiplicativity and the norm of square root five

```lean
rw [goldenNorm_mul, goldenNorm_sqrtFive]
```

This reduces the expression to

$$
N(goldenOfInt(x.snd))\cdot(-5).
$$

### 3. Expand the norm of the embedded integer

```lean
simp [goldenNorm, goldenOfInt]
ring
```

Since `goldenOfInt x.snd = ⟨x.snd,0⟩`, its norm reduces to `x.snd ^ 2`. The final `ring` normalizes multiplication order and signs to obtain

$$
-5*x.snd^2.
$$

## Lean-specific processing

The first rewrite reuses 0241 as a theorem-level factorization API, so the conjugation and square-root-of-five coordinates are not re-expanded here. This is exactly where extracting 0241 as a named theorem pays off.

`goldenNorm_mul` is stated for the raw multiplication operation `goldenMul`, so the raw form on the right-hand side of 0241 also keeps the proof short.

`goldenNorm_sqrtFive` applies through the transparent alias layer because `sqrtFiveElement` is an `abbrev` for `goldenSqrtFive`.

The final

```lean
simp [goldenNorm, goldenOfInt]
```

recomputes the norm of an embedded integer definitionally rather than using the already available theorem `goldenNorm_ofInt`. This is a small API-level duplication discussed below.

## Redundancy and duplication

The clearest duplication is that 0169 `goldenNorm_ofInt` already proves

```lean
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

Therefore the present explicit unfolding of

```lean
simp [goldenNorm, goldenOfInt]
```

could potentially be replaced by the existing higher-level API.

Declarations 0241 and 0242 are also normally consumed together: 0241 gives the factorization, while 0242 turns it into a norm identity. They could be collapsed into a single coordinate proof, but the current split is useful for auditing because it separates

1. factorization inside the golden order, and
2. the resulting integer norm mass.

## Optimization candidates

1. **Reuse `goldenNorm_ofInt`**

   Rewrite `goldenNorm (goldenOfInt x.snd)` through the existing theorem instead of unfolding the coordinate norm again.

2. **Investigate a shorter `simpa` proof**

   Combining 0241, `goldenNorm_mul`, `goldenNorm_sqrtFive`, and `goldenNorm_ofInt` may remove the explicit `simp + ring` tail. This is unverified here because no Lean build is performed.

3. **Bundle conjugation as a `RingEquiv`**

   A structured conjugation API could make identities involving `x * conj x` and anti-invariant components more generic.

4. **Generalize to a quadratic-order theorem**

   In a quadratic order of discriminant `5`, the norm of the conjugate difference is controlled by the discriminant times the square of the anti-invariant coordinate. The present theorem is a concrete instance of that pattern.

5. **Organize 0241–0243 as one conjugate-difference mass API**

   0241 is the generic factorization, 0242 the generic norm formula, and 0243 the stripped-packet specialization. Consistent naming or a dedicated namespace could improve discoverability.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is relatively small:

- equality rewriting through `rw`
- simplification through `simp`
- integer polynomial normalization through `ring`

Most mathematical dependencies come from project-local golden-order declarations.

The theorem in isolation likely needs much less than all of `Mathlib`, but the full `SignedGoldenConjugateCoprime.lean` module also uses integer divisibility, `natAbs`, coprimality, and unit arguments. Import minimization therefore has to be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementations to compare include:

- A: current rewrite chain + `simp` + `ring`
- B: a higher-level proof reusing `goldenNorm_ofInt`
- C: a direct coordinate proof that does not use 0241
- D: an abstract proof after bundling conjugation as a `RingEquiv`
- E: specialization of a general quadratic-order / discriminant theorem

Useful metrics include proof length, direct dependencies, amount of definitional unfolding, visibility of mathematical provenance, dependence on the raw coordinate API, and generalizability.

A demonstrates the connectivity of the current API; B increases theorem reuse; C minimizes theorem dependency depth; D/E test a more abstract architecture.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0241 and immediately before the packet specialization

```lean
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

The exact page or section corresponding to this theorem in the existing Japanese and English PDFs was not directly identified in this pass, so no PDF page number is inferred.

## Next declaration to read

The next declaration in dependency order is **0243 `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`**:

```lean
/-- The packet coordinate makes the conjugate-difference norm explicit. -/
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

Declaration 0242 proves for arbitrary `x` that

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2.
$$

Declaration 0243 substitutes the stripped-packet coordinate

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

to obtain the exact integer mass

$$
N(\beta-\overline\beta)=-5^{15}a^{20}.
$$

This becomes the next direct input constraining the norm of any common divisor of `beta` and its conjugate.

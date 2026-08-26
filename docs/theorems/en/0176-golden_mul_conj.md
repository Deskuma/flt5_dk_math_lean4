# 0176 — `golden_mul_conj`

## Lean type

```lean
/-- Multiplication by the conjugate embeds the norm. -/
theorem golden_mul_conj (x : GoldenInt) :
    goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x) := by
  ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

This is a `theorem` stating that the product of a golden integer `x` with its conjugate `goldenConj x` is exactly the integer-valued norm `goldenNorm x`, embedded back into the golden order by `goldenOfInt`.

## Mathematical statement and meaning of the declaration

Write an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

By 0163 `goldenConj`,

$$
\overline{x}=(a+b)-b\varphi,
$$

and by 0164 `goldenNorm`,

$$
N(x)=a^2+ab-b^2.
$$

The theorem is the internal golden-order form of

$$
x\overline{x}=N(x).
$$

The integer `N(x)` on the right is embedded by `goldenOfInt` as

$$
N(x)\longmapsto N(x)+0\varphi.
$$

A direct coordinate calculation gives first coordinate

$$
a(a+b)+b(-b)=a^2+ab-b^2=N(x),
$$

and second coordinate

$$
a(-b)+b(a+b)+b(-b)=0.
$$

Hence the product is exactly `⟨goldenNorm x, 0⟩`, which is `goldenOfInt (goldenNorm x)`.

## Role in the overall proof

0174 `goldenNorm_mul` established

$$
N(xy)=N(x)N(y),
$$

while 0175 `goldenNorm_conj` established

$$
N(\overline{x})=N(x).
$$

The present theorem connects those norm laws to the actual ring product by identifying the norm with the product of an element and its conjugate.

This is a key bridge in golden-integer arithmetic. It turns the norm from a standalone quadratic form into an internal factorization identity

$$
x\overline{x}=N(x),
$$

which can then feed directly into arguments about conjugate factors, units, divisibility, and ramification.

The same `GoldenOrder` source later uses the theorem directly in

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

so 0176 is a concrete public API used in the norm-five ramifier arithmetic around `tau`.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0124 `goldenMul`
- 0162 `goldenOfInt`
- 0163 `goldenConj`
- 0164 `goldenNorm`
- `GoldenInt.ext`
- `simp`
- `ring`

0174 `goldenNorm_mul` and 0175 `goldenNorm_conj` are mathematically close, but this proof does not invoke either theorem. It closes independently by fully expanding the coordinate definitions and proving the resulting polynomial identities.

## Proof / construction flow

The entire proof is written as one tactic chain:

```lean
ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

Its structure is:

1. `ext` reduces equality of `GoldenInt` structures to equality of the `fst` and `snd` coordinates.
2. `simp` unfolds `goldenMul`, `goldenConj`, `goldenOfInt`, and `goldenNorm`, while simplifying projections and signs.
3. The first coordinate reduces to the norm polynomial, and the second coordinate reduces to zero.
4. `ring` normalizes both integer polynomial identities and closes them.

Thus the Lean proof mirrors the mathematics directly: the conjugate product loses its `φ` component, leaving only the integer norm.

## Lean-specific processing

The use of `ext` relies on the upstream `GoldenInt.ext` theorem, so structure equality can be handled coordinatewise instead of by explicit constructor reasoning.

Because `goldenMul`, `goldenConj`, and `goldenNorm` are all explicit coordinate definitions, the theorem needs no bundled `RingHom`, `RingEquiv`, or abstract quadratic-norm machinery. Once unfolded, it is ordinary commutative-ring polynomial algebra handled by `simp` and `ring`.

The statement deliberately uses the raw operation `goldenMul` on the left and the raw integer embedding `goldenOfInt` on the right. By 0159 `golden_mul_eq`, raw multiplication is definitionally connected to standard `x * y` notation, but the present theorem remains in the coordinate API layer.

## Redundancy and duplication

The main structural duplication is that `goldenNorm` is defined first as the explicit quadratic polynomial

$$
a^2+ab-b^2,
$$

and only afterward connected by this theorem to

$$
x\overline{x}=N(x).
$$

An alternative design could define norm from the element-times-conjugate construction, making 0176 closer to a definition or generic lemma. The current design, however, has the advantage that the integer-valued norm is immediately available for direct computation, multiplicativity proofs, and later Euclidean estimates.

Conjugation laws are also distributed across separate theorems such as `goldenConj_invol`, `goldenConj_mul`, and `goldenNorm_conj`. Bundling `goldenConj` as a `RingEquiv` could reduce this API-level fragmentation.

## Optimization candidates

1. Keep the present `ext <;> simp [...] <;> ring` proof for maximum coordinate transparency.
2. Make a standard-notation theorem

```lean
x * goldenConj x = goldenOfInt (goldenNorm x)
```

the primary public API, with the raw `goldenMul` form as a bridge.
3. Add a theorem identifying `goldenOfInt a` with the standard integer cast `(a : GoldenInt)`, allowing the right-hand side to use standard algebra notation.
4. Bundle `goldenConj` as `RingEquiv GoldenInt GoldenInt`.
5. Bundle `goldenNorm` as a multiplicative map and organize element-times-conjugate as part of a generic quadratic-order interface.
6. Compare the explicit implementation with `AdjoinRoot (X^2-X-1)` or quadratic-algebra conjugation and norm infrastructure.

The local proof is already short; the main optimization target is API organization and abstraction rather than proof length.

## Required Mathlib imports and import optimization

This theorem directly needs the upstream `GoldenInt` definitions, structure extensionality, integer simplification, and the `ring` tactic.

The standalone artifact uses `import Mathlib`, which is likely broader than necessary for this theorem alone. The complete `GoldenOrder` module also uses `Zsqrtd`, `omega`, `norm_num`, `interval_cases`, and substantial algebraic typeclass infrastructure, so the true minimal import set should be validated at module level. No Lean build is performed in this museum pass, so no exact minimal import list is claimed.

## Comparator challenge suitability

Yes.

Useful implementations to compare are:

- explicit coordinate proof (`ext` + `simp` + `ring`);
- a structural proof using bundled `RingEquiv` conjugation;
- a design defining norm through element-times-conjugate;
- reuse of a generic `AdjoinRoot` / quadratic-algebra norm theorem.

Comparison criteria include proof size, definitional transparency, duplication among conjugation laws, compatibility with standard notation, and downstream ergonomics for unit, divisibility, ramification, and Euclidean-domain proofs.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this theorem appears immediately after 0175 `goldenNorm_conj` and is followed by `goldenSqrtFive`.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- The ramified square root `2*phi - 1` of five. -/
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

By 0176, the basic relationships among `φ`, conjugation, norm, and the conjugate product are all available. The development now introduces the explicit ramified element corresponding to

$$
2\varphi-1=\sqrt5,
$$

then proceeds toward its square being `5`, its norm being `-5`, and its relationship with `tau=2+φ`.
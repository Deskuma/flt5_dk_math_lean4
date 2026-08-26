# 0199 — `goldenUnit_of_norm_eq_one`

## Lean type

```lean
theorem goldenUnit_of_norm_eq_one {x : GoldenInt} (h : goldenNorm x = 1) :
    GoldenUnit x := by
  refine ⟨goldenConj x, ?_, ?_⟩
  · simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
  · have hc : goldenMul (goldenConj x) x =
        goldenMul x (goldenConj x) := by
      change goldenConj x * x = x * goldenConj x
      exact mul_comm _ _
    rw [hc]
    simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

This theorem states that if a golden integer `x` has norm `1`, then `x` satisfies the domain-specific predicate `GoldenUnit`, hence is a unit of the golden order.

## Mathematical statement

The hypothesis is

$$
N(x)=1.
$$

Declaration 0176 `golden_mul_conj` proves for every golden integer that

$$
x\overline{x}=N(x).
$$

Therefore the norm-one hypothesis gives

$$
x\overline{x}=1.
$$

Because `GoldenInt` is a commutative ring,

$$
\overline{x}x=x\overline{x}=1
$$

as well. Thus `goldenConj x` is a two-sided inverse of `x`, exactly matching the definition of `GoldenUnit` from 0198.

## Role in the full proof

Immediately after 0198 defines unitness as the existence of a two-sided inverse, this theorem provides the first bridge from norm information to an explicit inverse witness.

The source then treats the `N(x)=-1` case in `goldenUnit_of_norm_eq_neg_one`, combines the two directions in `goldenUnit_of_norm_eq_one_or_neg_one`, and later proves the converse `goldenNorm_eq_one_or_neg_one_of_unit`. Together these establish the standard criterion

$$
GoldenUnit(x)
\iff
N(x)=1\ \text{or}\ N(x)=-1.
$$

That criterion supports the later lemmas `goldenUnit_phi`, `goldenUnit_mul`, `goldenUnit_pow`, and ultimately `GoldenRelPrime`, where every common divisor is required to be a unit.

## Direct dependencies

The direct dependencies are:

- 0198 `GoldenUnit`
- 0163 `goldenConj`
- 0176 `golden_mul_conj`
- 0162 `goldenOfInt`
- `goldenOne`
- commutativity from `CommRing GoldenInt`, via `mul_comm`

Conceptually,

$$
N(x)=1
+\bigl(x\overline{x}=N(x)\bigr)
+\text{commutativity}
\Longrightarrow
x^{-1}=\overline{x}.
$$

## Proof flow

The proof first chooses the conjugate as the inverse witness:

```lean
refine ⟨goldenConj x, ?_, ?_⟩
```

This expands the `GoldenUnit` goal into the two inverse equations.

The first direction is closed by

```lean
simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

which specializes `x * conj x = goldenOfInt (goldenNorm x)` and rewrites the norm to `1`.

For the reverse product order, the proof first establishes

```lean
have hc : goldenMul (goldenConj x) x =
    goldenMul x (goldenConj x) := by
  change goldenConj x * x = x * goldenConj x
  exact mul_comm _ _
```

then rewrites by `hc` and reuses the same `golden_mul_conj` argument.

## Lean-specific processing

`refine ⟨..., ?_, ?_⟩` constructs both the existential witness and the conjunction required by `GoldenUnit` in one step.

The `simpa ... using` pattern takes an already-proved theorem and normalizes its conclusion to the current goal using the norm hypothesis together with the raw definitions `goldenOfInt` and `goldenOne`.

The `change` step in the second branch crosses the raw/standard API boundary: it re-expresses `goldenMul` as the standard multiplication notation `*`, allowing the generic theorem `mul_comm` to be applied directly.

## Redundancy and duplication

Since `GoldenInt` is commutative, requiring both left and right inverse equations in the definition of `GoldenUnit` is mathematically redundant. The proof reflects this: the second inverse equation is obtained from the first form solely by commutativity.

There is also literal proof duplication in the two occurrences of

```lean
simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

A local lemma for `goldenMul x (goldenConj x) = goldenOne` could remove that repetition.

More globally, a design centered on Mathlib's standard `IsUnit` could potentially replace some explicit inverse bookkeeping with generic unit APIs.

## Optimization candidates

1. **Factor the right-inverse equation into a local lemma**
   - prove `goldenMul x (goldenConj x) = goldenOne` once and reuse it after commutativity.

2. **Move `GoldenUnit` closer to Mathlib `IsUnit`**
   - this may reduce custom witness-level code and improve access to generic algebraic lemmas.

3. **Bundle conjugation as a `RingEquiv`**
   - the necessary add/mul/involution properties have largely already been proved, and unit arguments could then become more structural.

4. **Bundle the norm as a multiplicative map**
   - this may allow the unit criterion to be phrased through more generic multiplicative-map infrastructure.

The current proof is nevertheless attractive for auditability because it explicitly displays the mathematical inverse `conj x`.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem directly needs only the core equality/existential machinery, `simpa`, `change`, `rw`, and commutative-ring multiplication through `mul_comm`.

No advanced analysis or number-theory library is used by this theorem itself. The surrounding module, however, already depends on arithmetic tactics, integer divisibility, and norm calculations, so the true minimal import set for the full module is broader. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. Useful variants include:

- A: the current explicit witness with two inverse branches
- B: factor out the right-inverse equation and reuse it
- C: center the proof on Mathlib `IsUnit`
- D: derive the result structurally from a bundled conjugation `RingEquiv`
- E: prove the inverse equations by direct coordinate expansion

Comparison axes include proof size, number of raw/standard API crossings, mathematical provenance, reuse of generic Mathlib APIs, refactor robustness, and auditability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In the verified source order, 0198 `GoldenUnit` is immediately followed by this theorem, and `goldenUnit_of_norm_eq_neg_one` follows immediately afterward.

The branch contains Japanese and English PDFs, but the exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0200 `goldenUnit_of_norm_eq_neg_one`**:

```lean
theorem goldenUnit_of_norm_eq_neg_one {x : GoldenInt} (h : goldenNorm x = -1) :
    GoldenUnit x := by
  refine ⟨-goldenConj x, ?_, ?_⟩
  ...
```

For norm `1`, 0199 uses the conjugate itself as the inverse. For norm `-1`, 0200 compensates for the sign by choosing `-goldenConj x`. This completes the two basic branches needed for the norm-`±1` unit criterion.
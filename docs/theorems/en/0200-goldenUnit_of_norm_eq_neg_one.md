# 0200 — `goldenUnit_of_norm_eq_neg_one`

## Lean type

```lean
theorem goldenUnit_of_norm_eq_neg_one {x : GoldenInt} (h : goldenNorm x = -1) :
    GoldenUnit x := by
  refine ⟨-goldenConj x, ?_, ?_⟩
  · have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl
  · have hc : goldenMul (-goldenConj x) x =
        goldenMul x (-goldenConj x) := by
      change (-goldenConj x) * x = x * (-goldenConj x)
      exact mul_comm _ _
    rw [hc]
    have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl
```

This is a `theorem` stating that if a golden integer `x` has norm `-1`, then `x` satisfies `GoldenUnit`, hence is a unit of the golden order.

## Mathematical statement

The hypothesis is

$$
N(x)=-1.
$$

By 0176 `golden_mul_conj`,

$$
x\overline{x}=N(x),
$$

so

$$
x\overline{x}=-1.
$$

Therefore the conjugate itself is not quite the inverse; its negation is. Taking

$$
-\overline{x}
$$

as the inverse candidate gives

$$
x(-\overline{x})=-(x\overline{x})=-(-1)=1.
$$

Because `GoldenInt` is commutative, the reverse product is also `1`. Thus `-goldenConj x` is a two-sided inverse of `x`.

## Role in the full proof

Declaration 0199 `goldenUnit_of_norm_eq_one` treats the branch $N(x)=1$. The present theorem fills the complementary branch $N(x)=-1$.

The immediately following theorem `goldenUnit_of_norm_eq_one_or_neg_one` combines the two results into

$$
N(x)=1\ \text{or}\ N(x)=-1
\Longrightarrow
GoldenUnit(x).
$$

The later converse `goldenNorm_eq_one_or_neg_one_of_unit` proves the reverse implication, completing the golden-order unit criterion

$$
GoldenUnit(x)
\iff
N(x)=\pm1.
$$

This criterion is then used by `goldenUnit_phi`, `goldenUnit_neg`, `goldenUnit_mul`, `goldenUnit_pow`, and eventually `GoldenRelPrime`.

## Direct dependencies

The direct dependencies are:

- 0198 `GoldenUnit`
- 0163 `goldenConj`
- 0176 `golden_mul_conj`
- `goldenNorm`
- `mul_neg` and `mul_comm` supplied by the commutative-ring structure on `GoldenInt`

Conceptually,

$$
N(x)=-1
+\bigl(x\overline{x}=N(x)\bigr)
+\text{sign correction}
+\text{commutativity}
\Longrightarrow
x^{-1}=-\overline{x}.
$$

## Proof flow

The proof first chooses the negative conjugate as the inverse witness:

```lean
refine ⟨-goldenConj x, ?_, ?_⟩
```

For the first inverse equation it establishes

```lean
have hm : goldenMul x (-goldenConj x) =
    -(goldenMul x (goldenConj x)) := by
  change x * (-goldenConj x) = -(x * goldenConj x)
  exact mul_neg _ _
```

This converts raw `goldenMul` notation into standard ring multiplication so that `mul_neg` can move the minus sign outside the product.

Then

```lean
rw [hm, golden_mul_conj, h]
rfl
```

reduces the goal to the sign computation

$$
-(x\overline{x})=-N(x)=1.
$$

For the reverse product, the proof first uses commutativity:

```lean
have hc : goldenMul (-goldenConj x) x =
    goldenMul x (-goldenConj x) := by
  change (-goldenConj x) * x = x * (-goldenConj x)
  exact mul_comm _ _
```

It rewrites by `hc`, reconstructs the same `hm`, and repeats the norm rewrite.

## Lean-specific processing

The two `change` steps expose standard `*` notation underneath the raw operation `goldenMul`.

- one allows the generic theorem `mul_neg` to be used;
- the other allows the generic theorem `mul_comm` to reorder the factors.

The sequence `rw [hm, golden_mul_conj, h]` turns the explicit inverse equation into a closed sign equality, which then closes by `rfl`.

Compared with 0199, which can rely mainly on `simpa`, the norm-`-1` branch requires an explicit sign correction, so the proof introduces the local equality `hm` to pull negation outside the product.

## Redundancy and duplication

The most obvious duplication is that the local lemma `hm` is written twice, once in each inverse branch:

```lean
have hm : goldenMul x (-goldenConj x) =
    -(goldenMul x (goldenConj x)) := by
  change x * (-goldenConj x) = -(x * goldenConj x)
  exact mul_neg _ _
```

It could be proved once and reused.

Also, because the ring is commutative, the second inverse equation is mechanically derivable from the first by `mul_comm`. This mirrors the redundancy already visible in the definition of `GoldenUnit`, which explicitly requires both inverse directions.

A design based on Mathlib's standard `IsUnit` could move some of this bookkeeping into generic algebra infrastructure.

## Optimization candidates

1. **Build `hm` once**
   - the smallest and safest local simplification.

2. **Prove one inverse equation first**
   - create a local theorem `goldenMul x (-goldenConj x) = goldenOne`, then obtain the reverse equation only by commutativity.

3. **Unify 0199 and 0200**
   - a helper parameterized by the norm sign could reduce structural duplication between the norm `1` and norm `-1` branches.

4. **Move `GoldenUnit` toward Mathlib `IsUnit`**
   - this may reduce explicit witness and two-sided inverse code.

5. **Bundle conjugation as a `RingEquiv`**
   - the development already contains add, mul, power, and involution properties, so the unit criterion could potentially be phrased more structurally.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself directly needs only basic existential/conjunction construction, `change`, `rw`, and the commutative-ring lemmas `mul_neg` and `mul_comm`.

No advanced analysis or number-theory API is used directly here. The surrounding `GoldenDivisibility` module does use integer divisibility, norm calculations, and arithmetic tactics, so the true minimal import set for the complete module is broader.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current explicit witness with duplicated `hm`
- B: factor `hm` into one local lemma
- C: prove one inverse equation and derive the other by commutativity
- D: unify the norm `1` and norm `-1` branches through a shared helper
- E: center the implementation on Mathlib `IsUnit`
- F: prove the inverse equations by direct coordinate expansion

Comparison axes include proof size, number of raw/standard API crossings, duplication, mathematical provenance, generic Mathlib reuse, refactor robustness, and auditability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In this run, the complete source of 0200 was verified directly in the repository, and the immediately following declaration was confirmed to be `goldenUnit_of_norm_eq_one_or_neg_one`.

The target branch also contains Japanese and English PDFs. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0201 `goldenUnit_of_norm_eq_one_or_neg_one`**:

```lean
theorem goldenUnit_of_norm_eq_one_or_neg_one {x : GoldenInt}
    (h : goldenNorm x = 1 ∨ goldenNorm x = -1) : GoldenUnit x :=
  h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

Declarations 0199 and 0200 establish the norm `1` and norm `-1` branches separately. Declaration 0201 combines them with `Or.elim`, completing the direction from norm `±1` to unitness.
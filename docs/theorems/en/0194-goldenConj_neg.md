# 0194 — `goldenConj_neg`

## Lean type

```lean
theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

This is a `theorem` stating that golden conjugation preserves additive inverses.

## Mathematical statement

Write a golden integer as

$$
x=a+b\varphi.
$$

Declaration 0163 defines conjugation in coordinates by

$$
(a,b)\longmapsto(a+b,-b).
$$

Since

$$
-x=(-a)+(-b)\varphi,
$$

conjugating the negative gives

$$
\overline{-x}=(-a-b)-(-b)\varphi=(-a-b)+b\varphi.
$$

On the other hand,

$$
-\overline{x}=-(a+b-b\varphi)=(-a-b)+b\varphi.
$$

Therefore

$$
\overline{-x}=-\overline{x}.
$$

Following 0193 `goldenConj_add`, this theorem makes explicit that conjugation is compatible with the additive-group structure of `GoldenInt`.

## Role in the full proof

The conjugation API has been assembled progressively:

- 0168 `goldenConj_ofInt` — conjugation fixes the embedded integers;
- 0170 `goldenConj_invol` — conjugation is involutive;
- 0171 `goldenConj_mul` — conjugation preserves multiplication;
- 0193 `goldenConj_add` — conjugation preserves addition;
- 0194 `goldenConj_neg` — conjugation preserves negation.

With 0194 available, the following subtraction-compatibility theorem can be handled naturally from addition and negation. This matters later in the relative-primality argument, where expressions such as `beta - goldenConj beta` occur and conjugation must move cleanly through signs and differences.

Together with 0171 and 0193, the present theorem shows that `goldenConj` already has the principal preservation laws expected from a ring homomorphism. Combining those laws with the involution from 0170 suggests a future bundled `RingEquiv GoldenInt GoldenInt` design.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`;
- 0163 `goldenConj`;
- 0122 `goldenNeg` and the `Neg GoldenInt` instance;
- 0139 `golden_fst_neg`;
- 0140 `golden_snd_neg`;
- `GoldenInt.ext`;
- standard integer simplification for addition and negation.

The proof explicitly unfolds `goldenConj`, then uses `ext` and `simp` on both coordinates. `add_comm` is explicitly added to the simp set.

## Proof flow

The proof is

```lean
by
  ext <;> simp [goldenConj, add_comm]
```

1. `ext` reduces equality of two `GoldenInt` values to equality of their `fst` and `snd` coordinates.
2. `simp [goldenConj, add_comm]` unfolds the coordinate definition of conjugation, uses the negation projection simp lemmas, and normalizes the resulting integer expressions.
3. Both coordinate goals reduce to reflexive integer equalities.

Unlike 0193 `goldenConj_add`, whose proof ends with `ring`, 0194 needs only simplification because it contains only linear sign manipulations. This difference accurately reflects the lower algebraic complexity of the negation law.

## Lean-specific processing

`ext` uses the previously registered `@[ext] theorem GoldenInt.ext`, turning structure equality into two field equalities.

The `<;>` combinator applies the same simplification pipeline to both generated goals.

`simp [goldenConj, add_comm]` unfolds `goldenConj` and uses existing `@[simp]` projection lemmas so that `(-x).fst` and `(-x).snd` reduce to `-x.fst` and `-x.snd`. In the first coordinate, summands may appear in a different order on the two sides, so `add_comm` is supplied explicitly to align the normal forms.

The proof does not reuse `goldenConj_add` directly. It therefore follows the explicit-coordinate audit style of the development rather than deriving negation preservation abstractly from additive-homomorphism theory.

## Redundancy and duplication

Once 0193 `goldenConj_add` has established additivity, negation preservation is mathematically a generic consequence of additive-group homomorphism theory.

Moreover, 0171 `goldenConj_mul`, 0193 `goldenConj_add`, 0194 `goldenConj_neg`, and the following `goldenConj_sub` distribute morphism-like behavior over several independent theorems.

This increases theorem count, but each property is directly checked against the explicit coordinate implementation. For an auditable FLT5 formalization, that transparency is a legitimate benefit.

## Optimization candidates

1. **Keep the current proof**
   - extremely short and fully transparent at the coordinate level.

2. **Derive negation preservation abstractly from 0193**
   - use additivity together with preservation of zero and additive-group uniqueness;
   - this may be mathematically more structural but can require more Lean infrastructure than the current proof.

3. **Bundle `goldenConj` as an `AddMonoidHom` or `RingHom`**
   - then `map_neg` can provide the result generically.

4. **Bundle conjugation as a `RingEquiv`**
   - use 0170 `goldenConj_invol` as the inverse law and collect the conjugation API in one structure.

5. **Recheck whether explicit `add_comm` is necessary**
   - a sufficiently canonical simp normal form might make it removable;
   - this is unverified because this museum pass does not run Lean builds.

Locally the current proof is already close to minimal. The main optimization opportunity is therefore not inside this theorem but in bundling the conjugation API as a whole.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface used by this theorem is small:

- structure extensionality;
- `simp`;
- integer addition and negation;
- the `GoldenInt` negation projection API;
- `goldenConj`.

The theorem itself does not require `ring`, divisibility, norm theory, or analysis APIs.

The surrounding `GoldenDivisibility.lean` module also develops divisibility, norms, units, and relative primality, so the module-wide minimal import set will be broader. Since no Lean build is run in this museum pass, the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful contestants include:

- A: current `ext <;> simp [goldenConj, add_comm]`;
- B: explicit `GoldenInt.ext` with separate coordinate proofs;
- C: derivation from 0193 `goldenConj_add` using additive-group theory;
- D: bundle `goldenConj` as a `RingHom` and use `map_neg`;
- E: bundle it as a `RingEquiv` and use the generic automorphism API.

Comparison axes include proof length, visibility of the coordinate implementation, abstraction cost, reuse of generic Mathlib API, downstream theorem size, and robustness under refactoring.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The preceding 0193 canonical document records the source sequence

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0195 `goldenConj_sub`**.

With 0193 establishing additivity and 0194 establishing negation preservation, the next step makes explicit that

$$
\overline{x-y}=\overline{x}-\overline{y}.
$$

This is directly relevant to the later relative-primality argument, where differences between an element and its conjugate are central.

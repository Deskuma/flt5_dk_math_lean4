# 0204 — `goldenUnit_one`

## Lean type

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

This is a `theorem` stating that the multiplicative identity `goldenOne` of the golden order is a `GoldenUnit`.

## Mathematical statement and meaning

`goldenOne` is the identity element of the golden order and corresponds to the coordinate value

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

so the golden norm

$$
N(a+b\varphi)=a^2+ab-b^2
$$

gives

$$
N(1)=1^2+1\cdot0-0^2=1.
$$

Declaration 0199 `goldenUnit_of_norm_eq_one` proves in general that

$$
N(x)=1\Longrightarrow GoldenUnit(x),
$$

so the present theorem is the most basic concrete specialization of that criterion.

Of course, mathematically $1\cdot1=1$, so `GoldenUnit goldenOne` could also be constructed directly by choosing `goldenOne` itself as the inverse witness. The current proof does not reconstruct that witness; instead it deliberately reuses the unit-by-norm API developed immediately upstream.

## Role in the full proof

Declarations 0198–0202 effectively establish

$$
GoldenUnit(x)\iff N(x)=\pm1.
$$

Declaration 0203 applies the norm `-1` branch to the generator $\varphi$. Declaration 0204 is the matching concrete certificate for the norm `1` branch, applied to the identity element itself.

Although tiny, this theorem has a clear downstream role. The later theorem `goldenUnit_pow` uses it as the base case of induction on natural powers. Since

$$
x^0=1,
$$

`goldenUnit_one` supplies unitness in the zero-power case, while the successor step uses `goldenUnit_mul`.

Thus 0204 is not merely a sanity check: it is the base-case API for the subsequent closure of `GoldenUnit` under powers.

## Direct dependencies

The current proof directly depends on:

- 0199 `goldenUnit_of_norm_eq_one`
- 0164 `goldenNorm`
- `goldenOne`
- `norm_num`

Conceptually the dependency is only

$$
N(1)=1
\Longrightarrow
GoldenUnit(1).
$$

The custom predicate itself was defined in 0198 as

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

so a direct proof could simply choose `goldenOne` as the witness.

## Proof flow

The proof has two stages.

```lean
apply goldenUnit_of_norm_eq_one
```

turns the goal

```lean
GoldenUnit goldenOne
```

into the subgoal

```lean
goldenNorm goldenOne = 1.
```

Then

```lean
norm_num [goldenNorm, goldenOne]
```

unfolds `goldenOne = ⟨1,0⟩` and the norm definition, reducing the goal to the closed integer computation

$$
1^2+1\cdot0-0^2=1.
$$

## Lean-specific processing

`apply goldenUnit_of_norm_eq_one` matches the conclusion of the upstream theorem with the current goal, specializes its implicit argument `x` to `goldenOne`, and leaves the hypothesis `goldenNorm goldenOne = 1` as the new goal.

`norm_num [goldenNorm, goldenOne]` unfolds both definitions and normalizes structure projections, integer powers, multiplication, addition, and subtraction. Because the goal is a completely closed arithmetic expression, neither `ring` nor `omega` is needed.

The proof style is exactly parallel to 0203 `goldenUnit_phi`: the general unit theorem is reused, while the concrete norm value is recomputed directly from coordinates.

## Redundancy and duplication

Mathematically, the statement that `1` is a unit is generic to every monoid, so a golden-order-specific theorem is highly redundant at the abstract algebra level. If `GoldenUnit` were connected to Mathlib's standard `IsUnit`, the result could likely be inherited from generic unit infrastructure.

Within the current raw API, one can also prove the theorem directly by constructing the witness `goldenOne` itself rather than passing through the norm criterion.

There is another possible micro-duplication: the closed fact `goldenNorm goldenOne = 1` is recomputed by `norm_num`. If that value is needed repeatedly, a dedicated `[simp]` theorem such as `goldenNorm_one` could centralize the computation. Whether that extra API is worthwhile depends on downstream usage frequency.

## Optimization candidates

1. **Construct the inverse witness directly**
   - use `goldenOne` itself to prove `GoldenUnit goldenOne`;
   - this removes dependency on the unit-by-norm block.

2. **Publish `goldenNorm_one`**
   - make the closed norm computation reusable.

3. **Bridge `GoldenUnit` to Mathlib `IsUnit`**
   - then generic theorems about the unit element can be reused.

4. **Publish the unit criterion as an iff theorem**
   - `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` would make concrete unit proofs more amenable to rewriting or `simp`.

5. **Treat 0203 and 0204 as one concrete-unit API block**
   - they are the two basic examples corresponding to the norm `-1` and norm `1` branches.

The current proof is already short; the main optimization question is API integration rather than line-count reduction.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is mainly `norm_num` and ordinary tactic machinery.

Its golden-order dependencies are upstream declarations in the same generated development. The surrounding `GoldenDivisibility.lean` module also uses integer divisibility, conjugation, norm arithmetic, and ring tactics, so module-level imports are broader than what 0204 needs in isolation.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants are:

- A: current `apply goldenUnit_of_norm_eq_one` + `norm_num`
- B: direct `GoldenUnit` witness using `goldenOne`
- C: reuse a dedicated `goldenNorm_one` theorem
- D: use a bridge to Mathlib `IsUnit`
- E: discharge the theorem via a bidirectional unit-by-norm criterion and `simp`

Useful comparison axes include proof size, direct dependency depth, how well the proof expresses the mathematical triviality of the unit element, reuse of Mathlib's standard unit API, robustness under refactoring, and downstream readability.

The contrast between A and B is especially clear: should the proof exercise the newly built norm criterion, or use the definitional triviality of the identity directly?

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The current Japanese and English 0203 documents record this theorem as the next declaration in source order:

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0205 `goldenUnit_neg`**:

```lean
theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

After the concrete unit examples 0203–0204, declaration 0205 begins the closure properties of `GoldenUnit`. It proves that if `x` is a unit then `-x` is also a unit, using invariance of the norm under sign together with the unit criterion.
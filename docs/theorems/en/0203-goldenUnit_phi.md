# 0203 — `goldenUnit_phi`

## Lean type

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

This is a `theorem` stating that `goldenPhi`, the generator of the golden order, is a `GoldenUnit`.

## Mathematical statement

`goldenPhi` is defined by

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

and represents the basis element $\varphi$ satisfying $\varphi^2=\varphi+1$.

Declaration 0167 `goldenNorm_phi` already establishes

$$
N(\varphi)=-1.
$$

The unit-by-norm results from 0199–0202 show that a golden integer whose norm is `1` or `-1` is a unit. Therefore the mathematical content of 0203 is the concrete specialization

$$
N(\varphi)=-1\Longrightarrow \varphi\in\mathbb Z[\varphi]^\times.
$$

One can also see an explicit inverse directly from $\varphi^2=\varphi+1$:

$$
\varphi(\varphi-1)=1.
$$

Thus the inverse of $\varphi$ is $\varphi-1$. The Lean proof does not reconstruct that witness directly; it passes through the norm criterion instead.

## Role in the full proof

Declarations 0198–0202 effectively complete the general criterion

$$
GoldenUnit(x)\iff N(x)=\pm1.
$$

Declaration 0203 is the first application of that criterion to a distinguished concrete golden integer.

The fact that `goldenPhi` is a unit also matters for the ramification picture. Declaration 0183 proves

$$
\tau=\varphi\sqrt5,
$$

so `tau` and `goldenSqrtFive` differ only by multiplication by the unit $\varphi$. In ring-theoretic language they point in the same ramified prime direction up to association. Naming `goldenUnit_phi` therefore provides a reusable certificate for later associate and unit-class arguments.

Furthermore, once `goldenUnit_pow` is available, every power $\varphi^n$ is a unit. This becomes part of the infrastructure for later unit classification and sector arithmetic.

## Direct dependencies

The direct proof dependencies are:

- 0200 `goldenUnit_of_norm_eq_neg_one`
- 0164 `goldenNorm`
- 0161 `goldenPhi`
- `norm_num`

Mathematically, 0167 `goldenNorm_phi` already exposes the exact fact `goldenNorm goldenPhi = -1`. The current proof does not reuse that theorem directly; instead it recomputes the same coordinate norm by

```lean
norm_num [goldenNorm, goldenPhi]
```

Conceptually the dependency is simply

$$
N(\varphi)=-1
\Longrightarrow
GoldenUnit(\varphi).
$$

## Proof flow

The proof has only two stages.

```lean
apply goldenUnit_of_norm_eq_neg_one
```

changes the goal `GoldenUnit goldenPhi` into the subgoal

```lean
goldenNorm goldenPhi = -1.
```

Then

```lean
norm_num [goldenNorm, goldenPhi]
```

unfolds `goldenPhi = ⟨0,1⟩` and the norm formula, reducing the goal to the closed integer computation

$$
0^2+0\cdot1-1^2=-1.
$$

## Lean-specific processing

`apply goldenUnit_of_norm_eq_neg_one` matches the conclusion of the upstream theorem with the current goal, specializes its implicit argument `x` to `goldenPhi`, and leaves its hypothesis `goldenNorm goldenPhi = -1` as the new goal.

`norm_num [goldenNorm, goldenPhi]` unfolds both definitions, simplifies the structure projections, and normalizes the resulting integer expression. No `ring` or `omega` call is necessary because the arithmetic is completely closed.

The notable design choice is that the proof reuses the general unit theorem from 0200 while recomputing the concrete norm value from coordinates.

## Redundancy and duplication

The clearest duplication is with 0167 `goldenNorm_phi`, which already proves

```lean
@[simp] theorem goldenNorm_phi : goldenNorm goldenPhi = -1 := by
  norm_num [goldenNorm, goldenPhi]
```

Thus 0203 repeats the same `norm_num` calculation.

The proof could likely be shortened to something conceptually like

```lean
exact goldenUnit_of_norm_eq_neg_one goldenNorm_phi
```

or

```lean
apply goldenUnit_of_norm_eq_neg_one
simpa using goldenNorm_phi
```

The exact elaboration of the shortest form is not checked here because this museum pass does not run a Lean build.

There is also an API-level overlap between the custom predicate `GoldenUnit` and Mathlib's standard `IsUnit`. A future bridge could move this theorem into more generic unit infrastructure.

## Optimization candidates

1. **Reuse 0167 `goldenNorm_phi`**
   - removes the duplicated closed-coordinate computation.

2. **Publish the unit criterion as an iff theorem**
   - a theorem `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` would make concrete unit proofs easy to discharge with rewriting or `simp`.

3. **Connect `GoldenUnit` to `IsUnit`**
   - enables Mathlib's generic unit and associate APIs.

4. **Expose the explicit inverse of `goldenPhi`**
   - a theorem corresponding to $\varphi^{-1}=\varphi-1$ would make the concrete algebra more visible, although it would add another API surface.

The current theorem is already short; the main improvement opportunity is reuse of the existing `goldenNorm_phi` theorem.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface used by 0203 is mostly `norm_num` and ordinary tactic infrastructure.

Its golden-order dependencies are upstream declarations in the same generated development. The surrounding `GoldenDivisibility.lean` module also uses integer divisibility, conjugation, norm arithmetic, and ring tactics, so module-level import requirements are broader than those of this theorem in isolation.

The exact minimal import set is not verified because no Lean build is run in this museum pass. Import minimization therefore remains an optimization candidate rather than a confirmed result.

## Comparator challenge suitability

Yes. Useful variants are:

- A: current `apply` + `norm_num`
- B: directly reuse 0167 `goldenNorm_phi`
- C: construct a `GoldenUnit` witness explicitly from $\varphi(\varphi-1)=1$
- D: use a bridge to Mathlib `IsUnit`
- E: use a bidirectional unit-by-norm criterion with `simp`

Useful comparison axes include proof length, dependency depth, mathematical provenance, duplicated coordinate arithmetic, reuse of standard Mathlib APIs, and downstream readability.

The contrast between A and B is especially clean: should an already named closed computation be recomputed locally, or reused through its public theorem?

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0202 and immediately before `goldenUnit_one`.

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0204 `goldenUnit_one`**:

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

Declaration 0203 applies the norm `-1` branch of the unit criterion to $\varphi$. Declaration 0204 applies the norm `1` branch to the identity element itself. The following declarations then establish closure of `GoldenUnit` under negation, multiplication, and powers.
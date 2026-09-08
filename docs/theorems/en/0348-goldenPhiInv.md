# 0348 — `goldenPhiInv`

## Declaration kind

This declaration is a **`def`**.

```lean
/-- The integral inverse `phi - 1` of `phi` in the coordinate model. -/
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

## Lean type

```lean
goldenPhiInv : GoldenInt
```

`GoldenInt` uses integral coordinates in the basis `1, φ`:

```lean
structure GoldenInt where
  fst : ℤ
  snd : ℤ
```

Thus a coordinate pair `⟨a, b⟩` represents mathematically $a+b\varphi$. Therefore

```lean
⟨-1, 1⟩
```

represents

$$
-1+\varphi=\varphi-1.
$$

## Mathematical meaning

This definition introduces the integral inverse candidate of the golden basis element $\varphi$:

$$
\varphi^{-1}=\varphi-1.
$$

The coordinate ring has already established

$$
\varphi^2=\varphi+1,
$$

so formally

$$
\varphi(\varphi-1)
=\varphi^2-\varphi
=1.
$$

The immediately following declarations `golden_phi_mul_inv` and `golden_inv_mul_phi` verify that multiplication in both orders gives `goldenOne`.

Hence `goldenPhiInv` itself is not a theorem proving invertibility. It is the **concrete definition of the inverse element** used by the subsequent proofs.

## Role in the overall proof

This point begins the `GoldenUnitClassification` module, whose purpose is to classify units in the golden integer order by an elementary descent.

The strategy is to multiply a non-base unit by either `φ` or `φ⁻¹` so that a coordinate measure strictly decreases, eventually reaching a base unit. A concrete element representing `φ⁻¹` inside the same integral coordinate ring is therefore required.

`goldenPhiInv` begins the chain

```text
goldenPhiInv
  → golden_phi_mul_inv / golden_inv_mul_phi
  → goldenUnit_phiInv
  → golden_mul_phiInv_coords
  → goldenUnit_descent
  → golden unit classification
```

Thus, after the zero-sector factorization layer, it provides one of the two basic unit moves needed by the descent machinery that reorganizes unit classes into fifth-power classes.

## Direct dependencies

The body of this `def` directly depends only on the project declaration `GoldenInt`.

- `GoldenInt` — the structure representing $a+b\varphi$ by integral coordinates `⟨a,b⟩`

To interpret its mathematical meaning, the following earlier declarations are also relevant:

- `goldenPhi : GoldenInt := ⟨0, 1⟩`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `golden_phi_sq` — the relation $\varphi^2=\varphi+1$
- `goldenMul` / the `Mul GoldenInt` structure — multiplication in the golden order

These do not occur syntactically in the body of `goldenPhiInv` itself.

## Construction flow

The construction has only one step.

1. Set the result type to `GoldenInt`.
2. Supply coordinates `fst = -1` and `snd = 1` using constructor notation `⟨-1, 1⟩`.
3. This fixes the ring element $-1+\varphi=\varphi-1$.

There is no proof term or tactic script in this declaration.

## Lean-specific processing

### Structure constructor notation

```lean
⟨-1, 1⟩
```

is shorthand for `GoldenInt.mk (-1) 1`. Since the expected type is `GoldenInt`, Lean assigns the two integers to the fields `fst` and `snd`.

### Negative integer literal

The literal `-1` is interpreted as an integer because the expected type of `GoldenInt.fst` is `ℤ`. No explicit cast is needed.

### Separation between data and proofs

The inverse property is not stored as a dependent field in this definition. The development first defines the bare ring element and then proves its properties through

```lean
golden_phi_mul_inv
golden_inv_mul_phi
goldenUnit_phiInv
```

This separation keeps the element easy to reuse in coordinate calculations.

## Redundancy and duplication

The declaration is a one-line concrete definition and contains no real redundancy.

Mathematically, one could instead define it as `goldenPhi - goldenOne`. The current coordinate form `⟨-1, 1⟩`, however, exposes the normalized coordinates directly and is likely convenient for the subsequent `decide` and coordinate reductions.

Thus the issue is not duplication but a design choice between a coordinate-level canonical definition and an algebraic-expression definition.

## Optimization candidates

There is little local optimization to perform.

One possible alternative is

```lean
def goldenPhiInv : GoldenInt := goldenPhi - goldenOne
```

which emphasizes the algebraic meaning. Whether that form would improve or worsen the later `decide`, `simp`, and coordinate proofs cannot be verified without a Lean build. In the current explicit coordinate model, `⟨-1,1⟩` is already the most direct representation.

Therefore there is no strong basis for recommending a change here.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For `goldenPhiInv` alone, the required external machinery is minimal: the integer type `ℤ`, negative numeral notation, and the Lean structure-construction infrastructure. However, `GoldenInt` itself is defined earlier together with ring structures and related algebraic infrastructure, so the minimal module-level import set cannot be inferred from this one-line definition alone.

Because no Lean build is performed in this run, the exact minimal imports for `GoldenUnitClassification.lean` remain **unverified**. The broad `import Mathlib` may be reducible, but this declaration alone is not sufficient evidence for naming the exact replacement imports.

## Comparator challenge suitability

**Suitable, but too easy in isolation.**

A useful challenge would combine the definition with verification of the inverse laws:

```lean
def candidatePhiInv : GoldenInt := ?_

example :
    goldenMul goldenPhi candidatePhiInv = goldenOne := by
  ...

example :
    goldenMul candidatePhiInv goldenPhi = goldenOne := by
  ...
```

This tests whether the solver can translate $\varphi^2=\varphi+1$ into the coordinate ring and construct the correct inverse `⟨-1,1⟩`.

Using only the definition as a hole would give too small a search space and therefore low discriminating power as a Comparator challenge.

## Next declaration to read

The next declaration should be **0349 `golden_phi_mul_inv`**, whose kind is **`theorem`**.

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

It is the first verification theorem showing that the element introduced in 0348 as `goldenPhiInv = φ - 1` is actually a right inverse of $\varphi$ by concrete coordinate computation.

It is followed by the opposite multiplication order,

```lean
golden_inv_mul_phi
```

and then by `goldenUnit_phiInv`, which packages the two inverse identities into a unit certificate.

# 0349 — `golden_phi_mul_inv`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

## Lean type

```lean
golden_phi_mul_inv :
  goldenMul goldenPhi goldenPhiInv = goldenOne
```

The left-hand side is the product of two concrete elements of the golden integer order,

```lean
goldenPhi    : GoldenInt
goldenPhiInv : GoldenInt
```

and the right-hand side is the multiplicative identity

```lean
goldenOne : GoldenInt
```

Thus this theorem proves that `goldenPhiInv` is a right inverse of `goldenPhi`.

## Mathematical statement

In the coordinate model,

$$
goldenPhi = \varphi,
\qquad
goldenPhiInv = \varphi-1.
$$

Using the golden-ratio relation

$$
\varphi^2=\varphi+1,
$$

we obtain

$$
\varphi(\varphi-1)
=\varphi^2-\varphi
=1.
$$

So mathematically the theorem verifies

$$
\varphi\,\varphi^{-1}=1.
$$

Directly in coordinates, `goldenPhi = ⟨0,1⟩` and `goldenPhiInv = ⟨-1,1⟩`. The golden multiplication law

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

therefore gives

$$
(0+\varphi)(-1+\varphi)
=1+0\varphi,
$$

which is exactly `goldenOne = ⟨1,0⟩`.

## Role in the overall proof

0348 `goldenPhiInv` merely defined the ring element `⟨-1,1⟩`; it did not carry a proof that this element is actually an inverse. This theorem is the first verification theorem certifying that the chosen element cancels `goldenPhi` on the right.

The dependency chain is

```text
goldenPhiInv
  → golden_phi_mul_inv
  → golden_inv_mul_phi
  → goldenUnit_phiInv
  → goldenUnit_descent
  → goldenUnitFifthClass_of_unit
```

The immediately following theorem `golden_inv_mul_phi` proves the opposite orientation

$$
\varphi^{-1}\varphi=1,
$$

and `goldenUnit_phiInv` then uses both identities to package `goldenPhiInv` as a `GoldenUnit`.

Later, `goldenUnit_descent` multiplies units by either `goldenPhi` or `goldenPhiInv`, depending on the signs of their coordinates, in order to decrease a coordinate measure. During reconstruction it explicitly uses

```lean
show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv
```

Thus, although this theorem is tiny, it is a basic certificate ensuring the reversibility of the unit-descent step.

## Direct dependencies

The theorem statement directly references four project declarations:

- `goldenMul` — multiplication on `GoldenInt`
- `goldenPhi` — the basis element $\varphi$, represented by `⟨0,1⟩`
- `goldenPhiInv` — the element $\varphi-1$ introduced in 0348, represented by `⟨-1,1⟩`
- `goldenOne` — the multiplicative identity, represented by `⟨1,0⟩`

The proof itself directly uses Lean's `decide` tactic.

Mathematically, the relation $\varphi^2=\varphi+1$ is already encoded in the definition of `goldenMul`, so there is no need to rewrite explicitly with `golden_phi_sq` here.

## Proof flow

The entire proof is

```lean
by decide
```

It can be understood as the following concrete computation.

1. Unfold `goldenPhi` to `⟨0,1⟩`.
2. Unfold `goldenPhiInv` to `⟨-1,1⟩`.
3. Unfold `goldenMul` and calculate both coordinates of the product.
4. The result is `⟨1,0⟩`.
5. This coincides with the definition of `goldenOne`, so the structure equality holds.

All terms are closed integer expressions and the equality proposition is decidable, allowing `decide` to construct the proof term by computation.

## Lean-specific processing

### `by decide`

The notable feature of this theorem is that it uses no explicit `ring`, `norm_num`, `simp`, or `ext` script. It closes solely by evaluation of a decidable proposition:

```lean
by decide
```

This does not prove a general theorem about rings. Rather, it **computes an equality between fully concrete `GoldenInt` values**.

The proof is short because `goldenPhi`, `goldenPhiInv`, and `goldenOne` are concrete data and `goldenMul` is a computable definition, not because Lean automatically derives a general inverse theorem from abstract algebra.

### Proof by definitional reduction

This style relies strongly on definitional unfolding and decidable equality. If `goldenPhiInv` had instead been introduced as an opaque witness selected from an existence theorem, the same `by decide` proof would likely no longer work.

The explicit coordinate definition `⟨-1,1⟩` introduced in 0348 is what enables this extremely compact verification.

### `goldenMul` versus `*`

The theorem statement deliberately uses the explicit function

```lean
goldenMul goldenPhi goldenPhiInv
```

whereas later proofs also use ring notation such as `goldenPhi * goldenPhiInv`. Existing instances and simplification bridges connect the two presentations.

## Redundancy and duplication

The immediately following theorem is

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

which is almost the same statement with the factors reversed.

If commutativity of multiplication on `GoldenInt` is already conveniently available, one of these theorems could in principle be derived from the other through commutativity. Conceptually, a proof of the shape

```lean
simpa [mul_comm] using golden_phi_mul_inv
```

might be possible for the opposite orientation.

However, the current two `by decide` proofs are independent closed computations, extremely short, and robust. Replacing one with a commutativity-based proof would add a dependency, so removing the apparent duplication is not automatically an improvement.

## Optimization candidates

Locally, the current

```lean
by decide
```

is essentially minimal and there is no meaningful proof-term shortening left.

Possible design-level experiments include:

1. Prove only one of `golden_phi_mul_inv` and `golden_inv_mul_phi` by direct computation and derive the other by commutativity.
2. Investigate whether marking the inverse identities as simplification lemmas would simplify later bridges such as

   ```lean
   show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv
   ```

3. If `goldenPhiInv` is eventually integrated more deeply with the ring `IsUnit` / `Units` API, reconsider where the two inverse-law lemmas should live.

Whether `[simp]` annotations would improve the existing rewrite set, or whether a commutativity-derived proof is actually cleaner, cannot be verified without a Lean build. These are therefore **optimization candidates**, not identified defects in the current code.

## Required Mathlib imports and import optimization

The generated standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem itself, the external machinery is mainly:

- `Decidable` / `decide`
- the integer type `ℤ` and concrete integer computation
- decidable equality for the structure

No ring tactic is used in this proof.

However, the `GoldenUnitClassification` section depends on earlier project declarations that construct `GoldenInt`, its ring instances, `goldenMul`, and the unit API. The generated standalone artifact removes per-module import lines and wraps the combined source in `import Mathlib`, so the exact minimal Mathlib imports of the original module cannot be determined from this theorem alone.

Because no Lean build is performed in this run, a finer replacement for `import Mathlib` remains **unverified**. The fact that the proof itself is only `decide` does show that the entire Mathlib umbrella import is not required by this theorem in isolation.

## Comparator challenge suitability

**Very suitable, at beginner difficulty.**

A minimal challenge is

```lean
example :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by
  ?_
```

The canonical short solution is simply

```lean
decide
```

As a Comparator challenge, this tests whether the solver recognizes that

- the goal is a concrete structure equality,
- all relevant definitions are reducible and computable, and
- `decide` is sufficient.

For greater discriminating power, the inverse element itself can also be hidden:

```lean
def candidate : GoldenInt := ?_

example : goldenMul goldenPhi candidate = goldenOne := by
  ?_
```

That version tests both discovery of the inverse coordinates and verification of the resulting identity.

## Next declaration to read

The next declaration should be **0350 `golden_inv_mul_phi`**, whose kind is **`theorem`**.

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

Where 0349 verifies

$$
\varphi(\varphi-1)=1,
$$

0350 reverses the multiplication order and verifies

$$
(\varphi-1)\varphi=1.
$$

The following declaration `goldenUnit_phiInv` combines these two identities into the unit certificate for `goldenPhiInv`, so 0350 is the remaining inverse law immediately before the unit packaging step.

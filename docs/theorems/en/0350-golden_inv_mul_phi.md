# 0350 — `golden_inv_mul_phi`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

## Lean type

```lean
golden_inv_mul_phi :
  goldenMul goldenPhiInv goldenPhi = goldenOne
```

The left-hand side multiplies the two concrete golden-integer elements

```lean
goldenPhiInv : GoldenInt
goldenPhi    : GoldenInt
```

in this order, while the right-hand side is the multiplicative identity

```lean
goldenOne : GoldenInt
```

Thus the theorem proves, by a concrete coordinate computation, that `goldenPhiInv` is a left inverse of `goldenPhi`.

## Mathematical statement

In the coordinate model,

$$
goldenPhiInv = \varphi-1,
\qquad
goldenPhi = \varphi.
$$

From the basic golden-ratio relation

$$
\varphi^2=\varphi+1
$$

we obtain

$$
(\varphi-1)\varphi
=\varphi^2-\varphi
=1.
$$

So mathematically the theorem verifies

$$
\varphi^{-1}\varphi=1.
$$

Directly in `GoldenInt` coordinates,

```lean
goldenPhiInv = ⟨-1, 1⟩
goldenPhi    = ⟨0, 1⟩
goldenOne    = ⟨1, 0⟩
```

and the multiplication law

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

gives

$$
(-1+\varphi)(0+\varphi)
=1+0\varphi,
$$

which is exactly `goldenOne`.

## Role in the overall proof

0348 `goldenPhiInv` introduced the concrete element corresponding to $\varphi-1$, and 0349 `golden_phi_mul_inv` established one inverse law,

$$
\varphi(\varphi-1)=1.
$$

The present theorem reverses the multiplication order and proves

$$
(\varphi-1)\varphi=1,
$$

completing the two-sided inverse information needed for `goldenPhiInv` and `goldenPhi`.

The dependency flow is

```text
goldenPhiInv
  → golden_phi_mul_inv
  → golden_inv_mul_phi
  → goldenUnit_phiInv
  → goldenUnit_descent
  → GoldenUnitFifthClass
```

The immediately following theorem `goldenUnit_phiInv` chooses `goldenPhi` as the witness for `GoldenUnit goldenPhiInv` and stores this theorem together with 0349 as its two inverse proofs:

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

Later, `goldenUnit_descent` actually uses this orientation when reconstructing a branch that multiplies by `goldenPhiInv`:

```lean
show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi
```

Thus the theorem is not merely a symmetric duplicate: it directly supplies one of the cancellation certificates used to make the unit-descent step reversible.

## Direct dependencies

The theorem statement directly references four project declarations:

- `goldenMul` — multiplication on `GoldenInt`.
- `goldenPhiInv` — $\varphi-1$ from 0348, with coordinates `⟨-1,1⟩`.
- `goldenPhi` — the basis element $\varphi$, with coordinates `⟨0,1⟩`.
- `goldenOne` — the multiplicative identity, with coordinates `⟨1,0⟩`.

The proof itself directly uses Lean's `decide` tactic.

Although 0349 `golden_phi_mul_inv` is mathematically almost the same statement in the opposite order, this theorem's proof term does not depend on it. The current source certifies both orientations as independent closed computations.

The relation $\varphi^2=\varphi+1$ is already encoded in the coordinate definition of `goldenMul`, so no explicit rewrite by a theorem such as `golden_phi_sq` is needed here.

## Proof flow

The entire proof is one line:

```lean
by decide
```

Expanded conceptually, the computation is:

1. Unfold `goldenPhiInv` to `⟨-1,1⟩`.
2. Unfold `goldenPhi` to `⟨0,1⟩`.
3. Unfold `goldenMul` and compute the two coordinates of the product.
4. The product reduces to `⟨1,0⟩`.
5. `goldenOne` also reduces to `⟨1,0⟩`, so the structure equality holds.

The goal contains no variables: it is a closed proposition involving computable integer operations and decidable equality on `GoldenInt`. Therefore `decide` can produce the proof term by evaluation.

## Lean-specific processing

### `by decide`

The theorem uses no explicit `ring`, `norm_num`, `simp`, or `ext` script. It closes solely with

```lean
by decide
```

This is not an abstract proof that a right inverse in a commutative ring is automatically a left inverse. Instead, because `goldenPhiInv`, `goldenPhi`, and `goldenOne` are all concrete values and `goldenMul` is computable, Lean is **deciding the concrete equality of two `GoldenInt` values**.

### Independent computation of the two inverse orientations

0349 and 0350 are mathematically interderivable from commutativity, but the Lean source proves both independently with `by decide`. Consequently, 0350 has no proof dependency on 0349 and supplies `goldenUnit_phiInv` with a second, independent closed-computation certificate.

### `goldenMul` versus `*`

The theorem statement uses the explicit function

```lean
goldenMul goldenPhiInv goldenPhi
```

whereas later descent proofs use ring notation such as

```lean
goldenPhiInv * goldenPhi
```

The ring instance constructed earlier connects these forms, allowing the theorem to be used later through a bridge such as

```lean
show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi
```

## Redundancy and duplication

The preceding theorem

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

is essentially the same closed computation with the factors reversed.

If commutativity of `GoldenInt` multiplication is conveniently available, one theorem could in principle be derived from the other. Conceptually, a proof of the shape

```lean
simpa [mul_comm] using golden_phi_mul_inv
```

might replace the second closed computation.

However, the current proof is itself only `by decide` and introduces no dependency on a commutativity lemma. From the perspectives of line count, locality of dependencies, and proof robustness, the apparent duplication is therefore reasonable.

## Optimization candidates

Locally, the existing

```lean
by decide
```

is already essentially minimal.

Possible design-level experiments are:

1. Prove only one of 0349 and 0350 by `decide`, deriving the other by commutativity.
2. Consider the two inverse laws as `[simp]` candidates and test whether this simplifies later explicit bridges such as `show ... by exact ...` in unit descent.
3. Package the inverse laws more directly into a unit-constructor API, potentially making the separate lemmas local if they are not otherwise useful.
4. If `GoldenUnit` is later connected more tightly to Mathlib's `IsUnit` / `Units` API, reconsider whether these inverse certificates should live closer to the standard unit interface.

Whether `[simp]` annotations improve the existing rewrite set, or whether a commutativity-derived proof actually reduces dependencies, cannot be established without a Lean build. These are therefore **optimization candidates**, not identified defects.

## Required Mathlib imports and import optimization

The generated standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem itself, the directly relevant external machinery is mainly:

- `Decidable` / `decide`,
- the integer type `ℤ` and concrete integer computation,
- the infrastructure providing decidable equality for `GoldenInt`.

No `ring`, `omega`, or `norm_num` tactic is used by this proof.

However, `GoldenInt`, `goldenMul`, and its ring instances depend on earlier project declarations, while the generated standalone source merges module boundaries and wraps the combined development in `import Mathlib`. The exact minimal Mathlib imports of the original module therefore cannot be determined from this theorem alone.

No Lean build is performed in this run, so finer-grained import replacements remain **unverified**. At minimum, the one-line proof itself does not require the full range of tactics exposed by the umbrella `Mathlib` import.

## Comparator challenge suitability

**Very suitable, at beginner difficulty.**

A minimal challenge is

```lean
example :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by
  ?_
```

and the canonical source-level solution is simply

```lean
decide
```

As a Comparator challenge, this tests whether a solver recognizes that

- the goal is a concrete structure equality,
- all terms are reducible closed values, and
- a general algebraic proof is unnecessary because `decide` suffices.

A paired challenge with 0349 could expose one orientation as a known theorem and leave the other as the hole. This permits comparison between a solution that reuses the known result through commutativity and a solution that independently uses `decide`.

The mathematical difficulty is low, so this is better viewed as a micro-challenge for definitional reduction, closed computation, and local proof-strategy selection than as a discriminator for large-scale theorem-proving capability.

## Next declaration to read

The next declaration should be **0351 `goldenUnit_phiInv`**, whose kind is **`theorem`**.

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

Here `GoldenUnit` is the two-sided-inverse predicate

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

The 0351 theorem chooses `goldenPhi` as the witness and combines the present identity

$$
(\varphi-1)\varphi=1
$$

with the 0349 identity

$$
\varphi(\varphi-1)=1
$$

to promote `goldenPhiInv = \varphi-1` to a formal `GoldenUnit` certificate. From there the development proceeds into the unit-descent machinery.

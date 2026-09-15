# 0362 — `golden_sector_zero_mul_phiInv`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  rw [mul_pow]
  calc
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
        goldenPhiInv * delta ^ 5 := by ring
    _ = (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5 := by
      rw [golden_phi_four_mul_inv_five]
    _ = goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5) := by ring
```

This is the local lemma that handles sector `0` of `GoldenUnitFifthClass` after multiplication by `goldenPhiInv`: it wraps the representative exponent back to `4` and absorbs the extra `goldenPhiInv ^ 5` into the fifth-power base.

## Lean type

```lean
golden_sector_zero_mul_phiInv :
  (delta : GoldenInt) →
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5
```

It is an equality in the golden integer ring for arbitrary `delta : GoldenInt`. Because it is `private`, the declaration name is an internal helper of `GoldenUnitClassification.lean`, not part of the external API.

## Mathematical statement

Reading `goldenPhi = φ` and `goldenPhiInv = φ⁻¹`, the left-hand side is

$$
(\varphi^0\delta^5)\varphi^{-1}
=\delta^5\varphi^{-1}.
$$

0361 `golden_phi_four_mul_inv_five` gives

$$
\varphi^4(\varphi^{-1})^5=\varphi^{-1}.
$$

Therefore

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1})^5\delta^5
=\varphi^4(\varphi^{-1}\delta)^5.
$$

Thus, modulo fifth powers, the unit class transition is

$$
0\xrightarrow{\times\varphi^{-1}}4.
$$

At the exponent level this is simply `0 - 1 ≡ 4 (mod 5)`. Lean does not use a negative natural exponent here; instead, the fifth power of `φ⁻¹` is absorbed into a new fifth-power witness, returning the representative to `4 : Fin 5`.

## Role in the full proof

0360 `GoldenUnitFifthClass` defines a five-sector representation

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

In 0359 `goldenUnit_descent`, the original unit `x` is reconstructed from a smaller unit `y` by either

$$
x=y\varphi
\quad\text{or}\quad
x=y\varphi^{-1}.
$$

To close the strong induction for unit classification, one must therefore prove that multiplying an already classified element by `φ` or `φ⁻¹` preserves `GoldenUnitFifthClass`.

For multiplication by `φ⁻¹`, sectors `1,2,3,4` are handled by simply decrementing the representative exponent. Sector `0` is exceptional because `-1` is not directly available as a natural-number representative of `Fin 5`. This theorem handles exactly that wrap-around case.

The following theorem `goldenUnitFifthClass_mul_phiInv` uses this result directly in its `i = 0` branch as the witness transformation.

## Direct dependencies

The main project declarations appearing directly are:

- `GoldenInt` — the coordinate type of golden integers.
- `goldenPhi` — the golden-ratio unit `φ`.
- `goldenPhiInv` — the multiplicative inverse of `φ`.
- 0361 `golden_phi_four_mul_inv_five` — the wrap-around identity `φ⁴(φ⁻¹)⁵ = φ⁻¹`.

On the Lean/Mathlib side, the proof uses ordinary ring operations `*`, `^`, the theorem `mul_pow`, and the `ring` tactic.

The background theorem `golden_phi_mul_inv : goldenPhi * goldenPhiInv = 1` also exists, but it is not directly invoked in this proof.

## Proof flow

### 1. Expand the fifth power of a product

The proof begins with

```lean
rw [mul_pow]
```

which turns

```lean
(goldenPhiInv * delta) ^ 5
```

into

```lean
goldenPhiInv ^ 5 * delta ^ 5
```

and exposes exactly the subexpression needed for 0361.

### 2. Simplify the sector-zero left-hand side

The expression

```lean
(goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv
```

is rewritten to

```lean
goldenPhiInv * delta ^ 5
```

and this step is closed by

```lean
by ring
```

Mathematically this uses only `φ⁰ = 1` and commutativity.

### 3. Insert the wrap-around identity

The middle equality

```lean
goldenPhiInv * delta ^ 5 =
  (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5
```

is proved by

```lean
rw [golden_phi_four_mul_inv_five]
```

This is the essential step: `φ⁻¹` is replaced with `φ⁴(φ⁻¹)⁵`, returning the representative exponent to `4`.

### 4. Reassociate into the fifth-power witness form

Finally,

```lean
(goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5
```

is rearranged into

```lean
goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5)
```

again by `ring`.

Together with the initial `rw [mul_pow]`, this gives the target form

```lean
goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5
```

required by `GoldenUnitFifthClass`.

## Lean-specific processing

### `rw [mul_pow]`

`mul_pow` is the standard theorem

$$
(ab)^n=a^n b^n.
$$

Because `GoldenInt` is equipped with a commutative-ring structure, it applies directly.

Here it is not merely cosmetic normalization: it exposes `goldenPhiInv ^ 5`, allowing 0361 to be used.

### `calc`

The `calc` block mirrors the mathematical structure of the proof in three explicit stages:

1. simplify sector `0`,
2. insert the 0361 wrap-around identity,
3. rebuild the fifth-power witness.

### `ring`

The first and third steps are purely commutative-ring normalization: associativity, commutativity, the unit element, and powers. `ring` hides those low-level rearrangements.

## Redundancy and overlap

The proof is short and contains no serious redundancy.

The first

```lean
by ring
```

could instead be written using `pow_zero`, `one_mul`, and commutativity. Likewise, the final `ring` could be replaced with associativity and commutativity rewrites.

The current proof is shorter, although it hides the fact that these steps require only very elementary multiplicative algebra.

Conceptually, `golden_sector_zero_mul_phiInv` and the next theorem `golden_sector_succ_mul_phiInv` are two branches of the same cyclic action of multiplication by `φ⁻¹` on five unit sectors. They could in principle be unified.

## Optimization candidates

1. **Keep the current proof** — the `calc` structure makes the `0 → 4` transition very clear and the proof is already small.
2. **Reduce dependence on `ring`** — proving the rearrangements with `pow_zero`, `one_mul`, `mul_assoc`, and `mul_comm` could weaken the algebraic/tactic requirements.
3. **Generalize the sector transition** — a single theorem using arithmetic in `Fin 5` plus a witness correction could combine the zero and successor cases. However, the `Fin` arithmetic and witness transport may become more complicated than the current explicit split.
4. **Unify notation** — this theorem uses ring notation `*` / `^` rather than the explicit `goldenMul` / `goldenPow` API. The surrounding bridge lemmas already make both notations compatible, so the gain from changing this is likely limited.

These are design candidates only; their Lean validity has not been checked because no Lean build was run.

## Required Mathlib imports and import optimization

The standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem itself, the directly relevant Mathlib functionality is mainly:

- natural-number powers and `mul_pow`,
- basic commutative-ring equalities,
- the `ring` tactic.

Therefore the theorem does not intrinsically require all of `Mathlib`. In the source module `GoldenUnitClassification.lean`, a smaller import set should be possible once the project declarations `GoldenInt`, `goldenPhi`, `goldenPhiInv`, 0361, and the surrounding unit-class API are available, plus support for `ring`.

The exact minimal import set is unverified because no Lean build was performed.

## Comparator challenge suitability

**Suitable.**

A challenge can be stated as:

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  ?_
```

with 0361 supplied as a premise:

```lean
golden_phi_four_mul_inv_five :
  goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv
```

Unlike 0361, which is a fully concrete equality, this theorem contains an arbitrary `delta`. A solver must understand how to:

- distribute the fifth power using `mul_pow`,
- insert the wrap-around lemma in the correct direction,
- normalize the ring expression back into witness form.

It is therefore a good small Comparator challenge for testing the ability to lift a concrete local identity into a generic witness transformation.

## Next declaration to read

Next is **0363 `golden_sector_succ_mul_phiInv`**, a **`private theorem`**.

```lean
private theorem golden_sector_succ_mul_phiInv (delta : GoldenInt) (n : ℕ) :
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5 := by
  calc
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
        goldenPhi ^ n * delta ^ 5 * (goldenPhi * goldenPhiInv) := by
      rw [pow_succ]
      ring
    _ = goldenPhi ^ n * delta ^ 5 := by
      rw [show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv, mul_one]
```

Where 0362 handles the wrap-around `0 → 4`, 0363 handles the generic successor transition

$$
n+1\xrightarrow{\times\varphi^{-1}}n.
$$

Together these two lemmas close all five branches of the later theorem `goldenUnitFifthClass_mul_phiInv`.
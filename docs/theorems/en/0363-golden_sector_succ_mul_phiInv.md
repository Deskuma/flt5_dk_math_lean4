# 0363 — `golden_sector_succ_mul_phiInv`

## Declaration kind

This declaration is a **`private theorem`**.

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

Where 0362 `golden_sector_zero_mul_phiInv` handles the wrap-around case `0 → 4`, this theorem handles the ordinary successor-sector transition

$$
n+1 \xrightarrow{\times\varphi^{-1}} n.
$$

## Lean type

```lean
golden_sector_succ_mul_phiInv :
  (delta : GoldenInt) → (n : ℕ) →
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5
```

It is an equality in the golden-integer ring for arbitrary `delta : GoldenInt` and `n : ℕ`. Because it is `private`, it serves as an internal helper for the unit-class classification rather than as an exported API theorem.

## Mathematical statement

Reading `goldenPhi = φ` and `goldenPhiInv = φ⁻¹`, the theorem states

$$
(\varphi^{n+1}\delta^5)\varphi^{-1}
=\varphi^n\delta^5.
$$

Using

$$
\varphi^{n+1}=\varphi^n\varphi,
\qquad
\varphi\varphi^{-1}=1,
$$

we obtain

$$
\varphi^{n+1}\delta^5\varphi^{-1}
=\varphi^n\delta^5(\varphi\varphi^{-1})
=\varphi^n\delta^5.
$$

Unlike the zero-sector theorem 0362, no change to the fifth-power witness `delta` is needed. For sectors `1,2,3,4`, multiplication by `φ⁻¹` simply decreases the representative exponent by one.

## Role in the full proof

0360 `GoldenUnitFifthClass` defines the five-sector representation

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

To connect the strict descent theorem 0359 `goldenUnit_descent` to strong induction, the proof must show that multiplying an already classified smaller unit by `φ` or `φ⁻¹` preserves membership in `GoldenUnitFifthClass`.

For multiplication by `φ⁻¹`, sector `0` is exceptional because `-1 ≡ 4 (mod 5)` and therefore requires the wrap-around theorem 0362. This theorem handles all remaining successor cases uniformly. In the following theorem `goldenUnitFifthClass_mul_phiInv`, it is used with `n = 0,1,2,3` in the branches corresponding to sectors `1,2,3,4`.

Thus 0362 and 0363 together implement the complete `−1` action on `Fin 5` sectors.

## Direct dependencies

The main project-local dependencies are:

- `GoldenInt` — the coordinate type of golden integers.
- `goldenPhi` — the golden-ratio unit `φ`.
- `goldenPhiInv` — the multiplicative inverse of `φ`.
- `golden_phi_mul_inv` — the identity `goldenPhi * goldenPhiInv = 1`.

On the Mathlib side, the proof mainly uses:

- `pow_succ`
- `mul_one`
- `rw`
- `ring`

The theorem does not directly depend on 0361 `golden_phi_four_mul_inv_five` or 0362 `golden_sector_zero_mul_phiInv`. They are conceptually paired with it, but not proof dependencies.

## Proof flow

### 1. Split the successor power

The first `calc` step uses

```lean
rw [pow_succ]
ring
```

`pow_succ` expands

```lean
goldenPhi ^ (n + 1)
```

as

```lean
goldenPhi ^ n * goldenPhi
```

and `ring` then normalizes the commutative product into the form

```lean
goldenPhi ^ n * delta ^ 5 *
  (goldenPhi * goldenPhiInv)
```

so that the inverse pair becomes explicit.

### 2. Cancel `φ * φ⁻¹`

The second step uses

```lean
rw [show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv, mul_one]
```

The `show ... by exact ...` expression presents the existing theorem `golden_phi_mul_inv` as precisely the equality required for rewriting. It replaces

```lean
goldenPhi * goldenPhiInv
```

by `1`, after which `mul_one` removes the terminal unit and yields

```lean
goldenPhi ^ n * delta ^ 5
```

as required.

## Lean-specific processing

### `pow_succ`

This is the standard natural-exponent identity

$$
a^{n+1}=a^n a.
$$

It is the entry point for turning the mathematical idea “lower the exponent by one” into multiplication by an explicit inverse pair.

### `ring`

Here `ring` is not proving any golden-integer number theory. It only normalizes the commutative-ring expression after `pow_succ`, rearranging factors so that `goldenPhi * goldenPhiInv` appears together.

### `show ... by exact golden_phi_mul_inv`

This makes the exact equality used by `rw` explicit. Compared with a bare rewrite, it documents the intended type and can avoid ambiguity in elaboration.

## Redundancy and overlap

The proof is short and has little internal redundancy.

Conceptually, however, 0362 and 0363 are two pieces of the same operation: multiplication by `φ⁻¹` on the five sectors. The current code deliberately separates the zero case from the successor cases, avoiding negative exponents and modular-arithmetic transport in the proof term.

The first `ring` also performs only associativity, commutativity, and normalization after `pow_succ`; it may be replaceable by direct algebraic rewrites.

## Optimization candidates

1. **Keep the current proof** — it is already very small and the division of responsibility with 0362 is clear.
2. **Reduce `ring` usage** — explicit uses of `mul_assoc`, `mul_left_comm`, and `mul_comm` may remove the tactic dependency.
3. **Try a `simpa` proof** — with suitable simp lemmas for `pow_succ` and `golden_phi_mul_inv`, the proof may compress further, though the rewrite structure would become less visible.
4. **Generalize to a `Fin 5` cyclic action** — 0362 and 0363 could potentially be unified as a theorem implementing `i ↦ i - 1 mod 5`. The zero-case witness correction, however, may make that abstraction more complicated than the current explicit split.

These alternatives are not verified here because no Lean build is performed.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem itself, the directly needed Mathlib functionality is essentially natural-number powers, commutative-ring algebra, `pow_succ`, `mul_one`, and the `ring` tactic, together with the project-local golden-integer inverse API.

Therefore importing all of `Mathlib` is likely broader than necessary for this theorem alone. The exact minimal imports for the actual `GoldenUnitClassification.lean` module cannot be certified without a Lean build because surrounding declarations contribute additional dependencies.

## Suitability as a Comparator challenge

**Suitable.**

A compact challenge can be formed as

```lean
private theorem golden_sector_succ_mul_phiInv (delta : GoldenInt) (n : ℕ) :
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5 := by
  ?_
```

with

```lean
golden_phi_mul_inv : goldenPhi * goldenPhiInv = 1
```

provided as an available lemma.

The challenge tests whether a model can:

- expose one factor using `pow_succ`,
- rearrange the product so the inverse pair is visible,
- close the goal using `φφ⁻¹ = 1`.

It is an even purer algebraic micro-challenge than 0362.

## Next declaration to read

The next declaration is **0364 `goldenUnitFifthClass_mul_phiInv`**, a **`theorem`**.

It extracts the witness `⟨i, delta, hx⟩` from `GoldenUnitFifthClass x` and performs `fin_cases i` over all five sectors. The zero branch uses 0362 `golden_sector_zero_mul_phiInv`, while sectors `1,2,3,4` use this theorem 0363 `golden_sector_succ_mul_phiInv`, completing

$$
GoldenUnitFifthClass(x)
\Longrightarrow
GoldenUnitFifthClass(x\varphi^{-1}).
$$

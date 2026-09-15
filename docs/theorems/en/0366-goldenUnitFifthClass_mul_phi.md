# 0366 — `goldenUnitFifthClass_mul_phi`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem goldenUnitFifthClass_mul_phi {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhi) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨4, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨0, by decide⟩, goldenMul goldenPhi delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
```

In the Lean source of record this theorem appears before `goldenUnitFifthClass_mul_phiInv`. The existing explanation sequence had already documented `...mul_phiInv` and later base cases, so this file fills that missed declaration.

## Lean type

```lean
goldenUnitFifthClass_mul_phi :
  {x : GoldenInt} →
  GoldenUnitFifthClass x →
  GoldenUnitFifthClass (goldenMul x goldenPhi)
```

`GoldenUnitFifthClass x` means

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Thus, if `x` admits a five-sector representation modulo fifth powers, then its product with `φ` admits one as well.

## Mathematical statement

Read the assumption as

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

The theorem proves that

$$
x\varphi
$$

can again be written in the form

$$
\varphi^j\gamma^5.
$$

The sector transition is

$$
0\longmapsto1,
\qquad
1\longmapsto2,
\qquad
2\longmapsto3,
\qquad
3\longmapsto4,
\qquad
4\longmapsto0.
$$

Equivalently, at the exponent level,

$$
i\longmapsto i+1\pmod5.
$$

For the first four cases the fifth-power witness `delta` is unchanged. The wrap-around case `4 → 0` uses

$$
\varphi^4\delta^5\varphi
=\varphi^5\delta^5
=(\varphi\delta)^5,
$$

so the witness is changed by

$$
\delta\longmapsto\varphi\delta.
$$

## Role in the full proof

The earlier theorem `goldenUnit_descent` shortens every non-base golden unit and provides a reconstruction

$$
x=y\varphi
$$

or

$$
x=y\varphi^{-1}.
$$

To turn this descent into a strong-induction classification, one must lift the fifth-class property from the smaller unit `y` back to both possible reconstructions. This theorem provides closure under multiplication by `φ`; `goldenUnitFifthClass_mul_phiInv` provides closure under multiplication by `φ⁻¹`.

In `goldenUnitFifthClass_of_unit`, the branch with `x = yφ` uses the theorem directly:

```lean
exact goldenUnitFifthClass_mul_phi hyClass
```

Hence this is one of the two closure bridges connecting the local unit descent to the global fifth-power classification.

## Direct dependencies

The main project-level dependencies are:

- `GoldenInt` — the coordinate type for golden integers.
- `goldenPhi` — the golden unit `φ`.
- `goldenMul` — multiplication in the golden order.
- `goldenPow` — powers in the project wrapper notation.
- `GoldenUnitFifthClass` — the predicate `x = φ^i δ^5` with `i : Fin 5`.
- `golden_mul_eq` — rewriting bridge from `goldenMul` to ordinary multiplication.
- `golden_pow_eq` — rewriting bridge from `goldenPow` to ordinary powers.

The Lean/Mathlib mechanisms used directly are `rcases`, `fin_cases`, `refine`, `decide`, `rw`, `simp only`, and `ring`.

The helper theorems `golden_sector_zero_mul_phiInv` and `golden_sector_succ_mul_phiInv` are not dependencies of this theorem; they belong specifically to the inverse-`φ` direction.

## Proof / construction flow

### 1. Extract the fifth-class witnesses

```lean
rcases hx with ⟨i, delta, hx⟩
```

produces

- `i : Fin 5`,
- `delta : GoldenInt`,
- `hx : x = φ^i δ^5`.

This turns the abstract predicate into an explicit sector representation.

### 2. Enumerate all elements of `Fin 5`

```lean
fin_cases i
```

splits into the five cases `i = 0,1,2,3,4`.

Mathematically this is one cyclic map

$$
i\mapsto i+1\pmod5,
$$

but the proof deliberately avoids a general modular-arithmetic layer and works with five concrete cases.

### 3. Handle `0 → 1`, `1 → 2`, `2 → 3`, `3 → 4`

In the first four branches, the new sector is `1,2,3,4` respectively and the fifth-power witness remains `delta`.

For example, the `i = 0` branch is

```lean
refine ⟨⟨1, by decide⟩, delta, ?_⟩
rw [hx]
simp only [golden_mul_eq, golden_pow_eq]
ring
```

`rw [hx]` replaces `x` by its known sector form, `simp only` removes the project wrappers, and `ring` closes the resulting commutative-ring identity.

### 4. Handle the wrap-around `4 → 0`

The last branch chooses

```lean
refine ⟨⟨0, by decide⟩, goldenMul goldenPhi delta, ?_⟩
```

because

$$
\varphi^4\delta^5\varphi
=\varphi^5\delta^5
=(\varphi\delta)^5.
$$

Again the final goal is discharged by the sequence `rw`, `simp only`, `ring`.

## Lean-specific processing

### `fin_cases i`

This tactic enumerates all values of `i : Fin 5`. It keeps the cyclic transition table explicit in the proof and avoids introducing arithmetic lemmas for addition modulo five.

### `⟨k, by decide⟩ : Fin 5`

Each new sector witness requires both the value `k` and a proof of `k < 5`. Because `k` is one of the concrete numerals `0,1,2,3,4`, `decide` closes the bound immediately.

### `simp only [golden_mul_eq, golden_pow_eq]`

This normalizes only the project-specific wrappers needed for the ring calculation. The use of `only` limits dependence on the global simp set and makes the transformation auditable.

### `ring`

Once the existential witnesses have been chosen, every branch reduces to a commutative-ring identity. In particular, the wrap-around identity contains the algebraic fact

$$
(\varphi\delta)^5=\varphi^5\delta^5,
$$

which `ring` handles after wrapper normalization.

## Redundancy and duplication

All five branches repeat

```lean
rw [hx]
simp only [golden_mul_eq, golden_pow_eq]
ring
```

and the first four branches differ essentially only in the numeric sector witness.

The duplication is not necessarily harmful, however. It makes the complete transition table visible, avoids extra `Fin` arithmetic infrastructure, and localizes failures to individual sectors.

## Optimization candidates

1. Combine the ordinary cases into one branch for `i.val + 1 < 5`, leaving only the wrap-around case separate.
2. Define a cyclic successor operation on `Fin 5` and state sector transport through that API.
3. Unify the `φ` and `φ⁻¹` closure theorems as a signed unit-step transport theorem.
4. Strengthen the local simp API around `golden_mul_eq` and `golden_pow_eq` to reduce repeated normalization code.
5. Extract the repeated `rw; simp only; ring` pattern into a small helper theorem.

These are design candidates only. No Lean build was run, so no claim is made that they actually reduce dependencies or proof-term size.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the file as a whole.

The Mathlib functionality visibly required by this theorem itself includes

- `Fin 5`,
- `fin_cases`,
- `decide`,
- `ring`,
- `rw`,
- `simp only`.

`import Mathlib` is likely broader than necessary for this theorem in isolation. A smaller set involving finite-type case analysis, ring normalization, and the basic tactic infrastructure may suffice, but the exact minimal import set is not asserted because builds are explicitly out of scope for this run.

## Comparator challenge suitability

 **Yes; this is a good intermediate micro-challenge.**

A useful challenge would provide `GoldenUnitFifthClass`, `goldenPhi`, `golden_mul_eq`, and `golden_pow_eq`, and ask for

```lean
theorem challenge {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhi) := by
  ...
```

The key evaluation points are

- extracting and rebuilding existential witnesses,
- finite case analysis over `Fin 5`,
- discovering the witness change `delta ↦ φδ` in the wrap-around case,
- reducing project wrappers to a ring identity.

The algebra itself is intentionally lightweight because `ring` can certify it; the challenge is primarily about witness design and finite-sector transport.

## Next declaration to read

The immediate next declaration in the Lean source is

```lean
theorem goldenUnitFifthClass_mul_phiInv ...
```

which has already been documented as `0364-goldenUnitFifthClass_mul_phiInv.md`. The following `goldenUnitFifthClass_one` has likewise already been documented as 0365.

Therefore the **next still-unexplained declaration** is

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
  decide
```

This `private theorem` places the base unit `-1` in sector `0` and is used directly in the base case of `goldenUnitFifthClass_of_unit`.
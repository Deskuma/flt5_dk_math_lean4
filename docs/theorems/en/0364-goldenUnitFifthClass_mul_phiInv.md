# 0364 — `goldenUnitFifthClass_mul_phiInv`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem goldenUnitFifthClass_mul_phiInv {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhiInv) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨4, by decide⟩, goldenMul goldenPhiInv delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_zero_mul_phiInv delta
  · refine ⟨⟨0, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 0
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 1
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 2
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 3
```

Where 0362 `golden_sector_zero_mul_phiInv` and 0363 `golden_sector_succ_mul_phiInv` provide the local sector transitions, this theorem lifts those transitions to the existential witnesses of `GoldenUnitFifthClass` and proves that multiplication by `φ⁻¹` preserves the five-sector classification.

## Lean type

```lean
goldenUnitFifthClass_mul_phiInv :
  {x : GoldenInt} →
  GoldenUnitFifthClass x →
  GoldenUnitFifthClass (goldenMul x goldenPhiInv)
```

Thus, whenever a golden integer `x` has a five-sector representation modulo fifth powers, its product with `φ⁻¹` also has a representation of the same form.

Expanding the definition of `GoldenUnitFifthClass`, the hypothesis is

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

and the conclusion is

```lean
∃ j : Fin 5, ∃ gamma : GoldenInt,
  goldenMul x goldenPhiInv =
    goldenMul (goldenPow goldenPhi j.val) (goldenPow gamma 5)
```

## Mathematical statement

Read `GoldenUnitFifthClass x` as

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

The theorem states that

$$
x\varphi^{-1}
$$

again admits a representation in the same five-sector form.

The sector transitions are

$$
0\longmapsto4,
\qquad
1\longmapsto0,
\qquad
2\longmapsto1,
\qquad
3\longmapsto2,
\qquad
4\longmapsto3.
$$

At the level of exponents this is simply

$$
i\longmapsto i-1\pmod 5.
$$

The zero sector is exceptional only because one cannot directly write sector `-1`. Therefore 0362 changes the fifth-power witness itself by

$$
\delta\longmapsto\varphi^{-1}\delta
$$

and uses

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5
$$

to wrap back to sector `4`.

For sectors `1,2,3,4`, the witness `delta` is unchanged and 0363 applies directly:

$$
(\varphi^{n+1}\delta^5)\varphi^{-1}
=\varphi^n\delta^5.
$$

## Role in the overall proof

0359 `goldenUnit_descent` constructs, from a golden unit `x` of measure greater than `1`, a smaller golden unit `y` together with one of the reconstruction identities

$$
x=y\varphi
$$

or

$$
x=y\varphi^{-1}.
$$

To connect that strict descent to strong induction, one must know that if the smaller unit `y` lies in a fifth class, then both `yφ` and `yφ⁻¹` also lie in a fifth class.

The preceding theorem `goldenUnitFifthClass_mul_phi` handles the `φ` direction. The present theorem handles the `φ⁻¹` direction.

Indeed, later in `goldenUnitFifthClass_of_unit`, the two reconstruction branches are closed by

```lean
exact goldenUnitFifthClass_mul_phi hyClass
```

or

```lean
exact goldenUnitFifthClass_mul_phiInv hyClass
```

respectively.

The theorem is therefore the bridge from local finite sector arithmetic to the global natural-number descent used to classify all golden units modulo fifth powers.

## Direct dependencies

The principal project-local dependencies are:

- `GoldenInt` — the type of golden integers.
- `goldenMul` — multiplication on golden integers.
- `goldenPhi` — the golden-ratio unit `φ`.
- `goldenPhiInv` — the multiplicative inverse of `φ`.
- `goldenPow` — exponentiation on golden integers.
- `GoldenUnitFifthClass` — the five-sector predicate `x = φ^i δ^5` with `i : Fin 5`.
- `golden_sector_zero_mul_phiInv` — the wrap-around transition `0 → 4`.
- `golden_sector_succ_mul_phiInv` — the ordinary successor transition `n+1 → n`.
- `golden_mul_eq` — rewrite bridge between `goldenMul` and ordinary multiplication notation.
- `golden_pow_eq` — rewrite bridge between `goldenPow` and ordinary power notation.

On the Lean / Mathlib side the proof mainly uses:

- `rcases`
- `fin_cases`
- `refine`
- `decide`
- `rw`
- `simpa only`

0361 `golden_phi_four_mul_inv_five` is not called directly here. It is used inside 0362, so the dependency is indirect by one layer.

## Proof flow

### 1. Extract the fifth-class witnesses

The proof begins with

```lean
rcases hx with ⟨i, delta, hx⟩
```

which produces

- `i : Fin 5`,
- `delta : GoldenInt`,
- `hx : x = φ^i δ^5`.

This converts the abstract predicate into concrete sector arithmetic.

### 2. Enumerate all of `Fin 5`

```lean
fin_cases i
```

splits the proof into exactly the five cases `i = 0,1,2,3,4`.

Mathematically the transition is one modular formula,

$$
i\mapsto i-1\pmod5,
$$

but explicit finite case analysis avoids introducing a separate API for subtraction or modular arithmetic on `Fin 5`.

### 3. Wrap sector `0` to sector `4`

In the first branch the new witnesses are chosen as

```lean
⟨⟨4, by decide⟩, goldenMul goldenPhiInv delta, ...⟩
```

so the new sector is `4` and the new fifth-power base is `φ⁻¹δ`.

Then

```lean
rw [hx]
```

replaces `x` by its original sector representation, and

```lean
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_zero_mul_phiInv delta
```

matches the local theorem 0362 to the required existential witness equation.

### 4. Decrement sectors `1,2,3,4`

In the remaining four branches the fifth-power base remains `delta`, while the new sector witnesses are respectively `0,1,2,3`.

For example, sector `1` is handled by

```lean
refine ⟨⟨0, by decide⟩, delta, ?_⟩
rw [hx]
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_succ_mul_phiInv delta 0
```

and the same pattern with `n = 1,2,3` closes `2→1`, `3→2`, and `4→3`.

## Lean-specific processing

### `fin_cases i`

This tactic enumerates all inhabitants of the finite type `Fin 5`.

The mathematical content is a cyclic shift, but `fin_cases` turns that shift into five concrete goals and avoids any need for lemmas about `Fin` subtraction or `% 5`.

### `⟨k, by decide⟩ : Fin 5`

Each new sector witness has type `Fin 5`, so Lean needs not only the numeral `k` but also a proof of `k < 5`.

For `k = 0,1,2,3,4` these are closed decidable arithmetic facts, hence `by decide` is sufficient.

### `rw [hx]`

This rewrites the abstract `x` in the goal to the concrete witness form `φ^i δ^5`, producing precisely the algebraic shape handled by 0362 or 0363.

### `simpa only [golden_mul_eq, golden_pow_eq] using ...`

The local sector lemmas are written with ordinary `(*)` and `(^)` notation, whereas `GoldenUnitFifthClass` uses the project wrappers `goldenMul` and `goldenPow`.

`simpa only` normalizes exactly this representation mismatch and nothing else, keeping the simp dependency narrow and auditable.

## Redundancy and repetition

The most visible repetition is the four successor branches. Each has essentially the shape

```lean
refine ⟨⟨k, by decide⟩, delta, ?_⟩
rw [hx]
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_succ_mul_phiInv delta k
```

for `k = 0,1,2,3`.

This repetition is not purely harmful, however. It has several practical advantages:

- the complete five-sector transition table is visible directly in the proof;
- no modular-subtraction API for `Fin` is required;
- each branch is small and failures are localized;
- the proof structure is easy to audit and suitable for Comparator tasks.

## Optimization candidates

1. **Keep the current proof** — with only five sectors, explicit enumeration is readable and dependency-light.
2. **Factor the four successor cases** — from `i ≠ 0`, one could derive `i = n+1` and apply 0363 once. This would likely introduce more `Fin`/`Nat` conversion machinery.
3. **Generalize to a cyclic action** — define `i ↦ i-1` on `Fin 5` and package sector update into one theorem. The zero case still needs a fifth-power-base correction, so the abstraction is not entirely free.
4. **Strengthen the simp API for wrappers** — making `golden_mul_eq` and `golden_pow_eq` available in a carefully scoped simp set could shorten each branch, at the possible cost of less explicit rewriting.
5. **Unify the `φ` and `φ⁻¹` closure theorems** — one could expose a common signed unit-step API. The current two-theorem interface is also natural because it matches the two reconstruction branches of the descent theorem.

These candidates are not Lean-build verified in this documentation run.

## Required Mathlib imports and import optimization

The standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the generated development as a whole.

For this theorem itself, the direct Mathlib-level needs are primarily facilities for

- `Fin 5`,
- `fin_cases`,
- `decide`,
- existential and pattern destructuring,
- `rw`,
- `simpa`.

The project-local definitions and local sector-transition theorems are additionally required.

Importing all of `Mathlib` is therefore likely broader than necessary for this theorem alone. However, the exact minimal import set for the original `GoldenUnitClassification.lean` module depends on surrounding declarations as well, and cannot be established here without performing a Lean build, which is intentionally not done.

## Comparator challenge suitability

**Suitable.** This is especially useful as a medium-size composition challenge with 0362 and 0363 supplied as available lemmas.

For example, one can replace the body with a hole:

```lean
theorem goldenUnitFifthClass_mul_phiInv {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhiInv) := by
  ?_
```

and provide

```lean
golden_sector_zero_mul_phiInv
golden_sector_succ_mul_phiInv
```

as the local API.

The model must recognize how to

- extract the existential witnesses `i, delta`,
- exhaust `Fin 5`,
- correct the fifth-power base only in the zero sector,
- decrement only the sector index in successor cases,
- bridge project wrapper notation to ordinary ring notation with `simpa only`.

This tests theorem composition and finite classification rather than mere ring normalization, so it is a meaningful step up in difficulty from 0361–0363.

## Next declaration to read

The next declaration is **0365 `goldenUnitFifthClass_one`**, a **`private theorem`**.

```lean
private theorem goldenUnitFifthClass_one : GoldenUnitFifthClass goldenOne := by
  refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
  decide
```

It begins connecting the measure-`1` base cases to concrete fifth-class witnesses by registering

$$
1=\varphi^0\cdot1^5
$$

as the sector-`0` representative.

By 0364, closure under both `φ` and `φ⁻¹` is available; starting with 0365, the development turns to placing the small base units needed by strong induction into the fifth-class predicate.

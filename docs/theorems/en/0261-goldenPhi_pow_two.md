# 0261 — `goldenPhi_pow_two`

## Lean type

```lean
theorem goldenPhi_pow_two :
    goldenPow goldenPhi 2 = ⟨1, 1⟩ := by
  decide
```

This is a `theorem` stating that the square of the golden basis element `goldenPhi` is equal to the concrete coordinate pair `⟨1,1⟩`.

## Mathematical statement

Let the golden basis element be $\varphi$. Its basic quadratic relation is

$$
\varphi^2=\varphi+1.
$$

In the coordinate representation of `GoldenInt`, this becomes

$$
\varphi^2=1+1\varphi=\langle1,1\rangle.
$$

Thus the theorem publishes the concrete identity

$$
goldenPow(\varphi,2)=\langle1,1\rangle
$$

as one entry of the finite unit-representative table.

## Role in the full proof

The small block 0259–0263 fixes the representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

as explicit coordinates for the raw powers `goldenPow goldenPhi i`.

The source lists them in the following order:

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

The present theorem handles the representative `φ²`, namely sector index `2`.

The downstream theorem `golden_unit_two_mul_fifth_snd` uses it explicitly through

```lean
rw [goldenPhi_pow_two]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

and proves

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

Therefore, when analyzing the second coordinate of `φ² * γ⁵`, this theorem is the entry point that replaces the raw unit power by the concrete coordinate pair `⟨1,1⟩`.

Mathematically the statement is tiny, but architecturally it serves as the **canonical rewrite interface for unit sector 2**.

## Direct dependencies

The main direct definitions are:

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

The proof is only `by decide`, so it does not directly invoke any upstream named theorem.

Expanding `goldenPow goldenPhi 2` recursively corresponds conceptually to

$$
\varphi^2
=\varphi\cdot\varphi.
$$

The multiplication law on `GoldenInt` already incorporates the relation $\varphi^2=\varphi+1$, so multiplying `⟨0,1⟩` by itself evaluates to `⟨1,1⟩`.

Declarations 0259 `goldenPhi_pow_zero` and 0260 `goldenPhi_pow_one` are neighboring entries of the same finite representative table, but they are not referenced by name in this proof.

## Proof flow

The entire proof is

```lean
by
  decide
```

The goal is an equality between two closed `GoldenInt` terms, so Lean can evaluate the available `Decidable` instance for the proposition.

Conceptually, the computation proceeds as follows:

1. evaluate `goldenPow goldenPhi 2` at the fixed exponent `2`;
2. use `goldenPhi = ⟨0,1⟩`;
3. evaluate the coordinate multiplication `goldenMul`;
4. obtain `⟨1,1⟩` from the golden quadratic relation built into the multiplication law;
5. reduce structure equality to equality of the integer coordinates, which `decide` closes.

Mathematically, the whole argument is just

$$
\varphi^2=1+\varphi.
$$

## Lean-specific processing

`decide` evaluates the `Decidable` instance of the goal proposition and produces a proof term when the proposition computes to true.

No general ring theorem is applied here. The proof is a closed computation at a fixed exponent and a fixed element.

`GoldenInt` is a structure with integer coordinates, and equality between the concrete terms ultimately reduces to two integer equalities, which are decidable.

The raw power operation `goldenPow` is connected elsewhere to the standard `^` notation, so another design could route the proof through `golden_pow_eq` and the standard power API. For this fixed theorem, however, direct closed computation keeps the dependency depth smaller.

## Redundancy and duplication

Mathematically, the theorem contains exactly the basic relation

$$
\varphi^2=\varphi+1,
$$

which is already encoded in the multiplication law of the golden integers.

Therefore the same result could be obtained locally by unfolding definitions, for example with a proof of the form

```lean
simp [goldenPow, goldenPhi, goldenMul, goldenOne]
```

if that reduction is accepted by the current definitions.

Nevertheless, keeping 0259–0263 as five named representative theorems has clear architectural benefits:

- the correspondence between sector index and concrete coordinates is visible directly in the source;
- downstream proofs can use `rw` without knowing the implementation of `goldenPow`;
- the proof pattern for sectors 0–4 remains symmetric;
- the unit-representative API can remain stable even if the implementation of raw powers changes.

Thus the theorem is logically redundant but useful as an explicit interface theorem.

## Optimization candidates

1. **Keep the current `by decide` proof**
   - it is close to minimal for a closed computation at a fixed exponent.

2. **Compare with explicit `simp` reduction**
   - `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` may expose the computation more clearly.
   - `decide` may nevertheless be more robust against small changes in definition unfolding.

3. **Route through the standard power API**
   - use `golden_pow_eq`, standard `pow_two`, and the quadratic relation for `φ`.
   - this is more algebraic but likely increases dependency depth for this tiny theorem.

4. **Introduce one `Fin 5` representative table**
   - define the coordinate representative for `i : Fin 5` once and derive 0259–0263 as specializations.

5. **Generalize to a Fibonacci coordinate theorem**
   - the coordinates of $\varphi^n$ satisfy the Fibonacci recurrence, so the `n=2` case could be derived from a general theorem.
   - for FLT5, where only the five residue representatives are needed, the current finite table is lighter.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This theorem itself needs very little from Mathlib beyond decidable equality and the basic definitions of `GoldenInt`, `goldenPow`, and `goldenPhi`. It does not directly use `ring`, `omega`, divisibility APIs, or `Fin 5`.

The surrounding `GoldenFifthPowerCoordinates.lean` module is broader: declarations 0255–0258 use `ring`, and later sector arithmetic requires additional algebraic machinery.

No Lean build is run in this museum pass, so the exact minimal import set is not verified. Import reduction is therefore recorded only as an optimization candidate.

## Comparator challenge suitability

The theorem by itself is probably too small for an interesting Comparator challenge, but the full representative block 0259–0263 is well suited to one.

Possible variants are:

- A: the current individual closed computations using `rfl` / `decide`;
- B: explicit `simp` reduction;
- C: proofs through the standard power API;
- D: one `Fin 5` table with specialized corollaries;
- E: a general Fibonacci-coordinate theorem specialized to exponents 0–4.

Useful comparison axes include proof-term size, dependency depth, robustness under definition changes, downstream rewrite usability, symmetry across the five sectors, and generalizability.

For 0261 alone, the current `by decide` proof is already sufficiently concise, so local optimization has low priority.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this theorem follows 0260 `goldenPhi_pow_one` and is followed by 0262 `goldenPhi_pow_three` and 0263 `goldenPhi_pow_four`.

The downstream theorem `golden_unit_two_mul_fifth_snd` directly rewrites with `goldenPhi_pow_two`, confirming its concrete role in the sector-2 coordinate calculation.

The branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0262 `goldenPhi_pow_three`**:

```lean
theorem goldenPhi_pow_three :
    goldenPow goldenPhi 3 = ⟨1, 2⟩ := by
  decide
```

This fixes

$$
\varphi^3
=\varphi(\varphi+1)
=1+2\varphi
$$

as the concrete coordinate pair `⟨1,2⟩` in the unit-representative table and supplies the canonical representative for sector index `3`.

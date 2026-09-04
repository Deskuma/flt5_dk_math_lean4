# 0260 — `goldenPhi_pow_one`

## Lean type

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
```

This is a `theorem` stating that the first power of the golden basis element `goldenPhi` is equal to its defining coordinate pair `⟨0,1⟩`.

## Mathematical statement

Mathematically, the content is simply

$$
\varphi^1=\varphi.
$$

In `GoldenInt`, an element

$$
a+b\varphi
$$

is represented by the coordinate pair `⟨a,b⟩`, and `goldenPhi` itself is defined by

$$
\varphi=0+1\varphi,
$$

namely `⟨0,1⟩`.

Thus the theorem publishes the concrete coordinate identity

$$
goldenPow(\varphi,1)=\langle0,1\rangle
$$

as a named rewrite theorem.

## Role in the full proof

The small block beginning with 0259 fixes the unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

as explicit coordinates of the raw powers `goldenPow goldenPhi i`.

The source lists

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

These five representatives form a finite table used later in the unit-sector arithmetic for expressions of the form

$$
\varphi^i\gamma^5.
$$

The present theorem handles sector index `1`, whose unit representative is `φ`. In the downstream theorem `golden_unit_one_mul_fifth_snd`, the proof begins with

```lean
rw [goldenPhi_pow_one]
```

so that the raw product `φ * γ^5` is reduced to multiplication by the explicit coordinate pair `⟨0,1⟩`. The proof then uses 0257 `goldenPow_five_fst` and 0258 `goldenPow_five_snd` to rewrite the fifth power into explicit coordinate polynomials.

This makes the second coordinate of a fifth-power-up-to-unit representation in the `φ` unit class directly accessible to the later arithmetic sector analysis.

Therefore, although the theorem itself is only the trivial first-power law, its API role is to **fix the canonical representative of unit sector 1 as a stable downstream rewrite target**.

## Direct dependencies

The direct definitions are:

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

The proof is only `by decide`, so it does not directly invoke any upstream named theorem.

By recursion,

$$
goldenPow\;goldenPhi\;1
$$

reduces to one multiplication step involving the zeroth power and `goldenPhi`, and evaluating the concrete coordinates yields `⟨0,1⟩`.

Conceptually,

$$
\varphi^1
=1\cdot\varphi
=\varphi
=\langle0,1\rangle.
$$

## Proof flow

The entire proof is

```lean
by decide
```

Both sides are closed `GoldenInt` terms. Equality on the coordinate structure is decidable, so Lean can evaluate the relevant definitions and decide the equality proposition directly.

No induction, general ring theorem, rewrite chain, or arithmetic tactic is needed. The theorem is a closed computation at the fixed exponent `1`.

## Lean-specific processing

`decide` uses the available `Decidable` instance for the goal proposition and computes a proof when the proposition reduces to `True`.

Here, the equality between the two concrete `GoldenInt` terms ultimately reduces to equality of integer coordinates, which is decidable.

Declaration 0259 `goldenPhi_pow_zero` was proved by `rfl`, whereas 0260 performs one recursive multiplication step before reaching its concrete normal form, so the current source uses `decide`.

Mathematically this is only `φ^1=φ`. A design centered on standard power notation could instead route through the generic `pow_one` theorem. Declaration 0160 `golden_pow_eq` already connects raw `goldenPow` with standard `^`.

## Redundancy and duplication

The mathematical information here is minimal.

- `goldenPhi` is already defined as `⟨0,1⟩`.
- exponent `1` for `goldenPow` can be evaluated directly from the recursive definition;
- standard algebra already provides the generic law `pow_one`.

So the theorem could be omitted and unfolded locally where needed.

However, keeping all five declarations 0259–0263 as a symmetric API is useful:

- downstream proofs can use `rw` without knowing the implementation of `goldenPow`;
- the correspondence between sector index and concrete coordinate representative is visible directly in the source;
- the five downstream sector theorems can follow the same proof pattern;
- the representative-coordinate interface can remain stable if the implementation of `goldenPow` changes.

Thus the declaration is logically redundant but useful as one entry in the finite unit-sector table.

## Optimization candidates

1. **Keep the current individual theorem**
   - `rw [goldenPhi_pow_one]` is explicit and preserves symmetry across the five sectors.

2. **Compare `decide` with `simp`, `norm_num`, or definitional reduction**
   - a proof such as `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` may expose more intent, while `decide` may remain the most robust closed computation.

3. **Derive it through standard `pow_one`**
   - use `golden_pow_eq` to move to standard exponentiation and then apply the generic law.
   - this may increase dependency depth for a theorem that is already computationally trivial.

4. **Introduce a `Fin 5` unit-representative table**
   - define the coordinate representative for `i : Fin 5` once and make 0259–0263 specializations.

5. **Generalize through the Fibonacci recurrence**
   - the coordinates of `φ^n` follow the Fibonacci pattern, so one could prove a general coordinate theorem and derive exponents 0–4 as corollaries.
   - for FLT5, where only the five residue representatives are needed, the current finite table is lighter.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This theorem by itself needs only `decide` together with the basic definitions of `GoldenInt`, `goldenPow`, and `goldenPhi`. It does not directly use `ring`, `omega`, divisibility APIs, or advanced number theory.

The surrounding `GoldenFifthPowerCoordinates.lean` module is broader: 0255–0258 use `ring`, and later declarations use `Fin 5`, `fin_cases`, divisibility, and sector arithmetic. Therefore the minimal imports for the whole module are larger than those required by this single theorem.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

The individual theorem is very small, but the full representative block 0259–0263 is well suited to a Comparator challenge.

Possible variants are:

- A: current individual closed computations (`rfl` / `decide`)
- B: explicit `simp` / `norm_num` reduction
- C: standard power notation with `pow_zero`, `pow_one`, and recursive lemmas
- D: one `Fin 5` table with specialized corollaries
- E: a general Fibonacci-coordinate theorem for `φ^n`

Useful comparison axes include proof-term size, dependency depth, computational transparency, downstream rewrite usability, symmetry across the five sectors, and generalizability.

For 0260 alone, the current `by decide` proof is already sufficiently small, so local optimization has low priority.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this theorem follows 0259 `goldenPhi_pow_zero` and is followed by `goldenPhi_pow_two`, `goldenPhi_pow_three`, and `goldenPhi_pow_four`.

The branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0261 `goldenPhi_pow_two`**:

```lean
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
```

This fixes the defining relation

$$
\varphi^2=\varphi+1
$$

as the concrete coordinate pair `⟨1,1⟩` in the unit-representative table and supplies the canonical representative for sector index `2`.

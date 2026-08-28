# 0259 — `goldenPhi_pow_zero`

## Lean type

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
```

This is a `theorem` stating that the zeroth power of the golden basis element `goldenPhi` is the coordinate pair `⟨1,0⟩`, namely the multiplicative identity of the golden integer ring.

## Mathematical statement

The mathematical content is simply the ordinary zeroth-power law

$$
\varphi^0=1.
$$

An element of `GoldenInt` is represented in coordinates as

$$
a+b\varphi,
$$

so the identity element is

$$
1=1+0\varphi,
$$

which corresponds to the coordinate pair `⟨1,0⟩`.

Thus the theorem merely exposes

$$
goldenPow(\varphi,0)=\langle1,0\rangle.
$$

## Role in the full proof

Declarations 0255–0258 expanded the fifth power of an arbitrary golden integer `gamma = p + qφ` into two explicit coordinate polynomials

$$
A(p,q),\qquad B(p,q).
$$

Declaration 0259 begins a new small block that fixes concrete coordinates for the unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

through the raw powers `goldenPow goldenPhi i`.

The source immediately continues with

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

These five representatives are then used by the unit-sector arithmetic for expressions of the form

$$
\varphi^i\gamma^5.
$$

The present theorem supports the zero sector, where the unit representative is `1 = φ^0`. Later in the source, `golden_unit_zero_mul_fifth_snd` begins with

```lean
rw [goldenPhi_pow_zero]
```

and thereby reduces

$$
1\cdot\gamma^5
$$

to `gamma^5` before applying 0258 `goldenPow_five_snd`.

The same theorem is also used later in zero-sector inversion: after proving that the unit index is `i = 0`, the sector equation is rewritten with `goldenPhi_pow_zero` to recover a pure fifth-power equation.

Therefore the theorem is mathematically trivial but serves as the **named rewrite API for the zero unit representative**.

## Direct dependencies

The direct dependency surface is very small:

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- the definition of `goldenOne`
- the coordinate constructor `⟨_, _⟩`

Because the proof is just `rfl`, it directly depends on no named theorem or tactic.

The raw recursion `goldenPow` returns `goldenOne` at exponent zero, and `goldenOne` is implemented by the coordinates `⟨1,0⟩`. Hence the two sides are definitionally equal.

Conceptually,

$$
goldenPow\;goldenPhi\;0
\equiv goldenOne
\equiv\langle1,0\rangle.
$$

## Proof flow

The complete proof is

```lean
:= rfl
```

Lean reduces `goldenPow goldenPhi 0` by the zero branch of the recursive definition to `goldenOne`, whose implementation is definitionally the same term as the right-hand side `⟨1,0⟩`.

No mathematical inference, induction, rewrite, or arithmetic tactic is required.

## Lean-specific processing

The important point is that the proof uses **definitional equality**, not a constructed propositional argument.

For `rfl` to succeed, elaboration and reduction must make the two sides the same term.

Because the statement uses the raw power API `goldenPow`, its zero branch is directly visible as a definitional equation. In contrast, a statement written with standard Mathlib notation,

```lean
goldenPhi ^ 0 = 1
```

could also be discharged through the generic `pow_zero` / simplification API.

Declaration 0160 `golden_pow_eq` already connects raw `goldenPow` to standard exponentiation. This block nevertheless stays on the raw coordinate layer because it is explicitly tabulating concrete unit representatives.

## Redundancy and duplication

Mathematically, this theorem is little more than the defining equation of `goldenPow` at zero, so it adds almost no logical information.

Since `goldenOne` is already `⟨1,0⟩`, downstream code could also unfold definitions directly with `rfl` or `simp [goldenPow, goldenOne]` instead of naming this theorem.

There are still good API reasons to keep it:

- the theorem name explicitly identifies the representative `φ^0`;
- downstream code can write `rw [goldenPhi_pow_zero]` without knowing the implementation of `goldenPow`;
- it makes the API symmetric with `goldenPhi_pow_one` through `goldenPhi_pow_four`;
- the rewrite surface can remain stable if the internal implementation of `goldenPow` changes.

Thus it is logically redundant but useful as API-level redundancy for the unit-sector block.

## Optimization candidates

1. **Keep the current theorem**
   - preserves the symmetry of the five representative theorems and keeps downstream rewrites readable.

2. **Mark it `@[simp]`**
   - useful if `goldenPow goldenPhi 0` is normalized frequently.
   - this may be redundant if the recursion equation of `goldenPow` is already available to simp, so the actual simp set should be checked by a Lean build.

3. **Package the five powers into a finite table API**
   - define representative coordinates for `i : Fin 5` and derive the five individual theorems as specializations.

4. **Use standard exponentiation as the canonical API**
   - make `goldenPhi ^ i` primary and hide raw `goldenPow` behind 0160 `golden_pow_eq`.

5. **Use `goldenOne` on the right-hand side**
   - `goldenPow goldenPhi 0 = goldenOne` is more abstract.
   - the present explicit pair `⟨1,0⟩` has the advantage that the unit-sector coordinate is immediately visible.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This theorem itself uses no external tactic. In isolation it needs only the core definitions behind `GoldenInt`, `goldenPow`, and `goldenPhi`, so its Mathlib dependency surface is extremely small.

The surrounding `GoldenFifthPowerCoordinates.lean` module is broader: later declarations use `decide`, `ring`, divisibility, `Fin 5`, `fin_cases`, `omega`, and related infrastructure. Therefore module-level minimal imports will necessarily be larger than the requirements of 0259 alone.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

The theorem by itself is too small to make an interesting challenge, but the complete unit-representative block is well suited to comparison.

Possible designs are:

- A: keep `goldenPhi_pow_zero` through `goldenPhi_pow_four` as five individual theorems;
- B: define one `Fin 5` coordinate table and derive the five theorems from it;
- C: derive the coordinates from standard exponentiation and a Fibonacci-style recurrence;
- D: compare `rfl`, `decide`, `norm_num`, and `simp` proof styles across the five exponents.

Useful metrics include API simplicity, proof duplication, downstream rewrite ergonomics, the raw/standard power boundary, and extensibility.

For 0259 alone, `rfl` is already minimal and there is essentially no local proof optimization left.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0258 `goldenPow_five_snd`, followed by `goldenPhi_pow_one`, `goldenPhi_pow_two`, `goldenPhi_pow_three`, and `goldenPhi_pow_four`.

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0260 `goldenPhi_pow_one`**:

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
```

Declaration 0259 fixes the representative `1 = φ^0`. Declaration 0260 fixes the coordinate pair `⟨0,1⟩` for `φ` itself, after which the source proceeds through concrete coordinates for `φ^2`, `φ^3`, and `φ^4` to complete the five unit-sector representatives.
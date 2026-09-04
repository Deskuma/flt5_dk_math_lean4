# 0262 — `goldenPhi_pow_three`

## Lean type

```lean
theorem goldenPhi_pow_three :
    goldenPow goldenPhi 3 = ⟨1, 2⟩ := by
  decide
```

This is a `theorem` stating that the third power of the golden basis element `goldenPhi` is equal to the concrete coordinate pair `⟨1,2⟩`.

## Mathematical statement

Let the golden basis element be $\varphi$. Using the basic quadratic relation

$$
\varphi^2=\varphi+1,
$$

we obtain

$$
\varphi^3
=\varphi(\varphi+1)
=\varphi^2+\varphi
=1+2\varphi.
$$

Thus, in the coordinate representation of `GoldenInt`,

$$
\varphi^3=\langle1,2\rangle.
$$

The theorem therefore publishes the concrete identity

$$
goldenPow(\varphi,3)=\langle1,2\rangle
$$

as the entry of index `3` in the finite unit-representative table.

## Role in the full proof

`GoldenFifthPowerCoordinates.lean` fixes the five representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

as concrete coordinates in order to analyze unit classes modulo fifth powers. In the canonical source, they appear as

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

This theorem is the representative for $\varphi^3$, i.e. sector index `3`.

The downstream theorem `golden_unit_three_mul_fifth_snd` uses it directly through

```lean
rw [goldenPhi_pow_three]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

and obtains the second coordinate

$$
2A(p,q)+3B(p,q),
$$

where

$$
A(p,q)=goldenFifthFstPoly(p,q),
$$

$$
B(p,q)=goldenFifthSndPoly(p,q).
$$

The coefficients `2` and `3` come from the coordinate multiplication rule together with $\varphi^3=1+2\varphi$. If

$$
\gamma^5=A+B\varphi,
$$

then the $\varphi$-coordinate of

$$
(1+2\varphi)(A+B\varphi)
$$

reduces, using $\varphi^2=1+\varphi$, to

$$
2A+3B.
$$

Thus, although this theorem is mathematically a small closed identity, in the proof architecture it is **the rewrite interface that fixes the canonical representative of unit sector 3 as explicit coordinates and connects it to fifth-power coordinate arithmetic**.

## Direct dependencies

The main direct definitions are:

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

The proof itself is only `by decide` and does not invoke the names of the preceding theorems 0259–0261.

Conceptually it evaluates

$$
\varphi^3=\varphi\cdot\varphi^2,
$$

but in Lean the closed term `goldenPow goldenPhi 3` is computed directly and its equality with the concrete structure `⟨1,2⟩` is discharged by decidable computation.

Therefore `goldenPhi_pow_two` is not a logical dependency of this proof term, although 0259–0263 together form one architectural unit-representative table.

## Proof flow

The proof is simply

```lean
by
  decide
```

Conceptually the evaluation is:

1. Recursively evaluate `goldenPow goldenPhi 3` at the fixed exponent `3`.
2. Use the coordinate representation `goldenPhi = ⟨0,1⟩`.
3. Repeatedly evaluate `goldenMul` on concrete coordinates.
4. Normalize through the multiplication rule encoding $\varphi^2=\varphi+1$.
5. The left-hand side computes to `⟨1,2⟩`, and `decide` proves the resulting structure equality.

Mathematically this is just

$$
\varphi^3
=\varphi(\varphi^2)
=\varphi(1+\varphi)
=1+2\varphi.
$$

## Lean-specific processing

`decide` executes the `Decidable` instance of the target proposition and produces a proof term when the proposition evaluates to true.

The target here is a closed equality containing no variables, so this technique is particularly appropriate. No general ring theorem is required; Lean can evaluate the fixed arithmetic directly.

`GoldenInt` is a structure with integer coordinates, so equality of concrete `GoldenInt` values ultimately reduces to equality of their integer coordinates.

By contrast, the later theorem `golden_unit_three_mul_fifth_snd` contains a variable `gamma`, so it cannot be closed by the same finite computation alone. It first rewrites the unit side using the present theorem, then uses `goldenPow_five_fst`, `goldenPow_five_snd`, and `ring` for the symbolic polynomial identity. This cleanly marks the boundary between closed computation and symbolic polynomial proof.

## Redundancy and duplication

Mathematically, the content of this theorem follows immediately from the quadratic golden-ratio relation, and the same structure is already encoded in the definition of `goldenMul`.

A use site could therefore potentially unfold everything directly with something such as

```lean
simp [goldenPow, goldenPhi, goldenMul, goldenOne]
```

instead of relying on a named theorem.

Keeping the named theorem nevertheless has clear architectural advantages:

- the correspondence between unit sector `3` and coordinate `⟨1,2⟩` is explicit in the source;
- downstream proofs only need `rw [goldenPhi_pow_three]` and need not know the recursive implementation of `goldenPow`;
- 0259–0263 form a symmetric API for the five representatives;
- downstream code is insulated from internal changes to `goldenPow`;
- the origin of the coefficients `2,3` in the sector formula is easier to audit.

Thus the theorem is logically redundant but architecturally useful.

## Optimization candidates

1. **Keep the current `by decide` proof**
   - It is close to minimal for a fixed exponent and a fixed element.
   - It also keeps the local dependency surface small.

2. **Compare with explicit `simp` reduction**
   - A proof of the form `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` would make the evaluated definitions more visible.
   - It would, however, depend more strongly on implementation details.

3. **Derive recursively from the preceding representative theorem**
   - One could use `goldenPhi_pow_two` and `goldenMul`, mirroring the mathematical derivation $\varphi^3=\varphi\varphi^2$.
   - This improves explanatory continuity but makes the proof longer than a closed computation.

4. **Bundle the five representatives into a `Fin 5` table**
   - Define the coordinate representative of $\varphi^i$ for `i : Fin 5`, with 0259–0263 as specializations.
   - This may become useful if unit-class routing grows, but for only five entries the current explicit declarations remain clear.

5. **Generalize to Fibonacci coordinates**
   - Powers of $\varphi$ follow the Fibonacci recurrence, conceptually giving

$$
\varphi^n=F_{n-1}+F_n\varphi.
$$

   For `n=3`, $F_2=1$ and $F_3=2$, yielding `⟨1,2⟩`.
   - The FLT5 development only needs five representatives modulo fifth powers, so a general Fibonacci theorem may be unnecessary at this local stage.

## Required Mathlib imports and import optimization

The standalone artifact `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib-side requirements of this theorem alone are small, essentially covering:

- decidable equality and `decide`;
- the basic integer infrastructure used by the coordinates of `GoldenInt`;
- the upstream definitions `goldenPhi`, `goldenPow`, and `goldenMul`.

This theorem itself does not use `ring`, `omega`, gcd, divisibility, or valuation APIs.

However, the surrounding `GoldenFifthPowerCoordinates.lean` module does use `ring` for the fifth-power coordinate expansions and the sector formulas, so the minimum import set of the whole module is broader than that of this theorem in isolation.

No Lean build is performed in this task, so the exact minimal replacement for `import Mathlib` has not been verified. Import reduction is therefore recorded only as an optimization candidate, not as a confirmed change.

## Comparator challenge suitability

This theorem alone is too small to make a substantial Comparator challenge, but the full representative block 0259–0263 is a good candidate.

Possible implementations to compare are:

- A: the current individual `rfl` / `decide` closed computations;
- B: explicit reduction by `simp` over `goldenPow` and `goldenMul`;
- C: recursive derivation from the previous representative theorem;
- D: a general Fibonacci-coordinate theorem followed by specialization.

Useful comparison criteria would include proof-term size, robustness under definition changes, mathematical transparency, dependency depth, and clarity of the connection to the five downstream sector theorems.

In particular, the challenge would test whether promoting a tiny local closed computation into a more general theory is actually an optimization for this development.

## Relation to the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

A concrete PDF page or section corresponding specifically to 0262 `goldenPhi_pow_three` has not been identified in this run. Therefore no PDF location is guessed or cited.

The technical interpretation above is grounded primarily in the canonical repository Lean source, especially the module commentary in `GoldenFifthPowerCoordinates.lean` and the actual dependency from `golden_unit_three_mul_fifth_snd` to `goldenPhi_pow_three`.

## Next declaration to read

The next declaration in source order is

```lean
theorem goldenPhi_pow_four :
    goldenPow goldenPhi 4 = ⟨2, 3⟩ := by
  decide
```

so the next item is **0263 `goldenPhi_pow_four`**.

Mathematically it records

$$
\varphi^4=2+3\varphi
$$

as the concrete coordinate pair `⟨2,3⟩`. This completes the five unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4,
$$

after which the development proceeds to the second-coordinate formulas beginning with `golden_unit_zero_mul_fifth_snd`.
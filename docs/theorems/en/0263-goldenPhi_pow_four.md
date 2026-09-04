# 0263 — `goldenPhi_pow_four`

## Lean type

```lean
theorem goldenPhi_pow_four :
    goldenPow goldenPhi 4 = ⟨2, 3⟩ := by
  decide
```

This is a `theorem`. It states that the fourth power of the golden-integer basis element `goldenPhi` is equal to the explicit coordinate pair `⟨2,3⟩`.

## Mathematical statement

Let the golden-ratio basis element be $\varphi$, with the fundamental relation

$$
\varphi^2=\varphi+1.
$$

Then

$$
\varphi^4
=\varphi\varphi^3
=\varphi(1+2\varphi)
=\varphi+2(1+\varphi)
=2+3\varphi.
$$

Therefore, in the coordinate representation of `GoldenInt`,

$$
\varphi^4=\langle2,3\rangle.
$$

This theorem is the entry of index `4` in the finite unit-representative table, reducing the raw power `goldenPow goldenPhi 4` to the explicit coordinate identity

$$
goldenPow(\varphi,4)=\langle2,3\rangle.
$$

## Role in the overall proof

In the `GoldenFifthPowerCoordinates.lean` portion of the canonical source, the five representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

are fixed as explicit coordinates in order to handle unit classes up to fifth powers.

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

This theorem supplies the final representative, $\varphi^4$, namely sector index `4`, and thereby completes the five-entry representative table.

The module comment explains that, for `gamma=p+q*φ`, the two coordinate polynomials of the fifth power are named first, and the second coordinate after multiplication by each of `1,φ,...,φ^4` is then computed. This turns unit classes modulo fifth powers into five explicit arithmetic sectors. Thus 0259–0263 form the concrete unit-side layer needed for that sector routing.

The downstream theorem `golden_unit_four_mul_fifth_snd` actually uses this theorem as follows:

```lean
rw [goldenPhi_pow_four]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

If `gamma^5=A+B\varphi`, then $\varphi^4=2+3\varphi$ gives

$$
(2+3\varphi)(A+B\varphi),
$$

whose $\varphi$-coordinate is

$$
3A+5B.
$$

The canonical Lean source likewise proves the sector-4 second coordinate as

```lean
3 * goldenFifthFstPoly gamma.fst gamma.snd +
  5 * goldenFifthSndPoly gamma.fst gamma.snd
```

Therefore, although this theorem is mathematically a small closed identity, in the overall proof it is a  **rewrite interface that fixes the canonical representative of unit sector 4 as explicit coordinates, connects it to the arithmetic fifth-power sector analysis, and closes the five-representative table** .

## Directly dependent definitions and lemmas

The main definitions directly involved are:

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

In the canonical source,

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

and natural powers are defined by

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

while golden-integer multiplication is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

The term `x.snd * y.snd` in the second coordinate incorporates the relation $\varphi^2=1+\varphi$ directly into coordinate multiplication.

The proof consists only of `by decide`; it does not invoke the preceding theorem `goldenPhi_pow_three` by name. Mathematically, one may explain the computation through $\varphi^3=1+2\varphi$, but the Lean proof has no logical dependency on that theorem: it closes by definitional computation of the fixed term `goldenPow goldenPhi 4`.

## Proof or construction flow

The proof is only

```lean
by
  decide
```

Conceptually, the computation proceeds as follows.

1. Evaluate `goldenPow goldenPhi 4` recursively at the fixed exponent 4.
2. Use `goldenPhi = ⟨0,1⟩`.
3. Repeat the coordinate multiplication `goldenMul` through the fourth power.
4. At each multiplication, normalize to two coordinates using the relation $\varphi^2=\varphi+1$ built into `goldenMul`.
5. The left-hand side evaluates to the concrete coordinate `⟨2,3⟩`, and `decide` closes the structure equality.

In the mathematical recursive description, from

$$
\varphi^3=1+2\varphi
$$

we obtain

$$
\varphi^4
=\varphi(1+2\varphi)
=2+3\varphi.
$$

## Lean-specific processing

`decide` executes the `Decidable` instance for the target proposition and produces a proof term when the closed proposition evaluates to true.

Because the present goal has no free variables, evaluating it as a closed computation is natural and avoids the need for general ring lemmas. `GoldenInt` is a structure with integer coordinates, so after evaluation the equality reduces to equality of concrete integer coordinates.

The type of `⟨2,3⟩` is inferred as `GoldenInt` from the target, and the numerals `2` and `3` are interpreted as its integer coordinates.

By contrast, the downstream theorem `golden_unit_four_mul_fifth_snd` contains the variable `gamma`, so `decide` alone cannot close it. It first uses this theorem to make the unit side concrete as `⟨2,3⟩`, unfolds `goldenMul`, rewrites the coordinates of the fifth power through 0257 `goldenPow_five_fst` and 0258 `goldenPow_five_snd`, and finally closes the symbolic polynomial identity with `ring`. This is the boundary between closed computation and symbolic arithmetic in this part of the development.

## Redundant or duplicated material

The five theorems 0259–0263 have very similar forms because they enumerate the concrete coordinates of fixed powers $\varphi^k$. Mathematically, all of them follow from the Fibonacci-type recurrence

$$
\varphi^n=F_{n-1}+F_n\varphi,
$$

and the same coordinates could also be recomputed by directly unfolding `goldenPow` and `goldenMul` at each use site.

Nevertheless, keeping separate named theorems has clear architectural advantages.

- The correspondence between sector indices `0` through `4` and concrete coordinates is immediately visible in the source.
- Downstream code needs only `rw [goldenPhi_pow_four]` and does not need to know the recursive implementation of `goldenPow`.
- The five representative theorems correspond one-to-one with the five sector computations and are easy to audit.
- Changes to the implementation of `goldenPow` can be absorbed at the representative-theorem boundary.
- The origin of the sector-4 coefficients `3A+5B` can be traced directly to `⟨2,3⟩`.

Thus the information is mathematically redundant, but the duplication is deliberate and useful in the proof architecture.

## Optimization candidates

1.  **Keep the current `by decide` proof**
   - It is close to minimal for a fixed-element, fixed-exponent closed computation.
   - It also keeps the individual theorem easy to maintain.

2.  **Compare with explicit reduction by `simp`**
   - A proof such as `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` would expose which definitions produce the coordinates.
   - It would, however, depend more strongly on implementation details.

3.  **Derive recursively from `goldenPhi_pow_three`**
   - This can formalize the mathematical explanation $\varphi^4=\varphi\cdot\varphi^3$ directly.
   - The proof becomes longer and gains an additional logical dependency.

4.  **Represent all five cases by one table**
   - One could define a coordinate table indexed by `i : Fin 5` and make 0259–0263 specializations.
   - This becomes attractive if unit-class routing is generalized further, but for only five cases the current named theorems remain quite transparent.

5.  **Generalize to a Fibonacci coordinate formula**
   - The coordinates of $\varphi^n$ can be described for arbitrary $n$ using Fibonacci numbers.
   - The local FLT5 requirement, however, is only the five representatives modulo fifth powers, so importing a general theory into this module may not actually simplify the development.

No Lean build is performed in this task, so the compilability, proof-term sizes, and actual import reductions of these optimization candidates have not been verified.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The functionality directly used by this theorem is small and is mainly within the following scope:

- decidable equality and `decide`
- the integer-coordinate foundations needed by `GoldenInt`
- the upstream definitions `goldenPhi`, `goldenPow`, `goldenMul`, and `goldenOne`

The theorem itself does not use `ring`, `omega`, gcd, divisibility, or valuations. `decide` itself is foundational Lean machinery, so this theorem alone does not imply that the entirety of Mathlib is necessary.

However, the same `GoldenFifthPowerCoordinates.lean` portion uses `ring` for the fifth-power coordinate expansions and symbolic sector proofs, so the imports required at module granularity are broader than those required by this theorem alone.

The original split module file is not present as a standalone file in this repository branch; the canonical source available here is the generated standalone artifact. Therefore the exact fine-grained Mathlib import to which `import Mathlib` could be reduced cannot be confirmed under the present no-build constraint. Import minimization is recorded only as a candidate.

## Comparator challenge suitability

The theorem by itself is low difficulty, but it is suitable as a small Comparator challenge for closed-computation proof strategies. A more meaningful challenge would treat the full representative block 0259–0263 as one unit.

Possible competitors are:

- A: the current individual `rfl` / `decide` closed computations
- B: explicit unfolding of `goldenPow`, `goldenPhi`, and `goldenMul` with `simp`
- C: recursive derivation from the representative theorem for the preceding exponent
- D: a general Fibonacci-coordinate theorem specialized to the five exponents

Useful evaluation axes include proof-term length, robustness under definition changes, mathematical explanatory value, dependency depth, and convenience for downstream rewriting.

Because 0263 is the endpoint of the five-representative table, it is a particularly neat small benchmark for asking whether five local closed computations are preferable to generating the entries from one general theorem.

## Relation to the PDFs

The following PDFs were confirmed again on the target branch during this run:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

A specific PDF page or section corresponding to 0263 `goldenPhi_pow_four` was not identified in this run. Therefore no PDF location or wording is guessed or quoted.

The primary technical grounding is the `GoldenFifthPowerCoordinates.lean` module comment embedded in the repository-canonical `Flt5DkMath/FLT5StandAlone.lean`, the actual declaration `goldenPhi_pow_four`, and its downstream use in `golden_unit_four_mul_fifth_snd`.

## Next declaration to read

Immediately after this theorem in source order is

```lean
/-- Second coordinate after the representative unit `1`. -/
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
```

Therefore the next declaration to read is  **0264 `golden_unit_zero_mul_fifth_snd`** .

By 0263, the explicit coordinates of all five unit representatives are complete. Starting with 0264, the development moves to computing the second coordinate of each representative multiplied by `gamma^5` as an explicit sector polynomial. In the first, zero sector, the unit is `1=\varphi^0`, so the second coordinate is simply `goldenFifthSndPoly` itself.
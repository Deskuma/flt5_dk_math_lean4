# 0264 — `golden_unit_zero_mul_fifth_snd`

## Declaration kind

This declaration is a `theorem`.

## Lean type

```lean
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_zero]
  simp only [goldenMul]
  rw [goldenPow_five_snd]
  ring
```

## Mathematical statement

Write an element of `GoldenInt` as

$$
\gamma=p+q\varphi.
$$

The representative unit of sector zero is

$$
\varphi^0=1,
$$

so

$$
\varphi^0\gamma^5=\gamma^5.
$$

By 0256 `goldenFifthSndPoly` and 0258 `goldenPow_five_snd`, the second coordinate of the fifth power is

$$
B(p,q)
=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right).
$$

Hence this theorem establishes, in Lean's explicit coordinate model,

$$
\operatorname{snd}(\varphi^0\gamma^5)=B(p,q).
$$

Here “sector” does not mean a geometric angular region. It is an algebraic sector determined by the residue class of a unit modulo fifth powers. Sector zero corresponds to the representative $1=\varphi^0$.

## Role in the full proof

Declarations 0259–0263 reduced the five unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

to explicit `GoldenInt` coordinates. Starting with the present theorem, the proof moves from that representative table to the explicit second coordinate obtained after multiplying each representative by `gamma^5`.

Sector zero is the first and simplest case: because its representative is $1$, there is no mixing of the two coordinates, and the second coordinate remains exactly `goldenFifthSndPoly`.

In sectors 1–4, the first-coordinate polynomial `goldenFifthFstPoly` and the second-coordinate polynomial `goldenFifthSndPoly` appear in nontrivial linear combinations.

Thus this theorem is the first bridge connecting

1. explicit unit-class representatives,
2. the fifth-power coordinate polynomials,
3. finite sector arithmetic.

## Direct dependencies

The proof script directly uses the following declarations.

- `goldenPhi_pow_zero`
  - `goldenPow goldenPhi 0 = ⟨1, 0⟩`.
  - It rewrites the sector-zero representative into explicit coordinates.
- `goldenMul`
  - Coordinate multiplication on `GoldenInt`.
  - `simp only [goldenMul]` expands the second coordinate of the product.
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`.
  - It replaces the raw fifth-power second coordinate by the named polynomial.
- `goldenFifthSndPoly`
  - The explicit second-coordinate polynomial of a fifth power.

Indirectly, the statement also depends on the definitions of `GoldenInt`, `goldenPhi`, and `goldenPow`.

## Proof flow

The proof has four short stages.

```lean
rw [goldenPhi_pow_zero]
```

rewrites

```lean
goldenPow goldenPhi 0
```

to `⟨1, 0⟩`.

Next,

```lean
simp only [goldenMul]
```

expands golden multiplication into coordinates. Since the left factor is `⟨1,0⟩`, the second coordinate simplifies to the second coordinate of the right factor `goldenPow gamma 5`.

Then,

```lean
rw [goldenPow_five_snd]
```

rewrites that second coordinate as `goldenFifthSndPoly gamma.fst gamma.snd`.

Finally,

```lean
ring
```

normalizes the remaining integer polynomial identity and closes the goal.

## Lean-specific processing

Mathematically, the content is essentially just $1\cdot\gamma^5=\gamma^5$. In Lean, however, `GoldenInt` is implemented as a direct coordinate model, so the proof unfolds `goldenMul` rather than relying only on an abstract ring multiplication API.

The use of `rw [goldenPhi_pow_zero]` is also deliberate: instead of depending directly on the recursive definition of `goldenPow`, the downstream proof uses the named theorem 0259 as a stable API boundary.

Likewise, `simp only [goldenMul]` intentionally limits the simplifier to the specified definition, reducing dependence on unrelated simp lemmas.

## Redundancy and overlap

The final `ring` is mathematically stronger than what seems necessary. Once `goldenPhi_pow_zero` has been rewritten and `goldenMul` expanded, the second coordinate is essentially the identity map, so a more local simplification may be sufficient.

There is also a repeated proof pattern across the following declarations:

- `golden_unit_one_mul_fifth_snd`
- `golden_unit_two_mul_fifth_snd`
- `golden_unit_three_mul_fifth_snd`
- `golden_unit_four_mul_fifth_snd`

Each follows the same general pattern: rewrite the representative, expand `goldenMul`, rewrite fifth-power coordinates, and finish with `ring`.

Keeping the five public theorems separate is nevertheless useful because each sector formula is immediately visible to downstream readers.

## Optimization candidates

A natural refactoring would introduce one general lemma for a unit representative `⟨a,b⟩` and fifth-power coordinates `A,B`:

$$
\operatorname{snd}((a+b\varphi)(A+B\varphi))=bA+(a+b)B.
$$

Then sectors 0–4 would follow by substituting the explicit representative coordinates. This would eliminate most of the duplicated proof machinery.

A good compromise would be to keep the five sector theorems as the public API while proving them through such a private or internal helper lemma.

For sector zero alone, it may also be possible to replace `ring` by weaker `simp`/`rfl`-style steps. This run does not perform a Lean build, so the exact minimal proof has not been verified.

## Required Mathlib import and import optimization

The verified standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

so the required integer-ring machinery and tactics are available in the repository's checked standalone environment.

The minimal Mathlib import set for this theorem alone has not been established. At least the support needed for integer arithmetic, rewriting/simplification, and the `ring` tactic is required, but identifying the exact smallest import set would require build-based validation. Since no Lean build is performed in this task, no minimal import claim is made.

For import optimization, a sensible approach would be to start from the direct imports of the original `GoldenFifthPowerCoordinates.lean` module together with the Mathlib module providing `ring`, then reduce them under compilation tests.

## Comparator challenge suitability

Yes. The difficulty is low.

A suitable challenge would provide declarations 0255–0259 together with `goldenMul`, and ask the participant to prove

```lean
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

Useful comparison criteria are whether the proof

- uses `goldenPhi_pow_zero` to concretize the representative,
- reuses `goldenPow_five_snd` instead of re-expanding the fifth power,
- avoids unnecessary unfolding and respects the existing API.

This is therefore better suited as a small Lean API/refactoring challenge than as a problem requiring substantial mathematical discovery.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

In this run, the PDF bodies could not be fetched directly in a form that allowed the exact page or section corresponding to declaration 0264 to be identified. No page-level correspondence is therefore asserted or guessed.

## Next declaration to read

The next declaration is `golden_unit_one_mul_fifth_snd`.

```lean
theorem golden_unit_one_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 1) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_one]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

In sector zero the second coordinate $B$ survives unchanged. In sector one, multiplication by the representative $\varphi$ mixes the first and second coordinates, giving

$$
\operatorname{snd}(\varphi\gamma^5)=A+B.
$$

This begins the sequence of sector-specific linear combinations.
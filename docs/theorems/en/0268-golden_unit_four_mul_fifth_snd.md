# 0268 — `golden_unit_four_mul_fifth_snd`

## Declaration kind

This is a `theorem`.

## Lean type

```lean
theorem golden_unit_four_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 4) (goldenPow gamma 5)).snd =
      3 * goldenFifthFstPoly gamma.fst gamma.snd +
        5 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_four]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

As a type, it states that for every `gamma : GoldenInt`, the second coordinate of the product of the sector-4 representative `goldenPow goldenPhi 4` with the fifth power of `gamma` is a specific linear combination of the two fifth-power coordinate polynomials.

## Mathematical statement

Write a `GoldenInt` element as

$$
\gamma=p+q\varphi
$$

and write its fifth power as

$$
\gamma^5=A(p,q)+B(p,q)\varphi.
$$

Here

$$
A(p,q)=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

and

$$
B(p,q)=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right).
$$

By 0263 `goldenPhi_pow_four`, the representative unit of sector 4 is

$$
\varphi^4=2+3\varphi,
$$

which is the `GoldenInt` coordinate pair `⟨2,3⟩`. Therefore

$$
\varphi^4\gamma^5=(2+3\varphi)(A+B\varphi).
$$

Using the golden-ratio relation $\varphi^2=\varphi+1$ gives

$$
(2+3\varphi)(A+B\varphi)
=(2A+3B)+(3A+5B)\varphi.
$$

Hence the second coordinate is

$$
\operatorname{snd}(\varphi^4\gamma^5)=3A(p,q)+5B(p,q).
$$

This theorem fixes that sector-4 coordinate transformation as a statement about Lean's `GoldenInt` multiplication.

## Role in the full proof

Theorems 0264–0268 form the sector-arithmetic table for the second coordinate obtained by multiplying a fifth power by the unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4.
$$

This theorem supplies the final sector, sector 4, completing the table

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B.
$$

The downstream theorem `signedGolden_nonzero_unitSector_false` rewrites directly with this result. The packet data imply that the second coordinate of the product is divisible by $5$, so in sector 4 one obtains

$$
5\mid 3A+5B.
$$

Since $5B$ is visibly a multiple of $5$, subtraction gives

$$
5\mid 3A.
$$

Because $5$ is prime and $5\nmid3$, this yields

$$
5\mid A.
$$

Passing this to `five_dvd_goldenNorm_of_five_dvd_fifthFst` gives

$$
5\mid\operatorname{Norm}(\gamma),
$$

contradicting the packet invariant `five_not_dvd_gamma_norm`.

Thus this theorem not only completes the five-sector coordinate table; it is also a direct input to the modulo-five elimination of sector 4.

## Direct dependencies

The proof script directly uses the following definitions and lemmas.

- `goldenPhi_pow_four`
  - `goldenPow goldenPhi 4 = ⟨2, 3⟩`.
  - Rewrites the sector-4 representative $\varphi^4$ to concrete coordinates.
- `goldenMul`
  - Coordinate multiplication on `GoldenInt`.
  - `simp only [goldenMul]` expands the second coordinate of the product into an integer expression.
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`.
  - Replaces the first coordinate of the fifth power by $A$.
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`.
  - Replaces the second coordinate of the fifth power by $B$.
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - The named polynomials giving the two fifth-power coordinates.

Indirectly, the theorem depends on `GoldenInt`, `goldenPhi`, `goldenPow`, and the relation $\varphi^2=\varphi+1$ encoded by golden-integer multiplication.

## Proof or construction flow

First,

```lean
rw [goldenPhi_pow_four]
```

replaces `goldenPow goldenPhi 4` by `⟨2,3⟩`.

Next,

```lean
simp only [goldenMul]
```

expands golden-integer multiplication into coordinate arithmetic. If the right factor is viewed as `⟨A,B⟩`, multiplication by the left factor `⟨2,3⟩` produces second coordinate $3A+5B$.

Then,

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

replaces the two raw coordinates of `gamma^5` by `goldenFifthFstPoly` and `goldenFifthSndPoly`.

Finally,

```lean
ring
```

normalizes the remaining polynomial identity over the integers and closes the proof.

## Lean-specific handling

Mathematically, the core calculation is only the expansion of $(2+3\varphi)(A+B\varphi)$. In Lean, however, the unit representative, golden-integer multiplication, and fifth-power coordinates are exposed as separate named APIs, so the proof deliberately lowers them one stage at a time to concrete arithmetic.

`simp only [goldenMul]` confines simplification to the expansion of `goldenMul`, avoiding accidental dependence on a broad global simp set. `ring` is used only for the final commutative-ring normalization.

Because the sector-4 second coordinate is $3A+5B$, both the first and second fifth-power coordinates occur, so both `goldenPow_five_fst` and `goldenPow_five_snd` are required by this proof.

## Redundancy and duplication

Theorems 0264–0268 repeat essentially the same proof skeleton.

1. Concretize the unit representative with `goldenPhi_pow_*`.
2. Expand `goldenMul`.
3. Rewrite the fifth-power coordinates with `goldenPow_five_fst` / `goldenPow_five_snd`.
4. Close with `ring`.

This is code duplication. On the other hand, keeping a separate theorem for each sector makes downstream divisibility arguments highly readable, for example through a direct `rw [golden_unit_four_mul_fifth_snd]`.

There is also a small downstream redundancy specific to sector 4. The current sector-4 branch uses `hS : 5 ∣ B` to establish divisibility of $5B$, but $5B$ is divisible by $5$ solely because its coefficient is already $5$. This is not redundancy in the present theorem itself, but it is a possible simplification in the consumer proof.

The final `ring` in this theorem may also be stronger than necessary after expansion, since the residual identity is simple. Whether a weaker normalization closes the exact Lean goal has not been checked because no Lean build is performed in this task.

## Optimization candidates

The most natural refactoring is a generic lemma for the second coordinate of a golden product. For arbitrary golden integers `x=⟨a,b⟩` and `y=⟨A,B⟩`, the second coordinate is

$$
bA+(a+b)B.
$$

Conceptually one could introduce a helper such as

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

and derive all five sector theorems simply by substituting the representative coordinates.

A second possible helper would package `goldenPow_five_fst` and `goldenPow_five_snd` into a single pair equality, allowing both fifth-power coordinates to be rewritten at once. The existing coordinate-specific theorems are still useful when downstream code needs only one coordinate, so such a helper would best complement rather than replace the current public API.

The downstream sector-4 proof could also be simplified so that divisibility of $5B$ does not depend on `hS : 5 ∣ B`. The most concise Mathlib lemma for that rewrite has not been verified here.

## Required Mathlib imports and import-optimization candidates

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` is confirmed to use

```lean
import Mathlib
```

The proof requires integer-ring arithmetic, `rw` / `simp only`, and the `ring` tactic. `GoldenInt`, `goldenMul`, `goldenPow`, `goldenPhi`, and the coordinate theorems are project-local definitions and lemmas, so importing Mathlib alone does not make this theorem standalone.

The minimal Mathlib import set has not been verified. A plausible import optimization would reduce the broad `Mathlib` import to modules supplying integer algebra plus the tactic module supplying `ring`, but the exact minimal import paths require Lean-build verification. Because this task explicitly does not run a Lean build, no minimal import claim is made.

## Comparator challenge suitability

Yes. The difficulty is low to medium.

```lean
theorem golden_unit_four_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 4) (goldenPow gamma 5)).snd =
      3 * goldenFifthFstPoly gamma.fst gamma.snd +
        5 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

can be presented as a goal and candidate proofs compared by how well they reuse the established API. Useful evaluation points are whether a proof concretizes the representative through `goldenPhi_pow_four`, reads the second coordinate of `goldenMul` correctly, and reuses `goldenPow_five_fst` / `goldenPow_five_snd` instead of recomputing the fifth power from definitions.

A stronger follow-up challenge would first ask for a generic `goldenMul_snd_formula` and then derive 0264–0268 as corollaries. That would compare API design and proof reuse, rather than merely competing on a short `ring` proof.

## Correspondence with the PDFs

The target branch is confirmed to contain

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

In this run the GitHub PDF binaries could not be obtained in a form suitable for content analysis. Therefore the exact PDF page or section corresponding to 0268, and any one-to-one match with PDF wording, have not been verified. No such correspondence is guessed. The technical account above is grounded in the canonical Lean source in the repository, together with confirmation that the two PDF artifacts exist.

## Next declaration to read

The next declaration is `golden_neg_unit_mul_fifth_snd`.

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
  rw [neg_mul]
  rfl
```

By 0268, the second-coordinate table for the positive representatives $1,\varphi,\ldots,\varphi^4$ is complete. The next theorem states that negating a representative simply negates the second coordinate of the resulting product, providing the coordinate API needed to absorb and organize unit signs on the fifth-power side.
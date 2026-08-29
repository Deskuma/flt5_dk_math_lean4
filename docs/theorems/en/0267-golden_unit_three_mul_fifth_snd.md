# 0267 — `golden_unit_three_mul_fifth_snd`

## Declaration kind

This is a `theorem`.

## Lean type

```lean
theorem golden_unit_three_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 3) (goldenPow gamma 5)).snd =
      2 * goldenFifthFstPoly gamma.fst gamma.snd +
        3 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_three]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

## Mathematical statement

Write an element of `GoldenInt` as

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

The representative unit of sector 3 is

$$
\varphi^3=1+2\varphi,
$$

that is, the `GoldenInt` coordinate pair `⟨1,2⟩`. Hence

$$
\varphi^3\gamma^5=(1+2\varphi)(A+B\varphi).
$$

Using the golden relation $\varphi^2=\varphi+1$ gives

$$
(1+2\varphi)(A+B\varphi)
=(A+2B)+(2A+3B)\varphi.
$$

Therefore the second coordinate is

$$
\operatorname{snd}(\varphi^3\gamma^5)=2A(p,q)+3B(p,q).
$$

The theorem establishes this sector-3 coordinate transformation in Lean using the concrete coordinate multiplication on `GoldenInt`.

## Role in the full proof

The theorems 0264–0268 form the sector-arithmetic table for multiplying a fifth power by the unit representatives $1,\varphi,\varphi^2,\varphi^3,\varphi^4$. This theorem is the sector-3 entry and provides the linear combination

$$
B \longmapsto 2A+3B.
$$

This formula is used directly later in `signedGolden_nonzero_unitSector_false`. The packet side already gives divisibility of the product's second coordinate by $5$, and `goldenFifthSndPoly` is itself always divisible by $5$. Thus in sector 3,

$$
5\mid 2A+3B,
\qquad
5\mid B
$$

imply

$$
5\mid 2A.
$$

Since $5$ is prime and $5\nmid2$, one obtains

$$
5\mid A.
$$

The theorem `five_dvd_goldenNorm_of_five_dvd_fifthFst` then converts this into $5\mid\operatorname{Norm}(\gamma)$, contradicting the packet invariant that the norm is not divisible by five.

So this theorem is not merely a coordinate computation: it is the arithmetic input that eliminates unit sector 3 modulo five.

## Direct dependencies

The proof script directly uses the following definitions and lemmas.

- `goldenPhi_pow_three`
  - `goldenPow goldenPhi 3 = ⟨1, 2⟩`.
  - Rewrites the sector-3 representative $\varphi^3$ to concrete coordinates.
- `goldenMul`
  - Coordinate multiplication on `GoldenInt`.
  - `simp only [goldenMul]` expands the second coordinate of the product.
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`.
  - Replaces the first fifth-power coordinate by the named polynomial $A$.
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`.
  - Replaces the second fifth-power coordinate by the named polynomial $B$.
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - The two coordinate polynomials for the fifth power.

Indirectly, the theorem depends on `GoldenInt`, `goldenPhi`, `goldenPow`, and on the golden-integer multiplication implementation incorporating $\varphi^2=\varphi+1$.

## Proof flow

First,

```lean
rw [goldenPhi_pow_three]
```

replaces `goldenPow goldenPhi 3` by `⟨1,2⟩`.

Next,

```lean
simp only [goldenMul]
```

expands golden multiplication into coordinate arithmetic. If the right factor is viewed as `⟨A,B⟩`, multiplication by the left factor `⟨1,2⟩` yields second coordinate $2A+3B$.

Then,

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

rewrites the two raw fifth-power coordinates as `goldenFifthFstPoly` and `goldenFifthSndPoly`.

Finally,

```lean
ring
```

normalizes the remaining polynomial identity over the integers and closes the proof.

## Lean-specific processing

Mathematically this is only the expansion of $(1+2\varphi)(A+B\varphi)`. In Lean, because `GoldenInt` is represented by explicit coordinates, the representative is first rewritten to a concrete pair, `goldenMul` is unfolded, and only then are the two named fifth-power coordinate theorems applied.

In sector 3, the original first coordinate $A$ flows into the resulting second coordinate with coefficient 2, so both `goldenPow_five_fst` and `goldenPow_five_snd` are needed.

The use of `simp only [goldenMul]` deliberately localizes simplification and avoids accidental dependence on a broad simp set. The final `ring` is used only for ring normalization.

## Redundancy and duplication

The sector theorems 0264–0268 repeat essentially the same proof pattern.

1. Rewrite the representative with `goldenPhi_pow_*`.
2. Expand `goldenMul`.
3. Rewrite fifth-power coordinates with `goldenPow_five_fst` / `goldenPow_five_snd`.
4. Close with `ring`.

This is implementation-level duplication. On the other hand, keeping explicit right-hand sides

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

as separate theorems is valuable for downstream rewriting and divisibility proofs.

For this theorem alone, `ring` may be stronger than strictly necessary because the post-expansion statement is essentially linear. A more restricted simplification may suffice, but this was not checked because no Lean build is run in this task.

## Optimization candidates

The most natural optimization is to introduce a general lemma for the second coordinate of a product. For coordinates `x=⟨a,b⟩` and `y=⟨A,B⟩`, the second coordinate is

$$
bA+(a+b)B.
$$

Conceptually, one could provide an API such as

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

Then sectors 0 through 4 would follow by substituting the representative coordinates.

A second possible optimization would package `goldenPow_five_fst` and `goldenPow_five_snd` into a pair equality so both rewrites can be handled through one API. The current coordinate-wise API remains useful when a downstream proof needs only one coordinate.

A good compromise is therefore to generalize the internal helper while keeping the explicit sector theorems as public rewrite lemmas.

## Required Mathlib imports and import optimization

The confirmed standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The proof needs integer-ring operations, rewriting/simplification, and the `ring` tactic. At the same time, `GoldenInt`, `goldenMul`, and `goldenPow` are project-side definitions, so Mathlib imports alone are not sufficient to make this theorem standalone.

The minimal Mathlib import set for this theorem has not been established. The standalone artifact merges many generated source modules, so the minimal import graph of the original individual module cannot be inferred from this check alone. Import minimization would need to reduce dependencies step by step to modules supplying integer algebra and `ring`, validating each step with a Lean build. No Lean build is performed in this task, so no minimal-import claim is made.

## Comparator challenge suitability

Yes. The difficulty is low to medium.

```lean
theorem golden_unit_three_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 3) (goldenPow gamma 5)).snd =
      2 * goldenFifthFstPoly gamma.fst gamma.snd +
        3 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

Useful scoring points are whether the proof rewrites the sector-3 representative to `⟨1,2⟩`, reuses the existing coordinate theorems instead of unfolding the fifth power from scratch, and correctly extracts $2A+3B$ from the definition of `goldenMul`.

A stronger challenge can include the downstream arithmetic step actually used after this theorem:

$$
5\mid2A+3B,\quad 5\mid B \Longrightarrow 5\mid A.
$$

That version tests both coordinate arithmetic and prime divisibility.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub connector confirmed the files and their metadata, but the PDF bodies were not analyzed in this run. Therefore the concrete page or section corresponding to 0267, and any one-to-one wording correspondence with the PDFs, have not been verified. No such details are inferred.

## Next declaration to read

The next declaration is `golden_unit_four_mul_fifth_snd`.

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

The sector-4 representative is $\varphi^4=2+3\varphi$, namely `⟨2,3⟩`, so the second coordinate becomes

$$
3A+5B.
$$

This completes the second-coordinate table for unit representatives 0 through 4.
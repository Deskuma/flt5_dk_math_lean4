# 0266 — `golden_unit_two_mul_fifth_snd`

## Declaration kind

This is a `theorem`.

## Lean type

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_two]
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

The representative unit of sector 2 is

$$
\varphi^2=1+\varphi,
$$

that is, the `GoldenInt` coordinate pair `⟨1,1⟩`. Hence

$$
\varphi^2\gamma^5=(1+\varphi)(A+B\varphi).
$$

Using the golden relation $\varphi^2=\varphi+1$ and collecting coordinates gives

$$
(1+\varphi)(A+B\varphi)
=(A+B)+(A+2B)\varphi.
$$

Therefore the second coordinate is

$$
\operatorname{snd}(\varphi^2\gamma^5)=A(p,q)+2B(p,q).
$$

The theorem establishes this sector-2 coordinate transformation in Lean using the concrete coordinate multiplication on `GoldenInt`.

## Role in the full proof

The theorems 0264–0268 form the sector-arithmetic table for multiplying a fifth power by the unit representatives $1,\varphi,\varphi^2,\varphi^3,\varphi^4$. This theorem is the sector-2 entry and provides the linear transformation

$$
B \longmapsto A+2B.
$$

Because `goldenFifthSndPoly` visibly contains a factor of $5$, downstream unit-sector elimination can combine $5\mid A+2B$ from the packet side with the already known $5\mid B$ to extract $5\mid A$. Thus this theorem is one of the bridges turning unit-class information into arithmetic modulo five.

Sector 1 produced $A+B`; here the coefficient becomes $A+2B`. This is exactly what results when the representative coordinate `⟨1,1⟩` acts through the second-coordinate formula encoded by `goldenMul`.

## Direct dependencies

The proof script directly uses the following definitions and lemmas.

- `goldenPhi_pow_two`
  - `goldenPow goldenPhi 2 = ⟨1, 1⟩`.
  - Rewrites the sector-2 representative $\varphi^2$ to concrete coordinates.
- `goldenMul`
  - Coordinate multiplication on `GoldenInt`.
  - `simp only [goldenMul]` expands the second coordinate of the product.
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`.
  - Replaces the first raw fifth-power coordinate by the named polynomial $A$.
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`.
  - Replaces the second raw fifth-power coordinate by the named polynomial $B$.
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - The two coordinate polynomials for the fifth power.

Indirectly, the theorem depends on `GoldenInt`, `goldenPhi`, `goldenPow`, and on the implementation of golden multiplication incorporating the relation $\varphi^2=\varphi+1$.

## Proof flow

First,

```lean
rw [goldenPhi_pow_two]
```

replaces `goldenPow goldenPhi 2` by `⟨1,1⟩`.

Next,

```lean
simp only [goldenMul]
```

expands golden multiplication into coordinate arithmetic. If the right factor is regarded as `⟨A,B⟩`, multiplication by the left factor `⟨1,1⟩` yields second coordinate $A+2B$.

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

Mathematically this is a single expansion of $(1+\varphi)(A+B\varphi)$. In Lean, because `GoldenInt` is represented by explicit coordinates, the representative is first rewritten to a concrete pair, `goldenMul` is unfolded, and only then are the named fifth-power coordinate theorems applied.

Both `goldenPow_five_fst` and `goldenPow_five_snd` are needed because multiplication by the unit causes the original first coordinate to flow into the resulting second coordinate.

The use of `simp only [goldenMul]` deliberately restricts the simplifier, avoiding accidental dependence on a broad simp set. The final `ring` is used only for algebraic normalization.

## Redundancy and duplication

The sector theorems 0264–0268 share almost the same proof pattern.

1. Rewrite the representative with `goldenPhi_pow_*`.
2. Expand `goldenMul`.
3. Rewrite fifth-power coordinates with `goldenPow_five_fst` / `goldenPow_five_snd`.
4. Close with `ring`.

This is implementation-level duplication. On the other hand, keeping the explicit right-hand sides

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

is valuable for downstream readability and rewriting, so there is little reason to remove the public theorems themselves.

For this theorem alone, `ring` may be stronger than strictly necessary because the post-expansion statement is essentially linear. `ring_nf` or additional simplification may suffice, but this was not checked because no Lean build was run in this task.

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

Then the sector-0 through sector-4 results would follow merely by substituting the representative coordinates.

A second possible optimization would package the first and second fifth-power coordinate theorems into a pair equality, allowing both rewrites to be performed through a single API. The present split form remains useful, however, when downstream proofs need only one coordinate.

A good compromise is therefore to generalize the internal helper while keeping the explicit sector theorems as public rewrite lemmas.

## Required Mathlib imports and import optimization

The confirmed standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The proof needs integer-ring operations, rewriting/simplification, and the `ring` tactic. At the same time, `GoldenInt`, `goldenMul`, and `goldenPow` are project-side definitions, so Mathlib imports alone are not sufficient to make this theorem standalone.

The minimal Mathlib import set for this theorem has not been established. Because the original generated modules are merged into the standalone artifact in this repository, the direct import graph of the source module could not be confirmed here. Import minimization would need to shrink the imports step by step to the modules providing integer algebra and `ring`, with Lean builds at each step. No Lean build is performed in this task, so no minimal import claim is made.

## Comparator challenge suitability

Yes. The difficulty is low to medium. It is structurally close to 0265, but the coefficient 2 makes it a useful test of whether the solver understands how the representative coordinates determine the resulting second coordinate.

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

Useful scoring points are whether the proof rewrites the sector-2 representative to `⟨1,1⟩`, reuses both existing fifth-power coordinate APIs instead of fully expanding `goldenPow`, and correctly obtains the coefficient pattern $A+2B$ from `goldenMul`.

A stronger challenge can first ask for the general second-coordinate formula $bA+(a+b)B$ and then require this theorem as a corollary.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub connector could confirm their presence but could not retrieve their binary text content, and an external fetch also failed. Therefore the concrete PDF page or section corresponding to 0266 could not be verified. No claim about the PDF location or wording is made by inference.

## Next declaration to read

The next declaration is `golden_unit_three_mul_fifth_snd`.

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

The sector-3 representative is $\varphi^3=1+2\varphi$, namely `⟨1,2⟩`, so the second coordinate becomes

$$
2A+3B.
$$

This continues the Fibonacci-type coefficient progression seen from sector 2 onward.
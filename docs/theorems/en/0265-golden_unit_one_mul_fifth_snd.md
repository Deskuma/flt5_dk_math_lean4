# 0265 — `golden_unit_one_mul_fifth_snd`

## Declaration kind

This declaration is a `theorem`.

## Lean type

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

The representative unit of sector 1 is

$$
\varphi^1=\varphi.
$$

Using the golden relation

$$
\varphi^2=\varphi+1,
$$

we obtain

$$
\varphi(A+B\varphi)
=A\varphi+B\varphi^2
=B+(A+B)\varphi.
$$

Therefore the second coordinate is

$$
\operatorname{snd}(\varphi\gamma^5)=A(p,q)+B(p,q).
$$

This theorem establishes that identity in Lean using the concrete coordinate multiplication on `GoldenInt`.

The word “sector” here is algebraic rather than geometric: it refers to a unit class modulo fifth powers. Sector 1 is represented by $\varphi$.

## Role in the whole proof

In 0264 `golden_unit_zero_mul_fifth_snd`, the representative unit is $1$, so the second coordinate $B$ of the fifth power is unchanged. This theorem is the first point where the first coordinate $A$ and second coordinate $B$ mix, producing the sector-specific linear combination

$$
B \longmapsto A+B.
$$

That form is important in the later elimination of nonzero unit sectors. Since `goldenFifthSndPoly` is always divisible by $5$, if the packet side also implies that the sector-1 second coordinate $A+B$ is divisible by $5$, subtracting the known $5$-divisible term gives

$$
5\mid A.
$$

The later argument then converts divisibility of the first fifth-power coordinate into divisibility of `goldenNorm gamma`, contradicting the packet invariant.

The repository source uses this theorem directly in the sector-1 branch of `signedGolden_nonzero_unitSector_false`:

```lean
rw [hbeta, golden_unit_one_mul_fifth_snd] at hb
have h := dvd_sub hb hS
ring_nf at h
exact h
```

Thus the theorem is not merely a coordinate calculation. It is the bridge that turns a unit-class representative into an explicit modulo-five arithmetic condition.

## Direct dependencies

The proof script directly uses the following declarations.

- `goldenPhi_pow_one`
  - `goldenPow goldenPhi 1 = ⟨0, 1⟩`.
  - Rewrites the sector-1 representative $\varphi$ into concrete coordinates.
- `goldenMul`
  - Coordinate multiplication on `GoldenInt`.
  - `simp only [goldenMul]` expands the second coordinate of the product.
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`.
  - Replaces the raw first coordinate of the fifth power with the named polynomial $A$.
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`.
  - Replaces the raw second coordinate with the named polynomial $B$.
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - The two coordinate polynomials of the fifth power.

Indirectly, the theorem depends on the definitions of `GoldenInt`, `goldenPhi`, and `goldenPow`, and on the relation $\varphi^2=\varphi+1$ encoded by the implementation of `goldenMul`.

## Proof flow

The proof has four stages.

First,

```lean
rw [goldenPhi_pow_one]
```

replaces

```lean
goldenPow goldenPhi 1
```

with the concrete coordinate pair `⟨0, 1⟩`.

Next,

```lean
simp only [goldenMul]
```

expands multiplication in coordinates. If the right factor is viewed as `⟨A,B⟩`, the second coordinate of multiplication by `⟨0,1⟩` becomes $A+B$.

Then,

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

rewrites the two raw coordinates of the fifth power as `goldenFifthFstPoly` and `goldenFifthSndPoly`.

Finally,

```lean
ring
```

normalizes the remaining polynomial identity over the integers.

## Lean-specific processing

Mathematically the content is the one-line calculation $\varphi(A+B\varphi)=B+(A+B)\varphi$. In Lean, however, `GoldenInt` is represented concretely by coordinates, so the proof first turns the unit representative into a concrete pair, unfolds coordinate multiplication, and then rewrites the fifth-power coordinates through named API theorems.

The use of both `goldenPow_five_fst` and `goldenPow_five_snd` is the main difference from 0264. Sector 0 only needs the second coordinate. In sector 1, multiplication by the unit makes the first coordinate flow into the resulting second coordinate, so both coordinate theorems are required.

The proof also uses `simp only [goldenMul]`, which deliberately limits the simplifier and reduces accidental dependence on unrelated simp lemmas. The final `ring` call handles polynomial normalization over `ℤ`.

## Redundancy and duplication

The sector theorems 0264–0268 all share the same proof pattern:

1. rewrite the relevant `goldenPhi_pow_*` representative;
2. expand `goldenMul`;
3. rewrite fifth-power coordinates using `goldenPow_five_fst` and/or `goldenPow_five_snd`;
4. close with `ring`.

There is therefore implementation-level duplication. On the other hand, exposing the final sector formulas

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

as separate named theorems is valuable for downstream readability, so there is little reason to remove the public declarations themselves.

For this theorem alone, `ring` may be stronger than necessary. After coordinate expansion the remaining statement is nearly linear, and a weaker `simp` or `ring_nf` proof may work. No Lean build is performed in this task, so the smallest tactic sequence has not been verified.

## Optimization candidates

The most natural refactoring is to add a general lemma giving the second coordinate of multiplication of two golden integers. For coordinates `⟨a,b⟩` and `⟨A,B⟩`, the formula is

$$
bA+(a+b)B.
$$

Conceptually one could expose an API such as

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

Then sectors 0–4 would reduce mostly to substituting the representative coordinates.

A second possible refactoring would bundle `goldenPow_five_fst` and `goldenPow_five_snd` into a pair equality for the two fifth-power coordinates. This would allow both coordinates to be rewritten through one API. The present split form remains useful when downstream proofs need only one coordinate.

A good compromise would therefore be to add a general internal helper while preserving the explicit sector theorems as the public API.

## Required Mathlib imports and import optimization

The checked standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

so the required integer-ring machinery and tactics are available in the repository artifact.

This proof at least needs rewriting/simplification, the `ring` tactic, and integer-ring operations. The project-specific declarations `GoldenInt`, `goldenMul`, and `goldenPow` must of course come from the project module dependency chain as well.

The minimal Mathlib import set for this theorem alone has not been established. A sensible import-minimization experiment would keep the direct project dependency of `GoldenFifthPowerCoordinates.lean` and reduce the Mathlib side gradually to the modules providing integer algebra and `ring`, checking each step with Lean. Since this task explicitly does not run a Lean build, no particular minimal import set is claimed here.

## Comparator challenge suitability

Yes. The difficulty is low to medium and slightly better than 0264 as a challenge.

A useful challenge would provide `goldenPhi_pow_one`, `goldenPow_five_fst`, `goldenPow_five_snd`, and `goldenMul`, then ask for

```lean
theorem golden_unit_one_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 1) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

The challenge can test whether the solver

- concretizes the sector representative using the existing theorem;
- recognizes that both first and second fifth-power coordinates are needed;
- reuses the named coordinate API instead of unfolding all of `goldenPow`;
- finishes the residual algebra with ring normalization.

A stronger version could first ask for the general second-coordinate transformation $bA+(a+b)B$ and then derive this theorem as a corollary.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The GitHub connector available in this run cannot retrieve the binary PDF body as text, so the precise PDF page or section corresponding to 0265 could not be verified. No page-level correspondence is inferred here.

## Next declaration to read

The next declaration is `golden_unit_two_mul_fifth_snd`.

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

The representative of sector 2 is $\varphi^2=1+\varphi$, namely the coordinate pair `⟨1,1⟩`. Multiplying the fifth-power pair `⟨A,B⟩` by this representative gives second coordinate

$$
A+2B.
$$

After sector 1's $A+B$, the Fibonacci-type coordinates of the unit representatives begin to appear directly as the coefficients in these second-coordinate formulas.
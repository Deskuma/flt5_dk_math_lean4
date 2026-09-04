# 0289 — `goldenFifthSndFactor_nonneg`

## Declaration kind

This is a **`theorem`**.

It proves that the quartic factor `goldenFifthSndFactor r s`, which appears in the second coordinate of a fifth power in the golden integers, is always nonnegative for arbitrary integers `r,s`.

## Lean type

```lean
/-- The quartic second-coordinate factor is nonnegative for all integer inputs. -/
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  have hdiag : 0 ≤
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
    positivity
  have hident := sixteen_mul_goldenFifthSndFactor_eq r s
  nlinarith
```

Mathematically, if

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s),
$$

then the theorem states that for all $r,s\in\mathbb Z$,

$$
H(r,s)\ge 0.
$$

The definition in the repository source is

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

From this expression alone, nonnegativity is not termwise obvious because the mixed terms $2r^3s$ and $3rs^3$ may change sign. The theorem therefore uses the immediately preceding 0288 `sixteen_mul_goldenFifthSndFactor_eq`, which gives

$$
16H(r,s)=X^4+10X^2s^2+5s^4,
\qquad X=2r+s.
$$

Every term on the right-hand side is nonnegative, so the left-hand side is nonnegative; since $16>0$, it follows that $H(r,s)\ge 0$.

## Mathematical meaning

The essential content of this theorem is that the sign-obscure quartic is converted, through the diagonalization identity from 0288, into an **explicitly nonnegative representation**.

Indeed,

$$
X^4\ge 0,
\qquad
10X^2s^2\ge 0,
\qquad
5s^4\ge 0,
$$

hence

$$
X^4+10X^2s^2+5s^4\ge 0.
$$

Therefore

$$
16H(r,s)\ge 0,
$$

and because $16>0$,

$$
H(r,s)\ge 0.
$$

This is more than a computational lemma. In the later zero-sector inversion, it removes sign ambiguity from `goldenFifthSndFactor` when absolute values and tenth-power information are used.

## Role in the overall proof

The zero-sector arithmetic layer has already produced a tenth-power split, while the inversion layer introduces

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W,
\qquad
Q=5^5c^8.
$$

The preceding theorem 0288 rewrites the original quartic factor $H(r,s)$ in the new coordinate $X$ as

$$
16H=X^4+10X^2s^2+5s^4.
$$

The present theorem 0289 is the first step that turns this algebraic identity into **order-theoretic information**.

The logical flow is therefore

$$
\text{quartic identity}
\longrightarrow
\text{sum of nonnegative terms}
\longrightarrow
H(r,s)\ge 0.
$$

This nonnegativity prepares the proof for later uses of information such as `|H(r,s)| = d^10`, where one may need to remove an absolute value and pass to `H(r,s) = d^10`. This theorem alone does not state that later absolute-value elimination; it only establishes the sign control needed for it.

## Direct dependencies

### `goldenFifthSndFactor`

This is the quartic under study.

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

Its original meaning is the factor $H(r,s)$ appearing in the second coordinate of $(r+s\varphi)^5$.

### `zeroSectorX`

The diagonal coordinate introduced in 0282:

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

### `sixteen_mul_goldenFifthSndFactor_eq`

The immediately preceding theorem 0288:

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorX
  ring
```

It already provides the mathematical core as an exact algebraic identity.

### `positivity`

A Mathlib tactic that automatically proves the nonnegativity of the diagonalized right-hand side from even powers and nonnegative coefficients.

### `nlinarith`

A Mathlib tactic that combines `hdiag` and `hident` and closes the final nonlinear arithmetic goal `0 ≤ goldenFifthSndFactor r s`.

## Proof flow

The proof has three stages.

### 1. Prove nonnegativity of the diagonalized right-hand side

```lean
have hdiag : 0 ≤
    zeroSectorX r s ^ 4 +
      10 * zeroSectorX r s ^ 2 * s ^ 2 +
      5 * s ^ 4 := by
  positivity
```

`positivity` recognizes the even powers and nonnegative coefficients and proves that the entire expression is nonnegative.

### 2. Obtain the identity from 0288

```lean
have hident := sixteen_mul_goldenFifthSndFactor_eq r s
```

This introduces

$$
16H(r,s)=X^4+10X^2s^2+5s^4
$$

as a local equality.

### 3. Finish by nonlinear arithmetic

```lean
nlinarith
```

Combining `hdiag` and `hident` yields

$$
16H(r,s)\ge 0.
$$

Since the coefficient $16$ is positive, `nlinarith` derives

$$
H(r,s)\ge 0.
$$

## Lean-specific processing

A notable feature is that this theorem does not unfold `goldenFifthSndFactor` directly.

In 0288 the proof used

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

to establish a pure polynomial identity. The present theorem reuses that result and delegates only the sign reasoning to `positivity` and `nlinarith`.

Thus the responsibilities are cleanly separated:

- algebraic normalization in 0288;
- order reasoning in 0289.

Because the theorem lives entirely in `ℤ`, there is no `Nat`/`Int` coercion management, `natAbs`, divisibility API, or coprimality API here.

The line

```lean
have hident := sixteen_mul_goldenFifthSndFactor_eq r s
```

also relies on Lean's elaborator to infer the specialized equality type without an explicit type annotation.

## Redundancy and duplication

The proof body is short and contains essentially no serious redundancy.

In principle, one could rewrite with 0288 and then prove a nonnegative multiple first, followed by an explicit order argument that divides out the positive constant 16. That would expose more intermediate mathematics.

The current proof,

```lean
positivity
have hident := ...
nlinarith
```

has a clear division of labor and remains easy to audit.

`nlinarith` is stronger than strictly necessary for this small conclusion, but it efficiently combines the polynomial equality and inequality, so its use is proportionate to the code saved.

## Optimization candidates

### 1. Reduce reliance on `nlinarith`

It would be possible to use narrower order lemmas: first derive `0 ≤ 16 * H`, then explicitly conclude `0 ≤ H` from positivity of 16. This may expose the mathematical argument more transparently.

On the other hand, the present `nlinarith` proof is compact and robust, so there is no strong implementation reason to replace it.

### 2. Package stronger positivity information

Because 0288 already provides the exact identity, there is little need to introduce another lemma merely restating the sum-of-nonnegative-terms form.

If later developments repeatedly need equality conditions, a stronger result such as

$$
H(r,s)=0 \iff r=0\land s=0
$$

could be useful as a positive-definiteness lemma. This is only a mathematical optimization candidate; it is not asserted here as an existing theorem in the repository.

### 3. Explicitly type `hident`

For teaching material one could write

```lean
have hident :
    16 * goldenFifthSndFactor r s = ... :=
  sixteen_mul_goldenFifthSndFactor_eq r s
```

so that the intermediate statement is visible in the proof script. For implementation, however, the current inferred form is more concise.

## Required Mathlib imports and import optimization candidates

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main facilities directly needed by this theorem are:

- the ordered commutative ring structure on integers;
- natural-number powers;
- the `positivity` tactic;
- the `nlinarith` tactic;
- the dependency definitions `goldenFifthSndFactor` and `zeroSectorX`;
- theorem 0288 `sixteen_mul_goldenFifthSndFactor_eq`.

Therefore `import Mathlib` is likely broader than necessary for this theorem in isolation. However, this task does not run a Lean build, so the actual minimal import set of the source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` is **not verified**. No specific import reduction is claimed without verification.

## Comparator challenge suitability

**Suitable.**

Compared with 0288, this adds one small layer of reasoning:

1. recognize nonnegativity from even powers;
2. use an existing exact identity;
3. return from a positive constant multiple to the original factor.

A suitable challenge would provide 0288 and ask the solver to complete

```lean
theorem challenge (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  ...
```

The current `positivity` + `nlinarith` solution can then be compared with a proof using explicit order lemmas, making it useful Comparator material.

Verdict: **suitable**.

## Correspondence with the PDFs

The repository tree on the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the normal GitHub connector text path cannot decode the PDF binaries into analyzable text, and the direct PDF retrieval attempted in this run did not succeed. Therefore the exact PDF page, section, and wording corresponding to this theorem are **not verified**.

No PDF location is guessed here; the repository's Lean source and existing theorem museum are used as the canonical evidence.

## Next declaration to read

The next declaration is 0290 `GoldenZeroSectorCandidate`, whose kind is **`structure`**.

In the canonical source it appears immediately after 0289 and packages the raw hypotheses supplied by the zero-sector arithmetic receiver together with the chosen tenth-power split.

Its beginning is:

```lean
structure GoldenZeroSectorCandidate where
  r : ℤ
  s : ℤ
  ...
```

Declarations 0282–0289 prepare generic inversion coordinates, identities, and sign information. Declaration 0290 then begins the data-bearing part of the inversion by collecting the actual zero-sector candidate into one structure whose fields can be used by subsequent factorization proofs.

Thus, in dependency order, 0289 establishes sign control of the quartic factor, and 0290 fixes the input data structure for the inversion stage.
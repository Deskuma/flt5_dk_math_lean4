# 0093 — `GoldenNorm`

## Lean type

```lean
def GoldenNorm (m n : ℤ) : ℤ :=
  m ^ 2 + m * n - n ^ 2
```

This declaration is the first definition in `DkMath/FLT/Five/SquareGoldenBridge.lean`. It opens a new algebraic bridge immediately after 0092 closes the five-adic exact power-split layer.

The type is simple: it takes two integer coordinates `m n : ℤ` and returns an integer.

## Mathematical statement

`GoldenNorm` introduces the named binary quadratic form

$$
N(m,n)=m^2+mn-n^2.
$$

When the golden ratio $\varphi$ satisfies

$$
\varphi^2=\varphi+1,
$$

this is the norm form appearing in the conjugate product of a formal element $m+n\varphi$,

$$
(m+n\varphi)(m+n\varphi').
$$

Here $\varphi'$ is the other root, with

$$
\varphi+\varphi'=1,\qquad \varphi\varphi'=-1,
$$

so expansion gives

$$
m^2+mn-n^2.
$$

However, this definition itself does not introduce a number field, algebraic integers, or a conjugation map. The source comment explicitly says that the form is "later realized as the norm", so at this stage it is most accurate to treat it as a pure integral quadratic form.

## Role in the full proof

Up to 0092, the Branch-B route normalizes an FLT5 candidate five-adically and builds the layer that yields an exact fifth-power split.

Starting with 0093, the viewpoint changes. `SquareGoldenBridge.lean` rewrites `GN5` in endpoint-square coordinates and then identifies the resulting expression with a golden-ratio quadratic form.

The module comment uses the coordinates

$$
m=(g+y)^2+y^2,
$$

$$
n=(g+y)y,
$$

and aims to read `GN5 g y` as

$$
N(m,n)=m^2+mn-n^2.
$$

Thus `GoldenNorm` is the named target into which the fifth cyclotomic factor `GN5`, previously handled over natural numbers, is transported before the later golden-order arithmetic begins.

At the proof-graph level, the new chapter has the schematic form

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross coordinates}
\longrightarrow
\mathrm{GoldenNorm}
\longrightarrow
\text{discriminant-5 form}
\longrightarrow
\text{golden arithmetic}.
$$

## Direct dependencies

The definition itself has very few direct dependencies:

1. `ℤ`
2. integer addition `+`
3. integer multiplication `*`
4. integer subtraction `-`
5. powers `^ 2`

No project-local theorem or earlier FLT5 declaration appears in the body of the definition.

Semantically, however, the immediately following theorem `GN5_eq_goldenNorm_squareLink` connects `GN5` to this definition, so `GoldenNorm` is introduced as the target vocabulary of the `GN5` bridge.

## Proof flow

There is no proof body because this is a definition.

Lean unfolds

```lean
GoldenNorm m n
```

when requested to

```lean
m ^ 2 + m * n - n ^ 2.
```

Later theorems use `unfold GoldenNorm` to expose the polynomial and then hand the resulting identity to `ring` normalization.

In particular, the source theorems `GN5_eq_goldenNorm_squareLink` and `four_mul_goldenNorm_eq_discriminant_five` both follow this pattern: unfold `GoldenNorm`, then close the polynomial identity by ring arithmetic.

## Lean-specific processing

### 1. A `def` creates an abstraction boundary

Instead of repeating

```lean
m ^ 2 + m * n - n ^ 2
```

inside every theorem, the code names the expression `GoldenNorm`, giving later types and theorem names mathematical meaning.

### 2. The domain is fixed to `ℤ`

Upstream, `GN5` appears as a quantity over `ℕ`. In the golden-norm bridge, differences, conjugation, and signed expressions arise naturally, so the target domain is `ℤ`.

This choice makes identities such as

$$
4N(m,n)=(2m+n)^2-5n^2
$$

ordinary ring statements rather than awkward natural-number subtraction statements.

### 3. A normal `def`, not an `abbrev`

Because this is a `def` rather than an `abbrev`, the simplifier is not forced to erase the name everywhere. The code can retain the abstract name where that improves readability and explicitly use `unfold GoldenNorm` where polynomial calculation is desired.

## Redundancy and overlap

There is essentially no redundancy in the definition body itself.

Possible overlap may appear later if the golden-order implementation introduces the same norm expression in another form. Even then, `GoldenNorm : ℤ → ℤ → ℤ` is a coordinate-level quadratic form, while a later norm API on an actual golden-integer structure has a different type-level role.

Accordingly, repeated formulas should not automatically be treated as accidental duplication: if they live at different abstraction layers, the duplication may be an intentional bridge.

## Optimization candidates

### Candidate A — keep the current dedicated definition

This is the clearest design. It provides a lightweight algebraic interface between `GN5` and golden arithmetic without requiring a number-field implementation.

### Candidate B — abstract to a general binary quadratic form

One could define

$$
Q_{a,b,c}(m,n)=am^2+bmn+cn^2
$$

and represent `GoldenNorm` as the coefficient choice $(1,1,-1)$.

If FLT5 only needs this one form, however, the abstraction cost is probably greater than the benefit.

### Candidate C — integrate early with the golden-order norm

After the later algebraic structure is available, a theorem identifying `GoldenNorm m n` with the norm of a corresponding golden integer would be useful.

But the purpose of this module is explicitly to build the bridge without requiring number-field identification, so performing that integration already at 0093 would make the dependency direction heavier.

### Candidate D — introduce notation

A local notation for $N(m,n)$ could shorten formulas, but the explicit name `GoldenNorm` is better for source searchability and theorem naming.

## Required Mathlib imports and import optimization

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch depends on `Mathlib` as a whole, and its manifest places `DkMath/FLT/Five/SquareGoldenBridge.lean` immediately after `SignedFiveAdicPowerSplit.lean`.

This definition alone only requires integers, elementary ring operations, and natural-number powers, so umbrella `Mathlib` is clearly larger than necessary for the isolated declaration.

The surrounding theorems in `SquareGoldenBridge.lean`, however, use `ring`, `push_cast`, and `norm_num`, so the module as a whole needs polynomial-normalization and coercion support.

The exact minimal Mathlib module list is not asserted here because the original split source file's import header was not directly verified in this run, and no Lean build was performed by instruction. A safe import-minimization task would inspect the original module's direct imports and then verify the `ring`/cast dependencies one by one with a separate build.

## Comparator challenge suitability

This is suitable, though primarily as a representation-design challenge rather than a theorem-proving challenge.

The comparison candidates are:

1. the current dedicated `GoldenNorm` definition;
2. a specialization of a general binary quadratic-form abstraction;
3. defining the norm only after introducing a golden-integer structure and exposing it as a projection;
4. avoiding a named definition and expanding the formula directly inside `GN5_eq_goldenNorm_squareLink`.

Useful evaluation axes are dependency weight, visibility of the mathematical meaning, connectivity to later golden arithmetic, simplicity of `ring` proofs, namespace cost, and proof-graph auditability.

The current design is especially strong because it fixes the quadratic form before depending on the later algebraic-number infrastructure.

## PDF and source basis

The formal source of truth is the target branch's `Flt5DkMath/FLT5StandAlone.lean`. It confirms that immediately after 0092 `branchB_false_of_powerSplitCore`, `SignedFiveAdicPowerSplit.lean` ends, `SquareGoldenBridge.lean` begins, and `GoldenNorm` is its first declaration.

The same module comment states that the endpoint-square coordinates

$$
m=(g+y)^2+y^2,\qquad n=(g+y)y
$$

rewrite `GN5 g y` as `m^2 + m*n - n^2` and then lead to the discriminant-five identity.

The existing Japanese and English PDFs should be treated as narrative background sources. In this run, GitHub code search returned an upstream 502 error, so a concrete PDF file/page corresponding one-to-one with this definition could not be verified. Therefore no PDF page number, section number, or quotation is supplied by guesswork.

## Next declaration to read

The declaration immediately following `GoldenNorm` in the source is

```lean
theorem GN5_eq_square_cross_form (g y : ℕ) :
    GN5 g y =
      (g ^ 2) ^ 2 +
        5 * (g ^ 2) * (y * (g + y)) +
        5 * (y * (g + y)) ^ 2 := by
  unfold GN5
  ring
```

This theorem first rewrites `GN5` as the square/cross quadratic expression

$$
g^4+5g^2\,y(g+y)+5\bigl(y(g+y)\bigr)^2.
$$

If 0093 introduces the target vocabulary `GoldenNorm`, then 0094 is the first actual algebraic computation that puts the natural-number `GN5` expression onto the coordinate path leading to that target.
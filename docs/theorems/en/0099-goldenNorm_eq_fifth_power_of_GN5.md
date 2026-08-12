# 0099 — `goldenNorm_eq_fifth_power_of_GN5`

## Lean Type

```lean
theorem goldenNorm_eq_fifth_power_of_GN5
    {g y b : ℕ} (hGN : GN5 g y = b ^ 5) :
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
      (b : ℤ) ^ 5 := by
  calc
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
        (GN5 g y : ℤ) := (GN5_eq_goldenNorm_squareLink g y).symm
    _ = ((b ^ 5 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hGN
    _ = (b : ℤ) ^ 5 := by norm_num
```

## Mathematical Statement

If natural numbers `g y b` satisfy

$$
\mathrm{GN5}(g,y)=b^5,
$$

then for the endpoint-square coordinates

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y,
$$

one has, over the integers,

$$
\mathrm{GoldenNorm}(M,N)=b^5.
$$

The earlier theorem 0096 `GN5_eq_goldenNorm_squareLink` already gives

$$
\mathrm{GN5}(g,y)=\mathrm{GoldenNorm}(M,N),
$$

so the mathematical content here is the transport of a fifth-power equality proved in `ℕ` to the GoldenNorm representation of the same value.

## Role in the Overall Proof

This is the closing theorem of the `SquareGoldenBridge.lean` segment.

0093 introduced `GoldenNorm`; 0094–0096 connected `GN5` and endpoint-square coordinates to that norm; 0097–0098 exposed the discriminant-$5$ form and the independent perfect-square boundary. The present theorem places fifth-power data onto that bridge.

Thus the proof graph contains the edge

$$
\mathrm{GN5}(g,y)=b^5
\Longrightarrow
\mathrm{GoldenNorm}(M,N)=b^5.
$$

The following `SquareGoldenNormalForm.lean` segment can therefore package the fifth-power GoldenNorm information together with the square-world boundary information in the same named coordinates.

## Direct Dependencies

The project-local direct dependencies are:

1. `GN5` — the fifth cyclotomic factor over natural numbers.
2. `GoldenNorm` — the integer quadratic form $m^2+mn-n^2$.
3. `GN5_eq_goldenNorm_squareLink` — the identification of `GN5` with `GoldenNorm` on endpoint-square coordinates.

On the Lean/Mathlib side, the proof uses `congrArg` to apply a function to an equality, the coercion from naturals to integers, and `norm_num` to normalize the cast of a power.

## Proof Flow

The proof is a three-step `calc` chain.

The first step uses theorem 0096 in reverse:

```lean
(GN5_eq_goldenNorm_squareLink g y).symm
```

This rewrites the GoldenNorm expression back to `(GN5 g y : ℤ)`.

The second step applies the coercion from naturals to integers to both sides of

```lean
hGN : GN5 g y = b ^ 5
```

using

```lean
congrArg (fun n : ℕ => (n : ℤ)) hGN
```

and therefore obtains

$$
(\mathrm{GN5}(g,y):\mathbb Z)=((b^5:\mathbb N):\mathbb Z).
$$

The third step closes the coercion boundary

$$
((b^5:\mathbb N):\mathbb Z)=(b:\mathbb Z)^5
$$

by `norm_num`.

## Lean-Specific Processing

The essential Lean-specific issue is the explicit crossing between the mathematically compatible `ℕ` and `ℤ` worlds.

The hypothesis `hGN` is an equality in `ℕ`, so it cannot directly be inserted into an equality whose left side is `GoldenNorm : ℤ → ℤ → ℤ`. The proof therefore passes the coercion function to `congrArg`, lifting the entire equality into `ℤ`.

The bridge theorem 0096 is oriented as

$$
(\mathrm{GN5}(g,y):\mathbb Z)=\mathrm{GoldenNorm}(M,N),
$$

so `.symm` is used to match the starting point of the present `calc` chain.

The final `norm_num` step does not prove new number theory; it automatically normalizes the compatibility of coercion with exponentiation, corresponding to the usual `Nat.cast_pow` behavior.

## Redundancy and Duplication

Mathematically, the statement is almost entirely the transitivity of theorem 0096 and the hypothesis `hGN`. The third step exists because Lean makes the `ℕ`/`ℤ` type boundary explicit.

If the pattern “cast a natural-number equality to integers and connect it to a project-local bridge” occurs repeatedly, a local helper lemma could reduce duplication.

On the other hand, the current three-step `calc` cleanly separates:

1. structural conversion,
2. transport of the hypothesis,
3. coercion normalization.

That separation gives the proof high auditability and is a reason not to over-golf it.

## Optimization Candidates

1. Keep the current proof; it exposes the proof graph most clearly.
2. Test `exact_mod_cast hGN` or `norm_cast` to merge the second and third steps, at the cost of making tactic behavior less explicit.
3. Shorten the proof around `rw [← GN5_eq_goldenNorm_squareLink g y]`; this may concentrate coercion-direction issues into a less transparent step.
4. Introduce a generic helper for lifting natural-number equalities to integer equalities, but only if several later proofs repeat the same pattern.
5. Move earlier to the later `SquareGoldenM` / `SquareGoldenN` named coordinates to avoid repeating the long endpoint-square expressions. This would be a cross-module design change.

## Required Mathlib Imports and Import Optimization

The generated standalone artifact uses `import Mathlib`. Directly, this theorem needs integer coercions, powers, `congrArg`, and the `norm_num` tactic; project-locally it needs `GN5`, `GoldenNorm`, and `GN5_eq_goldenNorm_squareLink`.

For this theorem in isolation, umbrella `Mathlib` is likely broader than necessary. A reduced import set centered on `Mathlib.Tactic.NormNum` plus the basic natural/integer coercion modules is a plausible candidate. However, the full `SquareGoldenBridge.lean` segment also contains earlier theorems using `ring` and `push_cast`, so the minimal import set for the whole module should not be claimed without a Lean build.

## Comparator Challenge Suitability

Yes. It is particularly useful as a comparison exercise for coercion handling.

Candidate approaches are:

1. the current explicit `calc + congrArg + norm_num` proof,
2. a shorter `norm_cast` / `exact_mod_cast` proof,
3. a rewrite-centered proof using theorem 0096 first,
4. a structured proof using a reusable cast helper lemma.

The evaluation criteria should include not only line count but also whether the `ℕ → ℤ` boundary remains visible, whether the role of the bridge theorem is easy to audit, and whether tactic dependence becomes excessive.

## Relation to Existing Materials

The formal final authority is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its generated source marker places this theorem as the final theorem of `DkMath/FLT/Five/SquareGoldenBridge.lean`, immediately before `SquareGoldenNormalForm.lean` begins.

For the existing Japanese and English PDFs, GitHub code search returned an upstream 502 during this run, and a public Web search did not uniquely identify the corresponding PDF files in this repository. Therefore no page or section number is supplied by guesswork.

## Next Theorem to Read

In dependency order, the next declaration is the first definition in the new `SquareGoldenNormalForm.lean` module:

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

followed by

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

If the museum continues to include definitions in dependency order, the natural next article is `SquareGoldenM`. If the sequence is restricted strictly to theorems, the next theorem after these two coordinate definitions is `squareGolden_tenth_boundary_base`.
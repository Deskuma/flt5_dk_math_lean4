# 0178 — `goldenTau`

## Lean type

```lean
/-- The distinguished ramifier `2 + phi`. -/
def goldenTau : GoldenInt := ⟨2, 1⟩
```

This is a `def`, not a theorem. It names the concrete element

$$
2+\varphi
$$

of the golden integer ring `GoldenInt` as `goldenTau`.

## Mathematical statement and meaning of the declaration

In `GoldenInt`, the coordinate pair `⟨a,b⟩` represents $a+b\varphi$, so

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

represents exactly

$$
\tau=2+\varphi.
$$

With $\varphi=(1+\sqrt5)/2$ and the preceding declaration 0177,

$$
\sqrt5=2\varphi-1,
$$

the later source proves

$$
\tau=\varphi\sqrt5
$$

through

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

It also proves

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

so

$$
N(\tau)=5.
$$

Thus `goldenTau` is the distinguished norm-five element representing the ramified prime above five inside the explicit golden order.

## Role in the overall proof

0177 `goldenSqrtFive` fixes the square-root-side ramified element corresponding to $2\varphi-1$. The present declaration fixes a unit-associated representative, $2+\varphi$, whose norm is positive five and which is used directly as a visible factor in the exceptional FLT5 branch.

The source immediately continues with

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
abbrev tau : GoldenInt := goldenTau
```

and then develops

- `goldenSqrtFive_sq`
- `goldenNorm_sqrtFive`
- `goldenTau_eq_phi_mul_sqrtFive`
- `goldenNorm_tau`
- `golden_tau_mul_conj`
- `exists_goldenTau_factor_of_five_dvd`

The last theorem is especially important: from divisibility $5\mid 2M+N$ it explicitly extracts `goldenTau` as a factor of the corresponding `GoldenInt`. Therefore `goldenTau` is not merely a named arithmetic constant; it is the concrete ramified factor used to expose the five-adic exceptional structure.

## Direct dependencies

The definition itself has very few syntactic dependencies:

- `GoldenInt`
- the integer literals `2` and `1`

Its mathematical interpretation is closely connected with

- 0161 `goldenPhi`
- 0164 `goldenNorm`
- 0177 `goldenSqrtFive`

but the definition body does not call them. Instead it uses the already reduced coordinate pair `⟨2,1⟩` directly.

## Proof / construction flow

There is no proof script.

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

is a direct structure literal.

Conceptually the construction is:

1. choose the distinguished ramifier $\tau=2+\varphi$;
2. read off the coefficients in the basis $1,\varphi$;
3. store the coefficients $2,1$ as the two integer coordinates of `GoldenInt`.

## Lean-specific processing

Because the expected type is `GoldenInt`, Lean elaborates `⟨2,1⟩` using the structure constructor, with both literals interpreted as integers.

The implementation deliberately uses explicit coordinates rather than an algebraic expression such as `goldenPhi * goldenSqrtFive`. This keeps downstream closed proofs close to concrete integer arithmetic. In the source, `goldenNorm_tau` closes with `norm_num`, while `goldenTau_eq_phi_mul_sqrtFive` closes with `decide`.

The declaration is not marked `@[simp]`, because it is a distinguished named element rather than a rewrite rule intended to define a global normalization direction.

## Redundancy and duplication

Immediately afterward the source introduces

```lean
abbrev tau : GoldenInt := goldenTau
```

so `goldenTau` and `tau` are definitionally the same value and create a small API-level alias duplication.

There is also a representation-level duplication between the coordinate form `⟨2,1⟩` and the algebraic identity

$$
\tau=\varphi\sqrt5.
$$

The current source keeps the coordinate form as the definition and proves the algebraic relation separately.

## Optimization candidates

1. Keep the current `⟨2,1⟩` definition to preserve simple closed computation.
2. Define `goldenTau` from `goldenMul goldenPhi goldenSqrtFive`, exposing its mathematical provenance directly in the definition.
3. Keep the coordinate definition but express `goldenTau_eq_phi_mul_sqrtFive` through standard multiplication notation.
4. Audit downstream use of the alias `tau` and consolidate naming if the shorter public alias adds little value.
5. Abstract the construction as a ramified-prime representative in a generic quadratic order, specializing to discriminant five.

Since the local declaration is already one line, optimization concerns API organization, visibility of mathematical provenance, and generalizability rather than proof length.

## Required Mathlib imports and import optimization

This isolated `def` requires only the upstream `GoldenInt` declaration and basic integer-literal support. It directly uses no advanced Mathlib theorem or tactic.

The standalone artifact imports all of `Mathlib`, but the complete `GoldenOrder` module also uses `Zsqrtd`, `ring`, `omega`, `norm_num`, `interval_cases`, and substantial algebraic typeclass infrastructure. Import minimization should therefore be evaluated at module level rather than from this single declaration.

No Lean build is performed in this museum pass, so an exact minimal import set is not claimed.

## Comparator challenge suitability

Yes.

Useful implementations to compare are:

- explicit coordinates `⟨2,1⟩`;
- `goldenMul goldenPhi goldenSqrtFive`;
- standard notation `goldenPhi * goldenSqrtFive`;
- construction of a ramified element in a generic quadratic-order or `AdjoinRoot` representation.

Comparison criteria include proof burden for `goldenNorm_tau` and the factor-extraction theorem, definitional transparency, readability of the mathematical provenance, interaction with `simp` / `norm_num` / `decide`, and generalizability.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this declaration appears immediately after 0177 `goldenSqrtFive` and is followed by the alias `sqrtFiveElement`.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this declaration was not directly identified, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- Short public name for the element `2φ-1`, whose square is five. -/
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

By 0177–0178 the internal names `goldenSqrtFive` and `goldenTau` for the two ramified elements are in place. The next declarations introduce shorter public aliases before the source proceeds to their square, norm, and factor-extraction theorems.
# 0177 — `goldenSqrtFive`

## Lean type

```lean
/-- The ramified square root `2*phi - 1` of five. -/
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

This is a `def`, not a theorem. It names the concrete element

$$
-1+2\varphi
$$

of the golden integer ring `GoldenInt` as `goldenSqrtFive`.

## Mathematical statement and meaning of the declaration

The golden basis element is interpreted as

$$
\varphi=\frac{1+\sqrt5}{2},
$$

so

$$
2\varphi-1=\sqrt5.
$$

In `GoldenInt`, the coordinate pair `⟨a,b⟩` represents $a+b\varphi$. Therefore

$$
\sqrt5=-1+2\varphi
$$

corresponds to the coordinate pair

$$
(-1,2).
$$

Hence

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

fixes an explicit representative of the ramified element corresponding to the square root of five inside the quadratic order.

A significant implementation detail is that the definition does not syntactically refer to `goldenPhi`. Its mathematical meaning is $2\varphi-1$, but the Lean representation uses the already reduced integral coordinates `⟨-1,2⟩` directly.

## Role in the overall proof

By 0176 `golden_mul_conj`, the basic relationship between conjugation and norm has been established:

$$
x\overline{x}=N(x).
$$

The present declaration begins the next stage, where the exceptional prime `5` is represented by explicit ramified elements in the golden order.

The source continues with `goldenTau := ⟨2,1⟩`, short aliases, and then

```lean
theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide

theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

Thus `goldenSqrtFive` is the reference element used to formalize

$$
(\sqrt5)^2=5,
\qquad
N(\sqrt5)=-5.
$$

It is also connected directly to the distinguished norm-five element by

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

so this declaration becomes part of the explicit arithmetic of the ramified prime above five used in the FLT5 exceptional-factor analysis.

## Direct dependencies

The syntactic dependencies of this `def` are minimal:

- `GoldenInt`
- the fact that the two coordinates of `GoldenInt` are integers
- the integer literals `-1` and `2`

Its mathematical interpretation is closely related to the upstream declarations

- 0161 `goldenPhi`
- 0163 `goldenConj`
- 0164 `goldenNorm`

but none of them is called in the definition body.

Likewise, 0165 `golden_phi_sq`,

$$
\varphi^2=\varphi+1,
$$

can be used mathematically to derive $(2\varphi-1)^2=5$, but this `def` itself has no theorem-level dependency on that result.

## Proof / construction flow

There is no proof script.

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

is a direct structure literal.

Conceptually the construction is:

1. interpret the square root of five as $2\varphi-1$;
2. read off the coefficients in the basis $1,\varphi$;
3. store $a=-1$ and $b=2$ in the two coordinates of `GoldenInt`.

## Lean-specific processing

The expected type `GoldenInt` lets Lean infer the structure constructor in `⟨-1, 2⟩`. Since both coordinates are of type `ℤ`, the literals `-1` and `2` are elaborated as integers.

The definition deliberately uses a coordinate literal instead of an algebraic expression such as

```lean
2 * goldenPhi - 1
```

This keeps downstream closed computations definitionally close to concrete integer arithmetic. In particular, the later theorem `goldenSqrtFive_sq` can be closed by `decide`, which benefits from the computational transparency of the explicit representation.

The declaration is not marked `@[simp]`. It is a named arithmetic element rather than a rewrite rule intended to define a normalization direction.

## Redundancy and duplication

Immediately afterward the source introduces

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

so `goldenSqrtFive` and `sqrtFiveElement` are definitionally the same value and form an API-level duplication.

Their roles can nevertheless be distinguished:

- `goldenSqrtFive`: the explicit coordinate name local to the golden-order construction;
- `sqrtFiveElement`: a shorter public-facing alias for downstream use.

There is also a representation-level duplication between the coordinate form `⟨-1,2⟩` and the algebraic identity `2*goldenPhi-1`. The current source chooses the coordinate form for computational transparency.

## Optimization candidates

1. Keep `⟨-1,2⟩` as the definition and preserve simple closed computation.
2. Define `goldenSqrtFive` as `2 * goldenPhi - 1`, putting the mathematical provenance directly into the definition.
3. Keep the coordinate definition but add a standard-notation theorem

```lean
goldenSqrtFive = 2 * goldenPhi - 1
```

so mathematical meaning and computational representation remain separate.
4. Audit downstream use of `sqrtFiveElement`; if the alias contributes little, consolidate the public naming layer.
5. Abstract the construction as a discriminant or ramified element in a generic quadratic order, with the coordinate pair for discriminant five as a specialization.

The local declaration is already one line, so optimization concerns API organization and abstraction rather than proof length.

## Required Mathlib imports and import optimization

This `def` alone requires only the upstream `GoldenInt` declaration and basic integer-literal support. It directly uses no advanced Mathlib theorem or tactic.

The standalone artifact imports all of `Mathlib`, which is clearly broader than this isolated declaration needs. The complete `GoldenOrder` module, however, also uses `Zsqrtd`, `ring`, `omega`, `norm_num`, `interval_cases`, and substantial algebraic typeclass infrastructure. Import minimization should therefore be evaluated at module level rather than from this single line.

No Lean build is performed in this museum pass, so an exact minimal import set is not claimed.

## Comparator challenge suitability

Yes.

Useful implementations to compare are:

- explicit coordinates `⟨-1,2⟩`;
- the algebraic expression `2 * goldenPhi - 1`;
- construction from a generic discriminant element in an `AdjoinRoot` or quadratic-order representation.

Comparison criteria include:

- simplicity of the proof of `goldenSqrtFive_sq`;
- definitional transparency;
- visibility of the mathematical provenance;
- interaction with `simp`, `norm_num`, and `decide`;
- proof burden in downstream ramification theorems;
- generalizability.

This small declaration provides a clear test of the tradeoff between a coordinate-first definition optimized for computation and an algebraic-expression-first definition optimized for conceptual readability.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this definition appears immediately after 0176 `golden_mul_conj` and is followed by `goldenTau`.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this declaration was not directly identified, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- The distinguished ramifier `2 + phi`. -/
def goldenTau : GoldenInt := ⟨2, 1⟩
```

With 0177, the ramified square-root element corresponding to $2\varphi-1=\sqrt5$ has been fixed explicitly. The next step introduces

$$
\tau=2+\varphi,
$$

the norm-five ramifier used directly in downstream factor extraction, followed by the public aliases and the square, norm, and $\varphi\sqrt5$ relationships.
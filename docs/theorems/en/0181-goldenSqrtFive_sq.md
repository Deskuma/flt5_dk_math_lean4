# 0181 — `goldenSqrtFive_sq`

## Lean type

```lean
theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide
```

This is a `theorem`. It states that `goldenSqrtFive : GoldenInt := ⟨-1, 2⟩`, introduced in 0177, really squares to the embedded integer `5`.

## Mathematical statement and meaning of the declaration

A coordinate pair `⟨a,b⟩ : GoldenInt` represents $a+b\varphi$. Declaration 0177 defines

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

so

$$
goldenSqrtFive=-1+2\varphi=2\varphi-1.
$$

Using the golden relation $\varphi^2=\varphi+1$,

$$
(2\varphi-1)^2=4\varphi^2-4\varphi+1=4(\varphi+1)-4\varphi+1=5.
$$

Thus the theorem formalizes

$$
(2\varphi-1)^2=5
$$

inside the explicit coordinate model of the golden integer ring. The right-hand side `goldenOfInt 5` is the embedded integer $5$, namely the coordinate element `⟨5,0⟩`.

## Role in the overall proof

Declarations 0177–0180 introduce the ramified elements and their shorter public names. This theorem is the first substantive arithmetic result after that naming layer: it certifies that the distinguished element called `goldenSqrtFive` satisfies the expected square-root relation.

It is immediately followed by

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

and then by `goldenTau_eq_phi_mul_sqrtFive`, `goldenNorm_tau`, `golden_tau_mul_conj`, and `exists_goldenTau_factor_of_five_dvd`. Hence 0181 opens the explicit ramification arithmetic at the prime five.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- the raw multiplication `goldenMul`
- 0162 `goldenOfInt`
- 0177 `goldenSqrtFive`

Mathematically, the result expresses the same quadratic reduction rule as 0165 `golden_phi_sq`, namely $\varphi^2=\varphi+1$. However, the Lean proof does not rewrite by 0165. Instead, because `goldenMul` already contains the reduced coordinate multiplication, the theorem can be checked as a closed coordinate equality.

## Proof / construction flow

The proof is a single line:

```lean
by
  decide
```

All terms are concrete integer coordinates. After unfolding the definitions, the proposition reduces to the equality

```text
goldenSqrtFive = ⟨-1, 2⟩
goldenMul ⟨-1,2⟩ ⟨-1,2⟩ = ⟨5,0⟩
goldenOfInt 5 = ⟨5,0⟩
```

so Lean closes the proposition using decidable equality.

## Lean-specific processing

The use of `by decide` is significant: Lean is not invoking a general ring theorem here. It is evaluating a completely closed proposition whose equality is decidable.

Alternative proof shapes could include coordinate extensionality plus normalization, for example an `ext` / `norm_num` style proof, or a proof using standard ring notation and `ring`. Because this museum run does not execute a Lean build, those alternatives are optimization candidates rather than verified replacements.

## Redundancy and duplication

Mathematically, the theorem can be derived from 0165 `golden_phi_sq` together with the identity `goldenSqrtFive = 2φ-1`. If `goldenSqrtFive` had been defined directly through standard algebra notation, reusing `golden_phi_sq` would be a natural proof route.

The current code instead defines `goldenSqrtFive` directly as coordinates `⟨-1,2⟩`. In that representation, a closed `decide` proof is shorter and also acts as a regression check for the coordinate multiplication implementation.

Thus the apparent duplication reflects two different proof styles: deriving the identity from the abstract generator relation versus directly certifying the concrete coordinate model.

## Optimization candidates

1. Keep the current `by decide` proof as a minimal closed coordinate certificate.
2. Define `goldenSqrtFive` in standard algebra notation, close to `2 * goldenPhi - 1`, and derive the theorem from 0165 `golden_phi_sq`.
3. Use the bridge `golden_mul_eq` and state the public theorem as `goldenSqrtFive ^ 2 = 5`.
4. Provide both a raw-API theorem and a standard-notation theorem, with the latter as the primary public statement.
5. Abstract the construction to a generic quadratic-order theorem for a discriminant or ramified square-root element.

The current design has the advantage of a very small proof and strong definitional transparency.

## Required Mathlib imports and import optimization

This theorem itself only needs the existing definitions and the `decide` mechanism; it directly uses no advanced Mathlib theorem.

The standalone artifact imports all of `Mathlib`, but 0181 alone does not justify such a broad import. The true minimal import set is governed by the full `GoldenOrder` module, which also uses integer arithmetic, ring structures, `Zsqrtd`, and later algebraic infrastructure.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and import reduction is recorded only as an optimization candidate.

## Suitability as a Comparator challenge

Yes. Useful implementations to compare include:

- concrete coordinates + `by decide`
- `ext` + `norm_num`
- standard notation + `ring`
- derivation from `golden_phi_sq`
- specialization of a generic quadratic-order theorem

Comparison criteria include proof-term size, robustness under definition changes, mathematical readability, definitional transparency, import requirements, and downstream reuse.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `GoldenOrder` source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this theorem appears immediately after the `tau` alias and is followed by `goldenNorm_sqrtFive`.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to 0181 was not identified directly, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

Declaration 0181 establishes

$$
(2\varphi-1)^2=5.
$$

Declaration 0182 then proves that the same element has norm

$$
N(2\varphi-1)=-5,
$$

making the norm-five ramification arithmetic more explicit.
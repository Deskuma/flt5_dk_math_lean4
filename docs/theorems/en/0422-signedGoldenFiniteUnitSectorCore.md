# 0422 `signedGoldenFiniteUnitSectorCore`

## Declaration kind

`theorem`

## Lean type

```lean
/-- Every stripped golden packet is unconditionally reduced to the five sectors. -/
theorem signedGoldenFiniteUnitSectorCore : SignedGoldenFiniteUnitSectorCore :=
  signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

## Mathematical statement and meaning

0422 states that every ramifier-stripped signed golden packet is unconditionally reduced to one of five unit sectors.

Its conclusion, `SignedGoldenFiniteUnitSectorCore`, is an `abbrev : Prop` defined as

```lean
abbrev SignedGoldenFiniteUnitSectorCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ i : Fin 5, ∃ gamma : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)
```

Thus, mathematically, for every stripped packet `p`, its associated golden integer `p.beta` can be written in the form

$$
\beta = \phi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}.
$$

The five sectors are not geometric angular sectors. They are algebraic sectors corresponding to representatives of golden-order units modulo fifth powers,

$$
1,\ \phi,\ \phi^2,\ \phi^3,\ \phi^4.
$$

Because the exponent is odd, a sign can be absorbed into `gamma`, so no separate sign sector is required.

0422 does not re-prove this classification. Instead, it supplies the already-proved unit-classification theorem to the conditional sector-reduction receiver, thereby making the result unconditional.

## Role in the overall proof

Although 0422 appears after the final FLT5 endpoints 0420–0421, mathematically it republishes an important internal proof structure as a public facade theorem.

The proof architecture first uses coprime factorization to write the stripped packet factor as

$$
\beta = \varepsilon\gamma^5,
$$

where `epsilon` is a golden unit. Unit classification then gives

$$
\varepsilon = \phi^i\delta^5,
$$

hence

$$
\beta
= \phi^i\delta^5\gamma^5
= \phi^i(\delta\gamma)^5.
$$

This reduces the problem to five finite sectors.

That finite reduction is the branching point used later by `SignedGoldenSectorArithmetic`: sectors `i = 1,2,3,4` are eliminated arithmetically, while the surviving `i = 0` zero sector is sent into the strict-descent route.

The role of 0422 is to state at the Main facade layer that this finite-sector reduction is not a research assumption: it follows unconditionally from the already-proved `goldenUnitClassesModFifth` theorem.

## Direct dependencies

### `SignedGoldenFiniteUnitSectorCore`

This is an `abbrev : Prop` from `SignedGoldenUnitClasses.lean`.

```lean
abbrev SignedGoldenFiniteUnitSectorCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ i : Fin 5, ∃ gamma : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)
```

The conclusion of 0422 is exactly this proposition.

### `GoldenUnitClassesModFifth`

This is the unit-classification contract exported from the same module.

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

It states that every golden unit reduces, modulo fifth powers, to one of the five representatives `phi^i`.

### `signedGoldenFiniteUnitSectorCore_of_unitClasses`

This is the receiver theorem directly invoked by 0422.

```lean
theorem signedGoldenFiniteUnitSectorCore_of_unitClasses
    (hClasses : GoldenUnitClassesModFifth) :
    SignedGoldenFiniteUnitSectorCore := by
  intro u v w p
  obtain ⟨epsilon, gamma, hepsilon, hbeta⟩ :=
    signedGoldenFifthPowerUpToUnitCore p
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  refine ⟨i, goldenMul delta gamma, ?_⟩
  rw [hbeta, hdelta]
  simp only [golden_mul_eq, golden_pow_eq]
  rw [mul_pow]
  ring
```

This theorem performs the actual composition of the factorization with the unit classification.

### `goldenUnitClassesModFifth`

This is the unconditional provider theorem proved in `GoldenUnitClassification.lean`.

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

0422 supplies this theorem as the only hypothesis of `signedGoldenFiniteUnitSectorCore_of_unitClasses`.

### Indirect kernel: `signedGoldenFifthPowerUpToUnitCore`

Although it does not occur directly in the body of 0422, the receiver internally uses

```lean
signedGoldenFifthPowerUpToUnitCore p
```

to extract factorization data of the form

```lean
∃ epsilon gamma,
  GoldenUnit epsilon ∧
  p.beta = goldenMul epsilon (goldenPow gamma 5)
```

This theorem connects the golden-order coprime factor theorem to the FLT5 packet and is therefore the algebraic entry point to the five-sector reduction.

## Proof or construction flow

The body of 0422 is a single proof term:

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

It can be decomposed as follows.

### 1. Obtain the conditional receiver

The theorem

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore
```

states that unit classification is sufficient to reduce every stripped packet to five sectors.

### 2. Supply the unconditional unit-classification provider

`GoldenUnitClassification.lean` proves

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

unconditionally.

Its underlying proof uses coordinate-measure descent on golden units and shows that every unit belongs, modulo fifth powers, to one of the classes `phi^i` with `i : Fin 5`.

### 3. Discharge the receiver's final hypothesis

Applying the receiver to the provider,

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses
  goldenUnitClassesModFifth
```

has type

```lean
SignedGoldenFiniteUnitSectorCore
```

immediately.

No tactic block, rewrite, case split, or arithmetic normalization is needed in 0422 itself.

## Lean-specific processing

### Passing a proposition proof as a theorem argument

`GoldenUnitClassesModFifth` is a `Prop`, and

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

is its proof object.

The receiver has type

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore
```

so 0422 closes by ordinary Curry–Howard function application.

### Definitional transparency of `abbrev`

Both `GoldenUnitClassesModFifth` and `SignedGoldenFiniteUnitSectorCore` are `abbrev : Prop` declarations. Lean can transparently unfold them into their quantified propositions when needed.

No explicit `unfold` is necessary in 0422 because the types already match directly.

### `Fin 5` as a type-level finite-sector index

The sector index is represented as

```lean
i : Fin 5
```

rather than as a natural number plus a separate inequality. This incorporates `i.val < 5` into the type and aligns naturally with later `fin_cases` proofs over the five sectors.

## Redundancy and duplication

The proof body of 0422 is mathematically only a composition of an existing receiver with an existing provider. It introduces no new number-theoretic content.

A user could obtain the same proof object directly with

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

without the named theorem 0422. In that information-theoretic sense, the declaration is redundant.

However, it is useful as a Main-layer facade theorem because it:

- separates the conditional interface from the unconditional result;
- makes the unconditional provider discoverable by the name `signedGoldenFiniteUnitSectorCore`;
- records at the API level that unit classification has already been discharged;
- makes the proof architecture easier to audit by showing exactly where the hypothesis is closed.

Thus the duplication is intentional endpoint/facade duplication, analogous to the conditional-to-unconditional endpoint chain around 0418–0420.

## Optimization candidates

### 1. Remove the facade theorem

If minimizing code size were the only goal, 0422 could be deleted and callers could use

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

directly.

That would preserve the mathematics but reduce API readability, so retaining the wrapper is reasonable.

### 2. The current proof syntax is already minimal

It could also be written as

```lean
by
  exact signedGoldenFiniteUnitSectorCore_of_unitClasses
    goldenUnitClassesModFifth
```

but the existing term-style proof is shorter.

No `simpa` or `unfold` is needed, so there is essentially no local proof-code optimization available.

### 3. Architectural naming consistency

If the Main facade layer is reorganized later, one possible optimization is to standardize provider naming around a pattern such as

```text
<contract>_of_<assumption>
<contract>
```

for conditional/unconditional pairs. 0422 already approximately follows this pattern.

## Required Mathlib import

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

However, the body of 0422 itself performs only theorem application and introduces no specialized Mathlib tactic or API.

At minimum, the following FLT5 declarations must already be available:

- `SignedGoldenFiniteUnitSectorCore`
- `signedGoldenFiniteUnitSectorCore_of_unitClasses`
- `GoldenUnitClassesModFifth`
- `goldenUnitClassesModFifth`

Their transitive definitions and proofs in turn require `GoldenInt`, `GoldenUnit`, `goldenMul`, `goldenPow`, `Fin 5`, packet structures, Euclidean/gcd machinery, and related infrastructure.

### Import optimization candidate

It is unlikely that 0422 by itself needs a direct `import Mathlib`. In the split source tree, imports providing `SignedGoldenUnitClasses` and `GoldenUnitClassification`, together with their transitive imports, should likely suffice.

This run does not execute a Lean build, so the exact minimal Mathlib module set and exact minimal import closure have not been measured. No specific smaller import set is asserted as confirmed.

## Comparator challenge suitability

 **Suitable. In isolation it is low difficulty, but it is a clean dependency-selection challenge.**

A minimal challenge could be

```lean
theorem challenge : SignedGoldenFiniteUnitSectorCore := by
  ?_
```

with the main available declarations

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore

goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

The solver succeeds by matching the provider to the receiver:

```lean
exact signedGoldenFiniteUnitSectorCore_of_unitClasses
  goldenUnitClassesModFifth
```

A more useful challenge can hide `goldenUnitClassesModFifth` and expose only `goldenUnitFifthClass_of_unit`. The solver must then reconstruct `GoldenUnitClassesModFifth` by:

1. reading the quantified contract;
2. introducing `epsilon` and `GoldenUnit epsilon`;
3. applying the unit-classification theorem;
4. supplying the reconstructed contract to the sector receiver.

This tests theorem selection and interface understanding rather than merely name lookup.

For still higher difficulty, hide `signedGoldenFiniteUnitSectorCore_of_unitClasses` as well and require the solver to construct the sector witness from `signedGoldenFifthPowerUpToUnitCore` plus unit classification. That version exercises witness construction, rewriting, `mul_pow`, and ring normalization and becomes a substantive proof challenge.

## Next declaration to read

The next declaration is 0423 `counterexamplePackRefuter_of_zeroArithmetic`, of kind `theorem`.

```lean
/-- The zero-sector arithmetic proposition refutes every primitive packet. -/
theorem counterexamplePackRefuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

After 0422 publishes the unconditional finite unit-sector core facade, 0423 returns to the zero-sector arithmetic boundary. It accepts `GoldenZeroSectorArithmeticExclusion` as a hypothesis and internally supplies the already-proved unit classification to obtain a refuter for every primitive `CounterexamplePack`.

Therefore the dependency-order documentation continues with 0423.
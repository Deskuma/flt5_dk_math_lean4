# 0253 — `GoldenCoprimeFactorOfFifthPower`

## Lean type

```lean
/--
The generic factorization contract: a factor of a fifth power that is relatively prime
to its complementary factor is itself a fifth power up to a unit.
-/
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

This declaration is not a theorem. It is an **`abbrev : Prop`** naming the generic fifth-power factor-extraction contract in the golden integers while keeping the contract separate from its eventual proof.

## Mathematical statement and meaning of the declaration

The mathematical content is:

$$
xy=z^5,
\qquad
\operatorname{RelPrime}(x,y)
$$

implies that there exist a unit $\varepsilon$ and a golden integer $\gamma$ such that

$$
x=\varepsilon\gamma^5.
$$

In the raw Lean API,

- `GoldenRelPrime x y` means that every common divisor is a `GoldenUnit`;
- `goldenMul x y = goldenPow z 5` says that the product is a fifth power;
- `GoldenUnit epsilon` records unitness;
- `x = goldenMul epsilon (goldenPow gamma 5)` records the unit-times-fifth-power representation.

This is the golden-integer specialization of the standard UFD/gcd-domain principle that if two relatively prime factors multiply to an $n$-th power, then each factor is itself an $n$-th power up to a unit.

## Role in the full proof

By 0252, the stripped packet has already been converted into the two inputs required by the generic algebraic extraction step.

1. Declaration 0244 gives

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta}).
$$

2. Declaration 0252 gives

$$
\beta\overline{\beta}
=
(\operatorname{goldenOfInt} b)^5.
$$

Declaration 0253 deliberately forgets the packet-specific provenance and isolates only the general contract

$$
\text{coprime factors of a fifth power}
\Longrightarrow
\text{one factor is a fifth power up to a unit}.
$$

The immediately following declaration 0254 `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor` applies this contract to `beta` and `goldenConj beta`, producing the already-defined downstream requirement

$$
\beta=\varepsilon\gamma^5.
$$

Later in the source, `GoldenCoprimeFactor.lean` derives a `GCDMonoid GoldenInt` from the `EuclideanDomain GoldenInt` instance constructed in 0230 and proves the concrete implementation

```lean
goldenCoprimeFactorOfFifthPower : GoldenCoprimeFactorOfFifthPower
```

using the gcd/associated-power machinery.

Thus 0253 is the module boundary separating **FLT5-specific packet arithmetic** from **generic gcd/UFD-style fifth-power factor extraction**.

## Direct dependencies

Because this is an `abbrev`, it has no proof script and no direct theorem dependency.

Its statement directly uses:

- `GoldenInt`
- 0208 `GoldenRelPrime`
- 0198 `GoldenUnit`
- 0124 `goldenMul`
- `goldenPow`

Conceptually the contract packages the implication schema

$$
\operatorname{RelPrime}(x,y)
+
xy=z^5
\Longrightarrow
\exists \varepsilon,\gamma,
\quad
\operatorname{Unit}(\varepsilon)
\land
x=\varepsilon\gamma^5.
$$

The implementation of this contract is intentionally deferred to the later `GoldenCoprimeFactor.lean` module.

## Construction flow

The body consists only of universal quantification and implications:

```lean
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

Its logical flow is:

1. accept arbitrary `x y z : GoldenInt`;
2. assume that `x` and `y` satisfy `GoldenRelPrime`;
3. assume that their product is the fifth power of `z`;
4. require witnesses `epsilon` and `gamma`;
5. require `epsilon` to be a unit and `x` to equal `epsilon * gamma^5` in the raw golden API.

The declaration deliberately does not prescribe how factor extraction must be proved. A gcd proof, a unique-factorization proof, a valuation proof, or another implementation may satisfy the same contract without changing its consumers.

## Lean-specific processing

The use of

```lean
abbrev ... : Prop := ...
```

is significant.

Because it is an `abbrev` rather than an opaque `def`, the name remains transparently reducible to an ordinary function type. A downstream theorem can receive

```lean
hFactor : GoldenCoprimeFactorOfFifthPower
```

and immediately apply it as

```lean
hFactor p.beta (goldenConj p.beta) ...
```

without an explicit unfolding step.

Also, `GoldenRelPrime` and `GoldenUnit` are the explicit FLT5-domain interfaces rather than Mathlib's standard coprimality and `IsUnit` vocabulary. The contract therefore preserves the existing golden-order API boundary instead of exposing the implementation details of the later generic gcd theorem.

## Redundancy and duplication

Mathematically, this proposition is a fifth-power, `GoldenInt`-specific instance of a much more general theorem about coprime factors of powers, so there is substantial room for abstraction.

Potential duplication includes:

- the exponent is fixed to `5`;
- the ambient type is fixed to `GoldenInt`;
- `GoldenRelPrime` is a custom wrapper;
- `GoldenUnit` is a custom wrapper;
- raw `goldenMul` / `goldenPow` duplicate the meaning of standard `*` / `^` notation.

However, keeping the exact FLT5 consumer shape behind a named contract means downstream code does not need to know which Mathlib gcd/UFD theorem implements it. The declaration is therefore better understood as a **dependency-inversion contract layer** than as accidental logical duplication.

## Optimization candidates

1. **Keep the current contract**
   - it exactly matches the witness shape required downstream and cleanly separates modules.

2. **Generalize the exponent**
   - define something like `CoprimeFactorOfPow (n : ℕ)` and recover this declaration at `n = 5`.

3. **Generalize the ambient type**
   - formulate the theorem under `GCDMonoid`, `UniqueFactorizationMonoid`, or related assumptions.

4. **Move toward standard Mathlib vocabulary**
   - use bridges from `GoldenRelPrime` to standard coprimality, from `GoldenUnit` to `IsUnit`, and from raw operations to `*` / `^`.

5. **Use `Associated`**
   - instead of explicitly returning `epsilon`, conclude that `x` is associated to `gamma^5`.
   - the current existential form remains preferable if downstream proofs need the actual unit witness.

The present design is already well suited to the goal of allowing the proof engine to change while freezing the downstream witness interface.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

Declaration 0253 itself uses no tactic at all. Its direct surface is only the upstream golden-order definitions:

- `GoldenInt`
- `GoldenRelPrime`
- `GoldenUnit`
- `goldenMul`
- `goldenPow`

The later proof in `GoldenCoprimeFactor.lean`, however, uses Mathlib APIs including:

- `EuclideanDomain.gcdMonoid`
- `gcd`
- `IsUnit`
- `exists_associated_pow_of_mul_eq_pow`

so import minimization should be measured at the `SignedGoldenFifthPower.lean` / `GoldenCoprimeFactor.lean` module boundary rather than from 0253 in isolation.

No Lean build is performed in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

This declaration is highly suitable for a Comparator challenge focused on **abstraction level** rather than on a single proof script.

Possible variants are:

- A: the current `GoldenInt`, exponent-5-specific contract;
- B: an exponent-generalized contract;
- C: a generic theorem over `GCDMonoid`;
- D: a theorem over `UniqueFactorizationMonoid` using prime multiplicities;
- E: a standard-API version concluding `Associated x (gamma ^ 5)`.

Useful comparison axes include:

- downstream witness ergonomics;
- reuse of standard Mathlib APIs;
- generality of the theorem;
- typeclass dependency weight;
- standalone auditability;
- reduction in FLT5-specific code.

In particular, comparing the current existential-unit contract with an `Associated`-based generic theorem would clearly expose the trade-off between a concrete FLT5-facing witness API and a more idiomatic general-algebra interface.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenFifthPower.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this `abbrev` immediately after 0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth` and immediately before `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor`.

Later, `GoldenCoprimeFactor.lean` proves the concrete implementation using `EuclideanDomain.gcdMonoid GoldenInt` and `exists_associated_pow_of_mul_eq_pow`.

The target branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal contract was not identified in this run, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0254 `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor`**:

```lean
/-- Any implementation of the generic coprime-factor theorem supplies the stripped
packet's unit-times-fifth-power representation. -/
theorem signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    (hFactor : GoldenCoprimeFactorOfFifthPower) :
    SignedGoldenFifthPowerUpToUnitCore := by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

Declaration 0253 defines the generic factor-extraction contract. Declaration 0254 then feeds it the conjugate-coprimality certificate from 0244 and the fifth-power product identity from 0252, producing the stripped-packet core

$$
\beta=\varepsilon\gamma^5.
$$

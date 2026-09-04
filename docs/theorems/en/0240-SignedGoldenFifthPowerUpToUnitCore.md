# 0240 — `SignedGoldenFifthPowerUpToUnitCore`

## Lean type

```lean
/--
The algebraic output requested from a stripped packet: `beta` is a fifth power up to a
golden unit.  `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore` proves this
contract unconditionally after conjugate relative primality is certified.
-/
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

This is not a theorem but an `abbrev`. It gives a name to the proposition expressing the algebraic output that should eventually be extracted from a ramifier-stripped packet.

## Mathematical statement and meaning of the declaration

A `SignedGoldenRamifierStrippedPacket u v w` contains the golden integer `beta` obtained after removing one visible ramified factor `tau` from the exceptional branch. By the time this packet has been constructed, it carries data of the form

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta.
$$

Declaration 0240 asks for a stronger conclusion: the stripped element itself should have a factorization

$$
\beta=\varepsilon\gamma^5,
$$

where

- $\varepsilon$ is a unit of the golden order,
- $\gamma$ is a golden integer,
- `goldenPow gamma 5` represents $\gamma^5$, and
- `goldenMul epsilon (...)` represents $\varepsilon\gamma^5$.

Thus the proposition says that `beta` is an exact fifth power **up to multiplication by a unit**.

## Role in the full proof

Declarations 0237–0239 introduced a receiver contract that turns every ramifier-stripped packet into a contradiction and then lifted that receiver back through the Branch-A / Branch-B routing layers. Declaration 0240 takes a different role: it does not ask for `False` directly.

Instead, it isolates the essential algebraic payload that the Euclidean-domain / gcd / coprimality machinery is expected to produce:

$$
\beta=\varepsilon\gamma^5.
$$

This separation is structurally important. Rather than mixing fifth-power factor extraction with the eventual contradiction, the development names the intermediate algebraic contract independently.

The source comment explicitly states that a later theorem, `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore`, proves this contract unconditionally once relative primality of `beta` and its conjugate has been certified.

Conceptually, the later pipeline is therefore

$$
\text{ramifier-stripped packet}
\longrightarrow
\text{conjugate relative primality}
\longrightarrow
\beta=\varepsilon\gamma^5
\longrightarrow
\text{unit-sector / zero-sector analysis}
\longrightarrow
\bot.
$$

Declaration 0240 is the public contract for the middle “coprime factor of a fifth power is a fifth power up to a unit” stage.

## Direct dependencies

Because this declaration is an `abbrev`, it has no proof script and no direct theorem dependencies. Its type directly refers to:

- `SignedGoldenRamifierStrippedPacket`
- `GoldenInt`
- `GoldenUnit`
- `goldenMul`
- `goldenPow`
- natural numbers `ℕ`
- existential propositions `∃`

Conceptually,

$$
\texttt{SignedGoldenRamifierStrippedPacket}
+\texttt{GoldenUnit}
+\texttt{goldenPow}
\longrightarrow
\texttt{SignedGoldenFifthPowerUpToUnitCore}.
$$

A crucial point is that the packet field

$$
N(\beta)=b^5
$$

is not by itself sufficient to prove this contract. Knowing that the norm is a fifth power does not automatically imply that the element itself is a fifth power up to a unit. Factorization and relative-primality input are still required, and that is exactly what the following modules provide.

## Construction flow

The declaration simply names one proposition:

```lean
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

Its logical structure is:

1. take arbitrary indices `u v w`;
2. take an arbitrary stripped packet `p`;
3. require witnesses `epsilon` and `gamma`;
4. require `epsilon` to satisfy `GoldenUnit`;
5. require `p.beta = epsilon * gamma^5` in the explicit golden API.

The declaration does not prescribe how the witnesses are constructed. It is an interface for a producer, not the producer itself.

## Lean-specific processing

Because the declaration uses

```lean
abbrev ... : Prop := ...
```

Lean treats the name as a transparent abbreviation. Consumers can unfold it almost immediately back to the underlying `∀` / `∃` proposition when needed.

The indices

```lean
∀ {u v w : ℕ} ...
```

are implicit binders, so they are normally inferred from the type of `p`.

The nested existential

```lean
∃ epsilon gamma : GoldenInt,
  GoldenUnit epsilon ∧
  p.beta = goldenMul epsilon (goldenPow gamma 5)
```

can typically be produced in Lean by a term of the shape

```lean
refine ⟨epsilon, gamma, hUnit, hBeta⟩
```

once the witnesses and certificates have been constructed.

The statement deliberately keeps the raw operations `goldenMul` and `goldenPow`. Since those operations have already been connected to the standard algebra notation, the same mathematical statement could also be written as

```lean
p.beta = epsilon * gamma ^ 5
```

but the present API preserves the explicit golden-coordinate layer.

## Redundancy and duplication

Logically, this `abbrev` is only a name for a proposition. The same `∀ ... ∃ ...` statement could be written directly wherever it is needed.

The named contract is nevertheless valuable:

- it makes the required output of the stripped-packet layer explicit;
- it separates the gcd / Euclidean-domain producer from the later unit-sector consumer;
- it exposes the dependency boundary in theorem names;
- it allows the internal factor-extraction proof to change while keeping a stable public contract.

There is also a possible overlap with standard Mathlib notions such as `IsUnit` and `Associated`. Mathematically,

$$
\beta\sim\gamma^5
$$

could express that `beta` is associated to a fifth power.

The current formulation, however, keeps an explicit unit witness `epsilon`. That is useful later because the proof performs a concrete classification of unit sectors modulo fifth powers.

## Optimization candidates

1. **Keep the current transparent `abbrev`**
   - the producer / consumer boundary remains explicit and lightweight.

2. **Use standard algebra notation**

```lean
p.beta = epsilon * gamma ^ 5
```

   This may integrate more naturally with generic Mathlib rewriting, at the cost of hiding the explicit raw golden API.

3. **Express the result using `IsUnit` / `Associated`**
   - this could reuse generic algebraic infrastructure;
   - however, later code may still need to extract an explicit unit witness.

4. **Bundle the witnesses into a structure**
   - for example, a `SignedGoldenFifthPowerData` structure carrying `epsilon`, `gamma`, unitness, and the factorization equality;
   - useful if several downstream theorems reuse the same witnesses.

5. **Generalize the exponent**
   - one could define a generic “n-th power up to a unit” contract;
   - this development is specifically about exponent five, so the abstraction cost may exceed the benefit.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The Mathlib surface required by this `abbrev` itself is tiny: essentially `Prop`, universal / existential quantification, and `ℕ`.

The substantive dependencies are project declarations: `GoldenInt`, `GoldenUnit`, `goldenMul`, `goldenPow`, and `SignedGoldenRamifierStrippedPacket`.

Therefore the declaration alone should not require the whole of `Mathlib`. The surrounding `SignedGoldenRamifierStripped.lean` module, however, contains five-adic packet construction, divisibility, norm arithmetic, and ring tactics, so minimal imports should be measured at module scope.

No Lean build is performed in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current transparent `abbrev` using raw `goldenMul` / `goldenPow`
- B: an opaque `def`
- C: standard notation `epsilon * gamma ^ 5`
- D: a generic formulation using `IsUnit` / `Associated`
- E: a structure bundling the witnesses and certificates

Useful comparison axes are statement readability, definitional transparency, ease of downstream witness extraction, interoperability with Mathlib, proof-audit transparency, and future generalizability.

The comparison between A and D is particularly instructive: it measures the tradeoff between the FLT5-specific explicit golden API and a more abstract associated/unit-based algebraic formulation.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this declaration appears immediately after 0239 `branchB_false_of_goldenRamifierStrippedCore`, and it is the final declaration of `SignedGoldenRamifierStripped.lean`.

The source comment explicitly says that the later `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore` theorem proves this contract after conjugate relative primality has been certified.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal contract was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is the first theorem of the following module `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean`, **0241 `golden_sub_conj_eq_snd_mul_sqrtFive`**:

```lean
/-- Subtracting the conjugate isolates the square-root-of-five direction. -/
theorem golden_sub_conj_eq_snd_mul_sqrtFive (x : GoldenInt) :
    x - goldenConj x = goldenMul (goldenOfInt x.snd) sqrtFiveElement := by
  apply GoldenInt.ext
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
    ring
```

Declaration 0240 has made the fifth-power-extraction target explicit. Starting with 0241, the development proves the relative primality of `beta` and its conjugate that is needed to obtain that target. The first step is to show that

$$
x-\overline{x}
$$

lies entirely in the second-coordinate / $\sqrt5$ direction.
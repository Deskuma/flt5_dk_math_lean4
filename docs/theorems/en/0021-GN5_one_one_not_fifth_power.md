# 0021 — `GN5_one_one_not_fifth_power`

> This document is the English translation of the Japanese canonical edition.

## Lean type

```lean
theorem GN5_one_one_not_fifth_power :
    ¬ ∃ x : ℕ, GN5 1 1 = x ^ 5 := by
  exact not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

The fully qualified name is `DkMath.FLT.Five.GN5_one_one_not_fifth_power`.

## Mathematical statement

This theorem states that the concrete value `GN5 1 1` is not a perfect fifth power in the natural numbers.

$$
¬\exists x\in\mathbb{N},\ GN5(1,1)=x^5
$$

Using the earlier evaluation $GN5(1,1)=31$, this is the assertion that $31$ is not a fifth power of a natural number. The current proof does not directly unfold `GN5_one_one` and perform a numerical comparison. Instead, it passes to a general theorem the clean-channel certificate saying that the prime $31$ occurs in `GN5(1,1)` with local exponent exactly one.

## Role in the complete proof

This theorem is the first completed demonstration connecting the abstract consumer

```lean
not_fifth_power_GN5_of_clean
```

with the concrete provider

```lean
cleanGN5Channel_one_one_31
```

in a single line. It confirms that the local no-lift obstruction API works on an actual concrete input.

It is not itself a main step in the general exclusion of FLT5 counterexamples. Rather, it is an executable finite-prime escape example. Nevertheless, it is an important checkpoint because it displays, in the smallest possible case, the provider-consumer separation, the conflict between local exponent one and fifth-power exponents, and the intended form of theorem reuse.

## Direct dependencies

- `DkMath.FLT.Five.GN5`
- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.cleanGN5Channel_one_one_31`
- `DkMath.FLT.Five.not_fifth_power_GN5_of_clean`

Mathematically, `GN5_one_one : GN5 1 1 = 31` is also part of the background, but the proof term of this theorem does not reference it directly. The concrete evaluation is encapsulated in the provider.

## Proof flow

1. Obtain a clean-channel certificate for $g=1$, $y=1$, and $q=31$ from `cleanGN5Channel_one_one_31`.
2. Pass that certificate to the general theorem `not_fifth_power_GN5_of_clean`.
3. The general theorem derives a contradiction between local exponent one for $31$ and the exponent divisibility forced by a perfect fifth power.
4. Conclude `¬ ∃ x : ℕ, GN5 1 1 = x ^ 5`.

The theorem itself does not repeat the contradiction argument; it only composes two established APIs.

## Lean-specific processing

```lean
exact not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

Lean infers the implicit arguments `{g y q : ℕ}` from the target and the type of the provider. In particular, `cleanGN5Channel_one_one_31 : CleanGN5Channel 1 1 31` determines `g=1`, `y=1`, and `q=31` for the general theorem.

No arithmetic tactic, `rw`, `simp`, `norm_num`, or `ring` appears in this theorem. All computation and local divisibility reasoning are delegated to its dependencies. This thin proof indicates a well-formed semantic boundary between the provider and consumer layers.

## Redundancy and duplication

There is no substantial duplication in the proof body. It reuses both the general theorem `not_fifth_power_GN5_of_clean` and the concrete certificate `cleanGN5Channel_one_one_31`.

The same mathematical conclusion could likely be proved by rewriting with `GN5_one_one` and solving a closed numerical proposition directly. Such a proof might also be short, but it would no longer serve as an integration test for the clean-channel API.

## Optimization candidates

1. Keep the current one-line proof. It is already close to minimal while preserving the abstraction boundary.
2. Compare it with the term-style proof

```lean
theorem GN5_one_one_not_fifth_power :
    ¬ ∃ x : ℕ, GN5 1 1 = x ^ 5 :=
  not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

3. A `simpa` proof could be tested, but the types already match directly, so simplification appears unnecessary.
4. Compare against a direct numerical proof using `GN5_one_one` and `norm_num`, measuring proof-term size, dependencies, error locality, and value as an API regression test.
5. One could make this an `example` rather than a public theorem, but retaining a named theorem improves reuse and documentation links.

These proposals are unverified. No Lean build was performed.

## Required Mathlib imports and import optimization

The generated standalone source uses `import Mathlib`. This theorem itself merely applies existing declarations and requires no tactic or numerical computation directly.

Its effective environment only needs the following declarations to be available:

- `GN5`
- `CleanGN5Channel`
- `cleanGN5Channel_one_one_31`
- `not_fifth_power_GN5_of_clean`

Thus this theorem adds no further import requirement beyond its containing module. The complete `CleanChannel.lean` file, however, uses primality, divisibility, coprimality, `norm_num`, and `ring`, so file-level import minimization is a separate audit. Import minimization has not been verified.

## Comparator challenge suitability

This is well suited to a very small API-composition Comparator challenge.

Candidate variants include:

- The current provider-consumer composition.
- Term proof versus tactic proof.
- A direct numerical proof using `GN5_one_one`.
- `simpa using` versus direct `exact` and their inference clarity.
- A self-contained proof constructing the provider in a local `have`.

Useful comparison axes are not merely line count, but abstraction boundaries, dependency transparency, repeated computation, whether the proof acts as a regression test for the general API, and whether failures are localized to the provider or consumer layer.

## Next theorem to read

The next theorem is `DkMath.FLT.Five.coprime_y_z_of_counterexamplePack`.

This leaves the finite example in `CleanChannel.lean` and enters the general FLT5 reduction in `Reduction.lean`. From primitivity and the Fermat equation, it proves

$$
\gcd(y,z)=1
$$

which becomes the basis for coprimality of the gap and coordinate and later separation of the gap from `GN5`.

## Sources versus interpretation

The theorem type, proof, direct dependencies, declaration order, and next theorem were verified in the generated `DkMath/FLT/Five/CleanChannel.lean` section and the immediately following `Reduction.lean` section of `Flt5DkMath/FLT5StandAlone.lean`. The role in the complete proof, comparison with a direct numerical proof, import minimization, and Comparator proposals contain explanatory analysis or unverified suggestions. Existing PDFs were treated as supporting narrative context, while the Lean source was given priority.
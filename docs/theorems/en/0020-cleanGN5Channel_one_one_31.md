# 0020 — `cleanGN5Channel_one_one_31`

> This document is the English translation corresponding to the Japanese canonical edition.

## Lean type

```lean
theorem cleanGN5Channel_one_one_31 : CleanGN5Channel 1 1 31 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · norm_num [GN5]
  · norm_num
  · norm_num [GN5]
```

The fully qualified name is `DkMath.FLT.Five.cleanGN5Channel_one_one_31`.

## Mathematical statement

This theorem explicitly proves that `CleanGN5Channel` holds for $g=1$, $y=1$, and $q=31$.

$$
CleanGN5Channel(1,1,31)
$$

Expanded into the four structure fields, it asserts all of the following:

1. $31$ is prime.
2. $31∣GN5(1,1)$.
3. $31∤1$.
4. $31^2∤GN5(1,1)$.

Using the previously established concrete value

$$
GN5(1,1)=31,
$$

the second condition becomes $31∣31$, while the fourth becomes $31^2∤31$. Thus $31$ occurs exactly once in `GN5(1,1)` and does not occur in the gap $1$.

## Role in the complete proof

The preceding `CleanGN5Channel` theorems describe what follows once a clean prime has been supplied; they are consumer APIs. This theorem is the first concrete provider that actually constructs a clean channel for specific inputs.

Passing this provider to the immediately following theorem `GN5_one_one_not_fifth_power` specializes the general consumer

```lean
not_fifth_power_GN5_of_clean
```

and yields in one line that `GN5 1 1` is not a perfect fifth power.

This theorem does not by itself complete the general FLT5 contradiction. It is an executable finite example at $g=y=1$ showing that the whole finite-prime escape and local no-lift certificate pipeline works.

## Direct dependencies

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.GN5`
- the same concrete evaluation as `DkMath.FLT.Five.GN5_one_one`
- numerical verification of `Nat.Prime 31`
- tactic `refine`
- tactic `norm_num`

The proof does not reuse `GN5_one_one` by name. Instead, it unfolds and evaluates `GN5` twice with `norm_num [GN5]`.

## Proof flow

1. Use `refine ⟨by norm_num, ?_, ?_, ?_⟩` to construct the four fields of `CleanGN5Channel 1 1 31`.
2. Close the first field `prime` with `norm_num`, verifying that $31$ is prime.
3. Close `dvd_GN5` with `norm_num [GN5]`, evaluating `GN5(1,1)` to $31$ and proving $31∣31$.
4. Close `not_dvd_gap` with `norm_num`, proving $31∤1$.
5. Close `noLift` with `norm_num [GN5]`, numerically verifying $31^2∤31$.

## Lean-specific processing

```lean
refine ⟨by norm_num, ?_, ?_, ?_⟩
```

uses the structure constructor positionally: it solves the first field immediately and leaves the remaining three as ordered goals. This is positional rather than record syntax and therefore depends on the declaration order of the fields.

```lean
norm_num [GN5]
```

unfolds `GN5` and normalizes powers, multiplication, addition, divisibility, and non-divisibility over concrete natural numbers. `ring` is unnecessary because this is a fully closed numerical computation rather than a polynomial identity with variables.

For the fourth goal, Lean directly solves `¬31^2 ∣ GN5 1 1`. No valuation API or `Nat.factorization` is introduced; finite arithmetic alone certifies the no-lift condition.

## Redundancy and duplication

The computation of `GN5 1 1` duplicates the earlier theorem `GN5_one_one`. It is also repeated twice inside this theorem, once for `dvd_GN5` and once for `noLift`.

The advantage of the current form is that each field is an independent closed numerical goal, making the provider easy to audit. The cost is duplicated expansion work if the definition of `GN5` changes.

## Optimization candidates

1. Reuse `GN5_one_one` via `rw [GN5_one_one]` or `simpa [GN5_one_one]`.
2. Introduce `have hGN : GN5 1 1 = 31 := GN5_one_one` once and share it between `dvd_GN5` and `noLift`.
3. Replace positional syntax with record syntax:

```lean
refine {
  prime := by norm_num
  dvd_GN5 := ?_
  not_dvd_gap := by norm_num
  noLift := ?_
}
```

This would be more robust against field insertion or reordering.
4. For a family of concrete providers, design a helper theorem deriving `CleanGN5Channel g y q` from `GN5 g y = q` and `Nat.Prime q`, with a separate assumption $q∤g$.
5. Compare `norm_num [GN5]` against `rw [GN5_one_one]; norm_num` in proof-term size, execution time, and error locality.

These are unverified proposals. No Lean build was run.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem directly needs only:

- primality testing for natural numbers,
- divisibility and non-divisibility over naturals,
- natural-number powers and concrete arithmetic,
- tactic `refine`,
- tactic `norm_num`.

It does not use `ring`, `omega`, valuations, or `Nat.factorization`. The theorem in isolation could likely use much narrower imports, but the containing `CleanChannel.lean` file also uses coprimality, prime divisibility through powers, and `ring`, so theorem-level and file-level minimal imports are different questions. Import minimization remains unverified.

## Comparator challenge suitability

This theorem makes a small and clear Comparator challenge.

Candidate approaches include:

- the current fully automatic `norm_num [GN5]` proof,
- reusing `GN5_one_one` as a rewrite theorem,
- comparing positional construction with record syntax,
- comparing decidable closed propositions via `decide` against `norm_num`,
- splitting the four fields into separate helper lemmas.

Useful comparison axes are proof-term size, resilience to definition changes, duplicated computation, error locality, and auditability of the provider. The mathematics is elementary, but the theorem is a good lesson in choosing the granularity at which concrete certificates should be reused.

## Next theorem to read

Next is `DkMath.FLT.Five.GN5_one_one_not_fifth_power`.

It passes this theorem to the general consumer `not_fifth_power_GN5_of_clean` and obtains

$$
¬\exists x\in\mathbb{N},\ GN5(1,1)=x^5.
$$

This is the first completed demonstration where a concrete provider connects to an abstract consumer in a single line.

## Sources versus interpretation

The theorem type, proof, declaration order, and immediately following theorem were verified in the generated `DkMath/FLT/Five/CleanChannel.lean` section of `Flt5DkMath/FLT5StandAlone.lean`. The discussion of its global role, duplication, generalization, import minimization, and Comparator alternatives includes explanatory analysis and unverified proposals. Existing PDFs were treated as supplementary narrative context; the Lean source was given priority.
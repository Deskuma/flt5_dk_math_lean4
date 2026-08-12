# 0026 — `branchB_coprime_gap_GN5`

## Declaration

```lean
theorem branchB_coprime_gap_GN5
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    Nat.Coprime (z - y) (GN5 (z - y) y) :=
  coprime_gap_GN5_of_coprime_of_five_not_dvd
    (coprime_gap_y_of_counterexamplePack hPack) hBranch
```

## Lean type

This theorem takes a `CounterexamplePack x y z`, representing a positive primitive FLT5 counterexample candidate, together with the Branch B condition `¬ 5 ∣ z - y`, and returns that the natural-number gap `z - y` is coprime to the fifth-cyclotomic residual kernel `GN5 (z - y) y`.

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  Nat.Coprime (z - y) (GN5 (z - y) y)
```

## Mathematical statement

Set $g=z-y$. From the primitivity and equation contained in the counterexample candidate, one has already obtained

$$
\gcd(g,y)=1.
$$

Branch B additionally assumes

$$
5\nmid g.
$$

By the general theorem from the previous article, these two conditions imply

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1.
$$

Therefore, in the concrete coordinates,

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1.
$$

## Role in the complete proof

This is the Branch-B-specific connection API that completely separates the two factors in the fifth-power factorization

$$
z^5-y^5=(z-y)GN5(z-y,y).
$$

The later theorems `fifth_power_factor_split` and `branchB_fifth_power_factor_split` use this coprimality to show that if the product is a fifth power, then each factor is itself a fifth power.

The present theorem performs no new prime-divisor analysis. It is a boundary-layer theorem applying the general result from the previous article to the concrete gap coordinates derived from `CounterexamplePack`.

## Direct dependencies

1. `CounterexamplePack`
   - Packages positivity of `x,y,z`, `Nat.Coprime x y`, and the equation `x^5+y^5=z^5`.
2. `GN5`
   - The homogeneous degree-four residual kernel obtained after removing the gap from a fifth-power difference.
3. `coprime_gap_y_of_counterexamplePack`
   - Supplies `Nat.Coprime (z-y) y` from `hPack`.
4. `coprime_gap_GN5_of_coprime_of_five_not_dvd`
   - Derives `Nat.Coprime g (GN5 g y)` from `Nat.Coprime g y` and `¬ 5 ∣ g`.

## Proof flow

The proof is completed by a single function application.

1. `coprime_gap_y_of_counterexamplePack hPack` gives

$$
\gcd(z-y,y)=1.
$$

2. `hBranch` directly gives

$$
5\nmid z-y.
$$

3. Pass these two facts to `coprime_gap_GN5_of_coprime_of_five_not_dvd`.
4. Lean infers `g := z-y` and `y := y` from the types and returns the goal directly.

## Lean-specific processing

### Implicit-argument inference

The variables `g` and `y` of the general theorem are inferred from the type of

```lean
coprime_gap_y_of_counterexamplePack hPack
```

namely `Nat.Coprime (z-y) y`. No explicit `g := z-y` annotation and no `simpa` are required.

### Term proof

The proof is written in term style without a `by` block. Since the result type of the general theorem is definitionally identical to the target, no rewriting or tactic invocation is necessary.

### Safety around natural-number subtraction

Although the declaration contains `z-y`, it does not directly handle positivity of the subtraction or the proof of `y≤z`. Those issues were already discharged inside `coprime_gap_y_of_counterexamplePack`. This abstraction isolates the present theorem from the technical details of truncated subtraction on natural numbers.

## Redundancy and duplication

There is no computational duplication in the proof body. It is a minimal wrapper connecting a provider to a general theorem.

From a purely logical perspective, callers could inline the same two-lemma composition. The declaration is still worth keeping because it gives a name to a principal Branch B invariant and makes the intent of later proofs explicit.

## Optimization candidates

1. The current term proof is essentially minimal, leaving no meaningful proof-performance optimization.
2. The argument name `hBranch` clearly identifies the Branch B condition and should be retained.
3. If Branch B assumptions are later packaged into a structure, this theorem could become a method or namespace API for that structure. This is an unverified design proposal.
4. The general theorem has a long name, but introducing a local alias would provide little benefit because it appears only once here.

## Required Mathlib imports and import optimization

The standalone repository artifact uses `import Mathlib`, so the minimal import set for this declaration alone is not established by the source.

The theorem itself directly needs only natural numbers, divisibility, `Nat.Coprime`, and the preceding DkMath declarations. Any actual import audit should inspect the imports of the individual `Reduction.lean` module. Natural-number gcd, coprimality, and divisibility modules are plausible candidates for replacing the umbrella import, but this remains unverified because no Lean build was run.

## Comparator challenge suitability

This theorem is suitable for a small Comparator challenge, although the focus would be API composition and implicit inference rather than mathematical difficulty.

### Proposed task

Prove the following goal in one line or with a short term proof.

```lean
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
⊢ Nat.Coprime (z - y) (GN5 (z - y) y)
```

Possible variants to compare are:

1. The current term-style composition.
2. A `by exact ...` version.
3. A version with explicit implicit arguments.
4. A version that re-expands the common-prime contradiction instead of reusing the general theorem.

Evaluation should consider not only brevity but also dependency clarity, maintainability, reuse of the general theorem, and avoidance of duplicated arithmetic reasoning.

## Verified facts and interpretation

The declaration type, proof body, direct dependencies, and later use as input to `fifth_power_factor_split` were verified in the repository's Lean source. The proposed minimal imports and possible Branch B structure are unverified design suggestions.

## Next theorem to read

```lean
DkMath.FLT.Five.fifth_power_factor_split
```

This general separation theorem proves that if the product of two coprime natural numbers is a fifth power, then each factor is a fifth power. It is the core API that converts the Branch B coprimality established here into a fifth-power normal form.
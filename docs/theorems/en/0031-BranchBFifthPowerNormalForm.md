# 0031 — `BranchBFifthPowerNormalForm`

## Lean type

```lean
structure BranchBFifthPowerNormalForm
    (x y z a b : ℕ) : Prop where
  pack : CounterexamplePack x y z
  branchB : ¬ 5 ∣ z - y
  gap_eq : z - y = a ^ 5
  GN_eq : GN5 (a ^ 5) y = b ^ 5
  x_eq : x = a * b
  z_eq : z = y + a ^ 5
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_y : Nat.Coprime a y
  coprime_a_b : Nat.Coprime a b
  coprime_b_y : Nat.Coprime b y
  five_not_dvd_a : ¬ 5 ∣ a
```

`BranchBFifthPowerNormalForm x y z a b` packages a Branch-B FLT5 counterexample candidate together with the fifth-power roots `a` and `b`, their positivity, coprimality, and exclusion of the exceptional prime into a single `Prop` structure.

## Mathematical statement

An inhabitant of this structure simultaneously proves the following data.

$$
x^5+y^5=z^5,\qquad 5\nmid z-y
$$

Together with

$$
z-y=a^5,\qquad GN5(a^5,y)=b^5,\qquad x=ab,\qquad z=y+a^5
$$

and moreover

$$
a>0,\qquad b>0,\qquad \gcd(a,y)=\gcd(a,b)=\gcd(b,y)=1,\qquad 5\nmid a
$$

The `pack` field retains the positive primitive counterexample candidate, while the remaining fields fix the normal form needed after Branch-B fifth-power separation.

## Role in the complete proof

This declaration does not prove a new theorem. It is a **receiver interface** for downstream proofs. It gathers the facts separately obtained in the Reduction layer into one packet that the square/golden bridge and subsequent arguments can consume reliably.

In particular, later code can use projections such as `normal.gap_eq`, `normal.GN_eq`, and `normal.coprime_a_b` directly instead of reconstructing the original factorization repeatedly. This makes the boundary between the elementary number-theoretic Branch-B reduction and the golden-integer or square-world arguments explicit.

## Direct dependencies

The directly visible dependencies are:

- `CounterexamplePack`, used as the type of the `pack` field.
- `GN5`, whose residual value is fixed as a perfect fifth power by `GN_eq`.
- `Nat.Coprime`, used for the three pairwise coprimality fields.
- Natural-number powers, subtraction, divisibility, and positivity.

Because this declaration is a structure, it does not call the previous theorem `coprime_GN5_y_of_coprime` in a proof body. However, the immediately following provider `exists_branchB_fifthPowerNormalForm` uses that result to construct `coprime_b_y`. In this sense, the previous article supplies a dependency needed to inhabit this structure.

## Construction flow

The fields form four layers.

1. Input layer: `pack` and `branchB` retain the original candidate and branch condition.
2. Fifth-power normal-form layer: `gap_eq` and `GN_eq` project both factors to fifth powers.
3. Reconstruction layer: `x_eq` and `z_eq` recover the original coordinates from `a`, `b`, and `y`.
4. Nondegeneracy and primitivity layer: positivity, three coprimality facts, and `5 ∤ a` are retained.

This ordering follows the dependency direction from source data, through normal form and coordinate reconstruction, to arithmetic invariants.

## Lean-specific processing

Because this is declared as `structure ... : Prop`, it is a proof packet rather than computational data and is subject to proof irrelevance. Lean automatically generates named projections for each field.

A significant design choice is that `gap_eq` has right-hand side `a ^ 5`, while `GN_eq` is stated as `GN5 (a ^ 5) y = b ^ 5`. The structure does not retain `GN5 (z-y) y` directly; it normalizes the gap coordinate in advance and thereby reduces downstream rewriting.

Some fields are theoretically derivable again from `pack` and `branchB`. Retaining them prioritizes a convenient downstream API over logical minimality.

## Redundancy and duplication

- `z_eq` can be rederived from `gap_eq` and `pack`, after establishing `y ≤ z`.
- `five_not_dvd_a` can be rederived from `branchB` and `gap_eq`.
- `a_pos` and `b_pos` can also be rederived from `pack`, `gap_eq`, and `x_eq`.
- `coprime_a_b` and `coprime_b_y` follow from the preceding factor-splitting and congruence arguments, but they are cached because later proofs use them frequently.

Thus the structure is logically redundant but can be read as an intentional normal-form cache for proof engineering.

## Optimization candidates

1. Keeping the structure unchanged as a receiver interface is the safest option.
2. One could separate a minimal `BranchBFifthPowerCore` from an extended structure carrying derived facts. This may, however, increase projection paths and complicate downstream proofs.
3. `x_eq` and `z_eq` could be considered as simp lemmas, but any global `[simp]` registration would require auditing to avoid uncontrolled rewriting.
4. Positivity could be represented with a `PNat`-style type, though conversions back to the current natural-number APIs would add cost.

These are design proposals, not changes verified in the current source.

## Required Mathlib imports and import optimization

The confirmed generated standalone artifact uses `import Mathlib`. This structure declaration itself only needs natural numbers, divisibility, powers, `Nat.Coprime`, and the preceding DkMath declarations.

At module granularity, imports might be reducible to `Reduction.lean` plus the relevant Mathlib natural-number divisibility and gcd modules. The individual module import line was not visible in the standalone section inspected here, so this is an unverified import-optimization proposal.

## Comparator challenge suitability

Suitability is high, especially as a structure-design or type-equivalence challenge rather than a proof-search challenge.

Possible tasks:

- Define a minimal structure with the same mathematical content and construct conversions in both directions.
- Prove equivalence between a version storing `GN5 (z-y) y = b^5` and the current normalized version.
- Remove redundant fields and reconstruct `z_eq`, `five_not_dvd_a`, and positivity.

Useful comparison criteria include rewrite stability, dependency count, and concision at downstream use sites.

## Verified facts and proposals

The structure declaration, field order, role in the NormalForm layer, and the name of the immediately following provider were verified in the repository Lean source. Splitting the structure, adding simp attributes, and shrinking imports are unverified proposals.

## Next theorem to read

The next declaration is

```lean
theorem exists_branchB_fifthPowerNormalForm
```

This provider constructs `a` and `b` from a `CounterexamplePack` and the Branch-B condition, then fills every field of the receiver interface presented in this article.

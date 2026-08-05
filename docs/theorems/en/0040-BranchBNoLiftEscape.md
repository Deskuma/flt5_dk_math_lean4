# 0040 — `BranchBNoLiftEscape`

## 1. Declaration

```lean
/-- Unbundled no-lift escape data for every Branch-B counterexample candidate. -/
abbrev BranchBNoLiftEscape : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ GN5 (z - y) y ∧
      ¬ q ∣ z - y ∧
      ¬ q ^ 2 ∣ GN5 (z - y) y
```

> Note: the type above was reconstructed from the preceding article, the catalogue's dependency order, the name of the following adapter, and the repository material describing the bundled/unbundled correspondence. GitHub code search temporarily returned HTTP 502, so the individual source lines could not be fetched again in this run. The exact conjunction association and source-comment wording therefore remain audit items, while the mathematical content and API role are confirmed.

## 2. Lean Type

`BranchBNoLiftEscape` is an abbreviation for a proposition. For arbitrary natural numbers `x y z`, it receives:

- `CounterexamplePack x y z`;
- the Branch-B condition `¬ 5 ∣ z - y`;

and returns a natural number `q` together with four conditions:

```lean
Nat.Prime q
q ∣ GN5 (z - y) y
¬ q ∣ z - y
¬ q ^ 2 ∣ GN5 (z - y) y
```

The previous `BranchBCleanGN5ChannelProvider` bundled these conditions in `CleanGN5Channel`; this declaration returns the same information as a conjunction.

## 3. Mathematical Statement

Suppose a primitive positive Fermat counterexample candidate

$$
x^5+y^5=z^5
$$

belongs to Branch B:

$$
5\nmid z-y.
$$

Then there exists a prime $q$ such that

$$
q\mid GN5(z-y,y),
$$

$$
q\nmid z-y,
$$

$$
q^2\nmid GN5(z-y,y).
$$

The last condition says that the $q$-adic valuation does not lift to at least two. Together, the conditions say that $q$ occurs once on the cyclotomic side and not on the gap side, producing a clean prime channel.

## 4. Role in the Overall Proof

This declaration is the **unbundled kernel** that supplies a local prime obstruction from a Branch-B counterexample candidate.

Its relation to the preceding declaration is:

- `BranchBNoLiftEscape` returns primality and three divisibility conditions as a conjunction;
- `BranchBCleanGN5ChannelProvider` returns the same four conditions bundled as `CleanGN5Channel`;
- `branchBCleanGN5ChannelProvider_of_noLiftEscape` connects the two forms.

Thus the declaration separates the mathematical no-lift argument from the packaging required by the downstream API.

## 5. Direct Dependencies

### 5.1 `CounterexamplePack`

This input package stores positivity, primitiveness, and the Fermat equation. The declaration does not unfold its fields in the type.

### 5.2 `GN5`

This is the cyclotomic factor in the fifth-power difference:

$$
(g+y)^5-y^5=g\,GN5(g,y).
$$

Here the gap is specialized to $g=z-y$.

### 5.3 `Nat.Prime` and Divisibility

The witness `q` is a natural number, and primality is returned separately as `Nat.Prime q`. The remaining conditions are natural-number divisibility propositions.

### 5.4 The Branch-B Condition

`¬ 5 ∣ z-y` selects the branch in which the gap is not divisible by five. The no-lift prime supply is scoped to this branch.

## 6. Proof Flow

Because this is an `abbrev`, the declaration has no proof body. A proof implementing the interface would conceptually proceed as follows.

1. Receive `hPack : CounterexamplePack x y z`.
2. Receive `hBranch : ¬ 5 ∣ z-y`.
3. Select a prime-factor candidate `q` of `GN5 (z-y) y`.
4. Prove that `q` is prime.
5. Prove `q ∣ GN5 (z-y) y`.
6. Use coprimality of the gap and cyclotomic factor, or an equivalent argument, to prove `¬ q ∣ z-y`.
7. Use the no-lift argument to prove `¬ q^2 ∣ GN5 (z-y) y`.
8. Return `⟨q, hPrime, hDvd, hNotGap, hNotSq⟩`.

The declaration fixes the result type without itself providing steps 3–7.

## 7. Lean-Specific Processing

### 7.1 Transparency of `abbrev`

Given `hEscape : BranchBNoLiftEscape`, one can normally write:

```lean
hEscape hPack hBranch
```

without explicitly unfolding the abbreviation.

### 7.2 Right-Associative Conjunction

Lean's `∧` associates to the right. Conceptually, the returned proposition is:

```lean
Nat.Prime q ∧
  (q ∣ GN5 (z-y) y ∧
    (¬ q ∣ z-y ∧
      ¬ q^2 ∣ GN5 (z-y) y))
```

`rcases` can nevertheless destruct all four proofs at once:

```lean
rcases hEscape hPack hBranch with
  ⟨q, hq, hqGN, hqGap, hqSq⟩
```

### 7.3 Negation as a Function Type

Both `¬ q ∣ z-y` and `¬ q^2 ∣ GN5 ...` are functions from a divisibility proof to `False`.

### 7.4 Two Layers of Packaging

The outer layer is `∃ q`; the inner layer is a conjunction. The following adapter extracts the witness and builds a `CleanGN5Channel` structure from the four proofs.

## 8. Redundancy and Duplication

This declaration has nearly the same logical content as `BranchBCleanGN5ChannelProvider`. The difference is representation:

- bundled: `CleanGN5Channel ... q`;
- unbundled: a conjunction of four conditions.

The duplication is purposeful. A mathematical no-lift proof is often easier to construct as a conjunction, while consumers benefit from named structure projections. A small adapter separates those concerns.

## 9. Optimization Candidates

### 9.1 Keep Only the Bundled Provider

It would be possible to remove this declaration and use only the bundled provider. That would mix structure construction into the mathematical no-lift proof and blur the boundary between the kernel and API packaging.

### 9.2 Introduce a Dedicated Structure

The four conditions could be stored in a new `BranchBNoLiftEscapeData` structure. That would substantially duplicate `CleanGN5Channel`, so the current unbundled form is lighter.

### 9.3 Normalize Square Divisibility Syntax

If the project mixes `q ^ 2` and `q * q`, applying square-divisibility lemmas may require extra rewriting. A consistent notation could stabilize downstream proofs.

These are design proposals. No Lean build was run in this task.

## 10. Required Mathlib Imports and Import Optimization

The declaration itself needs only a limited Mathlib foundation:

- natural numbers;
- `Nat.Prime`;
- divisibility;
- powers;
- existential quantification and conjunction.

The project declarations that must be visible are at least:

- `CounterexamplePack`;
- `GN5`.

The exact module import lines could not be fetched again because GitHub code search was temporarily unavailable. It is plausible that only the local modules exporting `CounterexamplePack` and `GN5` are required, allowing a broad `Mathlib` import to be narrowed. Determining the exact minimal import set would require module-level Lean verification, which is outside this task.

## 11. Comparator Challenge Suitability

This declaration is well suited to a bundled-versus-unbundled API challenge.

### Challenge A — Reconstruct the Type

Reconstruct the `BranchBNoLiftEscape` proposition from a natural-language specification.

### Challenge B — Repackaging Adapter

Given the unbundled witness, prove:

```lean
∃ q, CleanGN5Channel (z-y) y q
```

with a short Lean proof.

### Challenge C — Robustness Under Conjunction Reordering

Change the order of the four conditions and compare the effect on existing `rcases` and constructor proofs.

### Challenge D — API Design Comparison

Implement the declaration as an `abbrev`, a `def`, and a structure, then compare transparency, readability, and reuse.

## 12. Confirmed Facts and Inferences

Confirmed:

- the Japanese and English series exists through article 0039;
- this declaration is explicitly next in dependency order;
- it is the unbundled no-lift kernel;
- the next adapter is `branchBCleanGN5ChannelProvider_of_noLiftEscape`;
- it carries the same local data as the preceding bundled provider.

Not reverified because of the temporary search failure:

- the exact parenthesization of the conjunction in the individual Lean source;
- the verbatim source comment;
- the exact imports of the individual module.

The mathematical statement, declaration role, and Japanese/English structure follow the existing articles and catalogue. The three items above should be audited when code search recovers.

## 13. Next Declaration

The next declaration is:

```lean
DkMath.FLT.Five.branchBCleanGN5ChannelProvider_of_noLiftEscape
```

It destructs the witness and four proofs returned by `BranchBNoLiftEscape`, repackages them into a `CleanGN5Channel` structure, and thereby constructs `BranchBCleanGN5ChannelProvider`.

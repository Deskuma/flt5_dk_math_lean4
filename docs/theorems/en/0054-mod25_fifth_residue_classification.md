# 0054 — `mod25_fifth_residue_classification`

## 1. Lean declaration

```lean
/-- The finite mod-25 residue obstruction used by the signed routing theorem. -/
private theorem mod25_fifth_residue_classification :
    ∀ x y z : Fin 25,
      (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
      ¬ 5 ∣ x.1 →
      5 ∣ y.1 ∨ 5 ∣ z.1 := by
  -- native_decide
  decide +kernel
```

The declaration is located inside the `DkMath.FLT.Five` namespace, but because it is `private`, it is not a public API declaration intended to be referenced by a stable fully qualified name outside the file. This article uses the source-level name `mod25_fifth_residue_classification`.

## 2. Lean type

```lean
∀ x y z : Fin 25,
  (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
  ¬ 5 ∣ x.1 →
  5 ∣ y.1 ∨ 5 ∣ z.1
```

The variables `x y z` are not arbitrary natural numbers but elements of `Fin 25`, whose values lie between $0$ and $24$. The projection `.1` extracts the underlying natural-number value.

## 3. Mathematical statement

Let $x,y,z\in\{0,1,\dots,24\}$ be residue representatives modulo $25$. If

$$
x^5+y^5\equiv z^5\pmod{25}
$$

and

$$
5\nmid x,
$$

then

$$
5\mid y
\quad\text{or}\quad
5\mid z.
$$

This is not a direct proof of a general theorem over infinitely many natural numbers. It is a complete finite classification of the $25^3=15625$ residue triples modulo $25$.

## 4. Role in the whole proof

The previous articles obtain $5\nmid x$ from a Branch-B counterexample candidate. Routing into signed Branch A then requires the dichotomy

$$
5\mid y
\quad\text{or}\quad
5\mid z.
$$

```text
Fermat5Equation x y z
        +
      5 ∤ x
        ↓ reduce modulo 25
mod25_fifth_residue_classification
        ↓
   5 ∣ y  ∨  5 ∣ z
        ↓
differenceGap / sumGap routing
```

This theorem is the finite arithmetic kernel of that route. The following public theorem `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x` reduces natural numbers to `Fin 25`, invokes this classification, and lifts the result back to divisibility over natural numbers.

## 5. Direct dependencies

The declaration has no direct dependency on repository-specific theorems. Its main ingredients are:

- `Fin 25`
- fifth powers of natural values, `x.1 ^ 5`
- remainder `% 25`
- divisibility `5 ∣ x.1`
- disjunction `Or`
- kernel-based decision by `decide +kernel`

Mathematically it encodes a classification of fifth-power residues modulo $25$, but it does not expose a separate residue table or supporting lemma.

## 6. Proof flow

The proof term is one line.

1. `Fin 25` makes the three-variable search space finite.
2. Equality, divisibility, negation, and disjunction are all decidable.
3. `decide +kernel` normalizes the proposition for every input and produces a proof term.
4. The commented line `-- native_decide` appears to record an alternative faster evaluation strategy, while the active proof stays within kernel reduction.

## 7. Lean-specific processing

### 7.1 `private theorem`

A `private` declaration is an implementation helper local to the source file rather than part of the external module API. The next public theorem wraps it in a stable theorem over natural numbers.

### 7.2 `Fin 25` and `.1`

An element of `Fin 25` contains both a value and a proof that the value is less than $25$. The projection `x.1` extracts the value. Because the range is part of the type, the decision procedure can enumerate all elements.

### 7.3 `decide +kernel`

`decide` evaluates the proposition's `Decidable` instance and returns a proof. The `+kernel` annotation explicitly uses kernel reduction and does not widen the proof trust boundary to external native code generation.

### 7.4 Explicit `% 25`

Although `x.1` itself is already less than $25$, fifth powers and their sum need not be. Therefore the equation still requires explicit reduction modulo $25$.

### 7.5 The disjunction is not exclusive

The conclusion is `5 ∣ y.1 ∨ 5 ∣ z.1`. It does not rule out the possibility that both are divisible by five. The later routing only needs at least one constructible orientation.

## 8. Redundancy and duplication

Because the proposition is finite, the proof is extremely short. The mathematical explanation, however, is hidden inside computation rather than visible in the proof script, so comments and downstream documentation carry most of the explanatory burden.

The projections `.1` are repeated for all three variables, but this is natural when using values of `Fin`. Defining a separate fifth-power residue map could shorten the expression, at the cost of expanding the helper API.

The comment `-- native_decide` is not executable and could be removed from a minimal finished source. It may still be useful as a record of a proof-performance alternative.

## 9. Optimization candidates

1. For greater mathematical transparency, explicitly classify fifth-power residues modulo $25$ and derive the theorem from that table.
2. If elaboration or proof-checking time becomes significant, reconsider `native_decide`, while keeping the intended trust boundary and CI environment explicit.
3. A local fifth-power map on `Fin 25` could reduce syntactic repetition, but would likely be over-abstraction for a single helper theorem.
4. One could seek a parameterized analogue for a prime $p$ modulo $p^2$, but the present statement depends on the special residue structure at $p=5$, so additional hypotheses would be required.
5. Remove `private` only if direct reuse outside the file becomes necessary. The following natural-number theorem currently provides the appropriate public boundary.

## 10. Required Mathlib imports

The generated standalone source on the target branch uses:

```lean
import Mathlib
```

In isolation, this theorem needs support for `Fin`, natural-number divisibility, remainders, powers, and decision procedures. Candidate import areas include:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
```

The exact minimal import set, especially for the `decide +kernel` syntax and all required instances, can only be confirmed by reducing imports and building the split source module. The list above is therefore partly conjectural.

At file level, neighboring theorems in `SignedBranchA.lean` also use `norm_num`, `interval_cases`, and natural-number remainder lemmas. Import optimization should therefore audit the whole module rather than this private theorem alone.

## 11. Comparator challenge suitability

Yes. It is well suited to comparing computational and explanatory proofs.

### Challenge proposal

Prove the following in two ways:

```lean
∀ x y z : Fin 25,
  (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
  ¬ 5 ∣ x.1 →
  5 ∣ y.1 ∨ 5 ∣ z.1
```

- Method A: finite decision using `decide +kernel` or `native_decide`.
- Method B: explicit classification of fifth-power residue classes.

Compare proof time, proof-term size, readability, trust boundary, and reuse for other moduli.

## 12. Evidence versus inference

The declaration name, `private` modifier, complete type, source comment, proof by `decide +kernel`, and direct use by the following public theorem were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The exact section names used for this lemma in the existing Japanese and English PDFs, and the exact minimal imports of the split file `DkMath/FLT/Five/SignedBranchA.lean`, were not directly verified in this run. Import-minimization remarks are explicitly presented as candidates rather than established facts.

## 13. Next theorem to read

Next, lift this finite classification to a public theorem over natural numbers:

```lean
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z := by
  ...
```

After that, `signedBranchA_normalForm_of_branchB` uses the dichotomy to construct either a difference-gap or a sum-gap `SignedBranchANormalForm`.
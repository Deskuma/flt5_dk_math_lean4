# 0052 — `SignedBranchAOrientation`

## 1. Lean declaration

```lean
/-- The two exceptional five-adic orientations of an exponent-five equation. -/
inductive SignedBranchAOrientation (u v w : ℕ) : Prop
  | differenceGap
      (five_dvd_left : 5 ∣ u)
      (five_dvd_gap : 5 ∣ w - v) :
      SignedBranchAOrientation u v w
  | sumGap
      (five_dvd_result : 5 ∣ w)
      (five_dvd_sum : 5 ∣ u + v) :
      SignedBranchAOrientation u v w
```

The fully qualified name is `DkMath.FLT.Five.SignedBranchAOrientation`.

## 2. Lean type

```lean
SignedBranchAOrientation (u v w : ℕ) : Prop
```

This is a proposition-valued inductive type carrying proof data, with two constructors.

```lean
SignedBranchAOrientation.differenceGap
  : 5 ∣ u → 5 ∣ w - v → SignedBranchAOrientation u v w

SignedBranchAOrientation.sumGap
  : 5 ∣ w → 5 ∣ u + v → SignedBranchAOrientation u v w
```

## 3. Mathematical statement

`SignedBranchAOrientation u v w` states that, when an exponent-five candidate is routed into the later common five-adic descent, one of the following two orientations holds.

1. Difference orientation:

$$
5\mid u,
\qquad
5\mid(w-v).
$$

2. Sum orientation:

$$
5\mid w,
\qquad
5\mid(u+v).
$$

Thus this declaration does not prove a single arithmetic identity. It is a sum-like logical interface classifying the exceptional five-adic situation into two normalized forms.

## 4. Role in the whole proof

By the preceding articles, after the Branch B condition yields $5\nmid x$, a modulo-five analysis of the Fermat equation gives $5\mid y$ or $5\mid z$. Each case is packaged into this inductive type as follows.

```text
5 ∣ y
  → swapped pack
  → 5 ∣ y and 5 ∣ z - x
  → differenceGap

5 ∣ z
  → original pack
  → 5 ∣ z and 5 ∣ x + y
  → sumGap
```

The next declaration, `SignedBranchANormalForm`, combines a `CounterexamplePack` with this orientation in one structure. Consequently, the later five-adic and golden-order descent does not handle the original asymmetric Branch B input directly; it only performs case analysis on these two constructors.

## 5. Direct dependencies

The declaration itself depends only on standard natural-number arithmetic.

- `ℕ`
- divisibility `Dvd.dvd`, notation `∣`
- natural-number addition `u + v`
- natural-number subtraction `w - v`

No repository-specific prior definition or theorem appears in the declaration body. In actual constructor production, however, the following previously documented results are used directly.

- `CounterexamplePack.swap`
- `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y`
- `five_dvd_x_add_y_of_fermat5_of_five_dvd_z`

## 6. Construction flow

Because this is an inductive definition, there is no proof script; the two formation rules are the definition itself.

- `differenceGap` takes $5\mid u$ and $5\mid(w-v)$.
- `sumGap` takes $5\mid w$ and $5\mid(u+v)$.
- Both produce the same conclusion, `SignedBranchAOrientation u v w`.

Users can completely split the two directions with `cases`, `rcases`, constructor patterns, or `induction`.

## 7. Lean-specific processing

### 7.1 `inductive ... : Prop`

Because the inductive type lives in `Prop`, its constructor fields are proof evidence rather than computational data. Case analysis on an orientation introduces the corresponding two divisibility hypotheses into the local context.

### 7.2 Named constructor arguments

`five_dvd_left`, `five_dvd_gap`, `five_dvd_result`, and `five_dvd_sum` are constructor field names. They improve readability of generated recursors and pattern matches.

### 7.3 Truncated natural-number subtraction

`w - v` is `Nat.sub`, not integer subtraction. Hence, if `w < v`, then $w-v=0$. In the actual `differenceGap` route, the necessary order comes separately from the `CounterexamplePack` and the Fermat equation. The declaration itself carries no order assumption, leaving that semantic invariant to the `pack` field of the later normal form.

### 7.4 Not an exclusive disjunction

This inductive type does not state “exactly one.” If both pairs of divisibility conditions hold, two different proof terms can be built for the same triple. The later proof needs existence of at least one descent entrance, not exclusivity.

## 8. Redundancy and duplication

Logically, the same proposition could be written as follows.

```lean
(5 ∣ u ∧ 5 ∣ w - v) ∨ (5 ∣ w ∧ 5 ∣ u + v)
```

Therefore the custom inductive type is redundant at the level of bare propositional content. However, the constructor names `differenceGap` and `sumGap` preserve the mathematical meaning and provide a stable API for later branches. This duplication is intentional semantic packaging.

## 9. Optimization candidates

1. If constructor-specific lemmas proliferate later, projection-style lemmas or simp lemmas for case analysis could be added.
2. To close the meaning of natural subtraction completely, one could add `v ≤ w` to `differenceGap`, or define the difference over integers. In the current architecture this would likely duplicate order information already carried by `CounterexamplePack`.
3. Replacing the custom type with an ordinary disjunction would reduce declaration count but lose named branches and documentation clarity. The current design better serves the proof architecture.
4. The constructor names are already descriptive; abbreviation would bring little benefit.

## 10. Required Mathlib imports

The generated standalone source uses `import Mathlib`. The declaration itself requires only natural numbers, addition, subtraction, divisibility, and basic inductive syntax, so importing all of Mathlib is excessive.

The exact import line of the split source file `DkMath/FLT/Five/SignedBranchA.lean` was not obtained in this run. The following is therefore only a candidate for declaration-level minimization.

```lean
import Mathlib.Data.Nat.Basic
```

The later theorems in the same module use `congrArg`, remainders, `interval_cases`, and `norm_num`, so the minimum import for the whole file may need to be broader. Declaration-level and module-level import audits should be separated.

## 11. Comparator challenge suitability

Yes, although it is better suited to an API-design challenge than to a proof-completion exercise.

### Challenge proposal

Redesign the following disjunction as a proposition-valued inductive type with two named constructors.

$$
(5\mid u\land5\mid(w-v))
\lor
(5\mid w\land5\mid(u+v)).
$$

Comparison points include:

- proof terms for `Or` versus a custom inductive type;
- readability of later case splits from constructor names;
- recognition that the type does not assert exclusivity;
- awareness of truncated `Nat.sub` semantics.

Its small size and clear objective make it suitable as an introductory-to-intermediate Lean API-design challenge.

## 12. Evidence and explicit conjecture

The declaration name, type, two constructors, divisibility fields, and the immediately following `SignedBranchANormalForm` were confirmed in the generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The exact import list of the split source module and the terminology used for this inductive type in the existing PDFs were not directly verified in this run. Import-minimization remarks are explicitly presented as candidates.

## 13. Next declaration to read

Next comes the following structure.

```lean
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

`SignedBranchANormalForm` combines the counterexample packet with the two-way tag from this article and defines the normalized input consumed by the later common five-adic descent.
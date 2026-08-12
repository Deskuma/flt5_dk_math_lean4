# 0044 — `DkMath.FLT.Five.BranchACondition`

## 1. Declaration

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

This declaration is the first item in `DkMath.FLT.Five.BranchA`. It names the exceptional branch condition in the exponent-five proof.

## 2. Lean type

```lean
BranchACondition : ℕ → ℕ → Prop
```

It takes natural numbers `y` and `z` and states that the natural-number gap `z - y` is divisible by `5`.

## 3. Mathematical statement

$$
BranchACondition(y,z) \iff 5\mid(z-y).
$$

For a positive FLT5 counterexample candidate, earlier results imply $y<z$, so `z-y` is the ordinary positive difference. The definition itself does not assume this order. Since subtraction on `Nat` is truncated, `z<y` implies `z-y=0`, and then the condition is true because every natural number divides zero.

## 4. Role in the proof

The declaration names the complementary side of the Branch B hypothesis

$$
5\nmid(z-y).
$$

Branch B uses coprime separation, fifth-power factor splitting, and clean-channel or no-lift providers. Branch A is exceptional because five divides the gap. The source documentation routes this side through the later signed Branch A layer, exact five-adic normalization, and golden-order descent.

Thus this is a routing predicate rather than a new number-theoretic theorem.

## 5. Direct dependencies

The body directly uses only `ℕ`, natural subtraction, and divisibility. It does not directly mention `CounterexamplePack`, `Fermat5Equation`, or `GN5`; later declarations connect those objects.

## 6. Proof flow

This is a `def`, so there is no proof script:

```text
inputs y, z
  ↓
form z - y
  ↓
state that 5 divides the gap
  ↓
BranchACondition y z
```

## 7. Lean-specific processing

`BranchACondition` returns `Prop`, not `Bool`. Evidence `hA : BranchACondition y z` can be exposed as `5 ∣ z-y` by definitional reduction, `unfold BranchACondition at hA`, or `simpa [BranchACondition] using hA`.

The main subtlety is truncated subtraction on natural numbers. To interpret the expression as a positive difference, a use site should separately obtain `y<z`, normally from `CounterexamplePack` and `right_lt_of_fermat5Equation`.

The numeral `5` is inferred to have type `ℕ`; explicitly the body is `(5 : ℕ) ∣ z-y`.

## 8. Redundancy and duplication

The formula already occurs inside Branch B assumptions as its negation. Naming it is nevertheless useful because it stabilizes the Branch A API, makes later theorem types readable, exposes the routing contract, and isolates consumers from the low-level predicate. It is an intentional semantic wrapper.

## 9. Optimization candidates

Changing `def` to `abbrev` would increase transparency, but the current `def` is appropriate for a public branch predicate with controlled unfolding.

A stronger auxiliary predicate could include order:

```lean
def PositiveBranchACondition (y z : ℕ) : Prop :=
  y < z ∧ 5 ∣ z - y
```

This may prevent misuse of truncated subtraction, but it would duplicate an order fact already derived from the counterexample package. Later use sites should be audited before adding it.

## 10. Mathlib imports

The generated standalone source uses `import Mathlib`. This declaration alone needs only basic natural-number subtraction and divisibility, so the full import is larger than necessary.

The exact import line of the original split `BranchA.lean` file was not available from the standalone artifact in this run. A module near `Mathlib.Data.Nat.Basic` may suffice for this definition alone, but the following `BranchARefuter` also requires the project module defining `CounterexamplePack`. Import optimization should therefore be performed for the whole source module. This is an audit proposal, not a verified minimal import claim.

## 11. Comparator challenge suitability

The declaration is suitable for compact exercises about definitional unfolding and truncated subtraction.

```lean
example {y z : ℕ} (h : BranchACondition y z) : 5 ∣ z - y := by
  exact h
```

```lean
example {y z : ℕ} (h : 5 ∣ z - y) : BranchACondition y z := by
  exact h
```

A stronger challenge is to prove that the condition holds when `z<y`, using `Nat.sub_eq_zero_of_le` and divisibility of zero.

## 12. Evidence and qualifications

Verified facts are the declaration name, parameters, type, body, its position as the first declaration of `BranchA.lean`, the immediately following `BranchARefuter`, and the source description of the later signed five-adic and golden-order route. Only the original split module's exact import line remains unverified.

## 13. Next declaration

The next declaration is

```lean
DkMath.FLT.Five.BranchARefuter
```

It is the reusable receiver contract taking `CounterexamplePack x y z` and `BranchACondition y z` to `False`.
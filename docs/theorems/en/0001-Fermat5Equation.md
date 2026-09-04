# 0001 — `Fermat5Equation`

## 1. Exhibit

```lean
namespace DkMath.FLT.Five

/-- The equation `x^5 + y^5 = z^5` over natural numbers. Positivity is deliberately
kept outside this definition and supplied by `CounterexamplePack` or `FLT5Target`. -/
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5

end DkMath.FLT.Five
```

Its fully qualified name is:

```lean
DkMath.FLT.Five.Fermat5Equation
```

Its Lean type is the following function type:

```lean
ℕ → ℕ → ℕ → Prop
```

It receives three natural numbers and returns the proposition that they satisfy the exponent-five Fermat equation.

## 2. Mathematical statement

`Fermat5Equation x y z` is simply a named form of the equality

$$
x^5+y^5=z^5.
$$

The definition itself asserts neither existence nor nonexistence of solutions. It also contains no positivity assumptions, coprimality assumptions, or ordering relations on `x`, `y`, and `z`.

The source comment states this separation explicitly: positivity is supplied later by `CounterexamplePack` or by the final entry-point layer through `FLT5Target`.

## 3. Role in the complete proof

This declaration is the minimal entry point of the FLT5 formalization.

It separates two kinds of information used throughout the proof:

1. the equation itself;
2. additional normalization conditions such as positivity and primitiveness.

By naming the equation independently, later lemmas can receive only the assumptions they actually need. The immediately following foundational declarations use it as follows:

- `fifth_sub_eq_of_add_eq` receives only the equation;
- `right_lt_of_fermat5Equation` receives the equation and `0 < x`;
- `gap_pos_of_fermat5Equation` also receives the equation and `0 < x`;
- `CounterexamplePack` bundles the equation with positivity and `Nat.Coprime x y`.

Thus this definition is the common interface used before the development moves to gap coordinates, `GN5` factorization, the 5-adic split, the golden integer order, and infinite descent.

## 4. Direct dependencies

It depends on no earlier repository-specific declaration. It uses only basic Lean/Mathlib notions:

- `ℕ`, the natural-number type;
- `Nat.pow` and the power notation `^`;
- natural-number addition `+`;
- equality `=`;
- the proposition universe `Prop`.

Conceptually, the dependency graph begins as follows:

```text
Nat, Nat.pow, Nat.add, Eq, Prop
  └─ Fermat5Equation
       ├─ CounterexamplePack
       ├─ fifth_sub_eq_of_add_eq
       ├─ right_lt_of_fermat5Equation
       └─ gap_pos_of_fermat5Equation
```

## 5. Construction flow

There is no tactic proof in this declaration. It merely wraps the right-hand proposition in a named predicate.

1. Receive `x y z : ℕ`.
2. Form the fifth power of each variable.
3. Add the first two fifth powers.
4. Return the proposition that this sum equals `z ^ 5`.

Because it is a `def`, later proofs can expose the original equality with `unfold Fermat5Equation`.

## 6. Lean-specific processing

### 6.1 Wrapping a proposition with `def`

Mathematically this is only an equality, but in Lean the name establishes an API boundary. Later declarations can accept `Fermat5Equation x y z` instead of repeating the raw equality in every signature.

### 6.2 Keeping positivity outside the definition

Because `ℕ` contains `0`, this definition alone does not exclude trivial zero cases. This is deliberate separation of responsibilities rather than an omission. Positivity is added by `CounterexamplePack` and related entry-point structures.

### 6.3 Definitional unfolding

The later theorems `fifth_sub_eq_of_add_eq` and `right_lt_of_fermat5Equation` begin with:

```lean
unfold Fermat5Equation at hEq
```

This turns the named predicate back into a raw natural-number equality so that `omega` and power-order lemmas can process it.

## 7. Redundancy and duplication

The definition itself contains no meaningful redundancy.

The public theorem `PNat.pow_add_pow_ne_pow_five` converts an equality over `ℕ+` back to an equality over `ℕ` with `Subtype.ext_iff.mp` before invoking the final internal theorem. This is not duplication competing with `Fermat5Equation`; it is boundary processing between the positive-natural-number API and the internal natural-number API.

As an audit candidate, raw occurrences of

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

elsewhere in the repository might sometimes be replaced by `Fermat5Equation`. This is only a design possibility. Raw equalities can be preferable for rewriting and automation, so a mechanical global replacement would not be justified.

## 8. Optimization candidates

### 8.1 Do not mark the definition `[simp]`

If simplification unfolded it everywhere, the named API boundary would largely disappear and goals could become unnecessarily larger. The present design, unfolding only where needed, is clearer.

### 8.2 Put any general-exponent abstraction in a separate layer

One could introduce a general predicate such as:

```lean
def FermatEquation (n x y z : ℕ) : Prop :=
  x ^ n + y ^ n = z ^ n
```

However, this repository is intentionally specialized to exponent five, and the later `GN5`, 5-adic valuation, and golden-order arguments are all exponent-five-specific. Generalization at this point could add abstraction without reducing proof duplication. It would become worthwhile only if a shared FLT foundation were developed in another module.

### 8.3 `abbrev` is not preferable here

Because the declaration is a mere alias, `abbrev` may appear tempting. Nevertheless, an explicit `def` better preserves a controlled proof API boundary and intentional unfolding behavior.

## 9. Mathlib import audit

The generated standalone file imports:

```lean
import Mathlib
```

This declaration alone needs only natural numbers, powers, addition, equality, and `Prop`, so `import Mathlib` is much broader than necessary when this one declaration is considered in isolation.

Unverified minimization possibilities include:

- the standard Lean prelude may already suffice;
- otherwise, a small Mathlib module providing basic natural-number operations may suffice.

The standalone file, however, combines many generated source modules. Its global imports are determined by all later algebraic, number-theoretic, and tactic requirements. Therefore this single declaration is not a reason to remove `import Mathlib` from the standalone artifact.

The exact minimum import must be tested by isolating the declaration in a separate file and running Lean. No build was performed in this museum pass, so these remain candidates rather than verified facts.

## 10. Comparator challenge suitability

Because the declaration contains no proof, it is not naturally suited to an ordinary proof-comparison challenge.

It can nevertheless support small Lean API challenges.

### Challenge A — Wrapping and unfolding

```lean
theorem fermat5Equation_iff (x y z : ℕ) :
    Fermat5Equation x y z ↔ x ^ 5 + y ^ 5 = z ^ 5 := by
  rfl
```

Possible submissions could compare `rfl`, `simp [Fermat5Equation]`, and a deliberately verbose `constructor` proof.

### Challenge B — API design comparison

Compare three designs: a `def`, an `abbrev`, and direct use of the raw equality. Evaluate goal display, unfolding control, and readability of downstream theorem signatures.

The verdict is therefore **limited suitability**. It is useful as an API-design comparator rather than as a mathematically difficult proof challenge.

## 11. Facts versus interpretation

Facts directly confirmed by the Lean source include:

- the complete type and right-hand side of the definition;
- the explicit decision to keep positivity outside the predicate;
- the fields bundled by `CounterexamplePack`;
- the fact that the next three foundational theorems unfold this predicate;
- the standalone file's use of `import Mathlib`.

The minimum-import suggestions, the assessment of generalization, and the proposed Comparator exercises are editorial and design analyses. They have not been verified by a separate Lean build.

The existing Japanese and English PDFs describe the exponent-five route through 5-adic valuation, the golden integer ring, and infinite descent. This article treats the repository's Lean declaration as the primary source and does not add any stronger claim from the narrative PDFs.

## 12. Next declaration to read

The next declaration should be:

```lean
DkMath.FLT.Five.CounterexamplePack
```

It is the first structure that supplements `Fermat5Equation` with positivity and primitiveness, thereby forming the positive primitive counterexample packet consumed by the later local factorizations.

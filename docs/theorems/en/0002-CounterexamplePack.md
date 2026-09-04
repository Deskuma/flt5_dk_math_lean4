# 0002 — `CounterexamplePack`

## 1. Exhibit

```lean
namespace DkMath.FLT.Five

/-- A positive primitive candidate for the exponent-five equation.  The condition
`Coprime x y` is the normalization needed by every subsequent local factorization. -/
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z

end DkMath.FLT.Five
```

Its fully qualified name is:

```lean
DkMath.FLT.Five.CounterexamplePack
```

For fixed `x y z : ℕ`, Lean treats it as a proposition-valued structure:

```lean
CounterexamplePack (x y z : ℕ) : Prop
```

## 2. Mathematical statement

`CounterexamplePack x y z` states that the three natural numbers simultaneously satisfy:

1. `x`, `y`, and `z` are positive;
2. `x` and `y` are coprime;
3. they satisfy the exponent-five Fermat equation.

$$
x^5+y^5=z^5
$$

Thus it packages not merely a possible solution, but a **positive primitive counterexample candidate** suitable for the later local factorizations.

Here “primitive” is recorded only by `Nat.Coprime x y`. Coprimality of `x` with `z` and of `y` with `z` is not stored as fields; the development derives those facts later from the equation.

## 3. Role in the complete proof

Where `Fermat5Equation` is the minimal predicate containing only the equation, `CounterexamplePack` is the first normalized input consumed by the active proof machinery.

The later gap, five-adic, and golden-order factorizations do not operate on an arbitrary triple that may contain zeros or a common factor. They assume a positive primitive candidate. This structure declares those assumptions once and makes them reusable through projections such as `p.hx`, `p.hxy`, and `p.hEq`.

Conceptually:

```text
Fermat5Equation x y z
  + positivity of x, y, z
  + Nat.Coprime x y
  └─ CounterexamplePack x y z
       └─ gap / GN5 / five-adic / golden-order reductions
```

## 4. Direct dependencies

There is one direct project-specific dependency:

- `DkMath.FLT.Five.Fermat5Equation`

From Lean and Mathlib it uses:

- `ℕ`;
- the natural-number order proposition `0 < x`;
- `Nat.Coprime`;
- proposition-valued structures.

It depends on no proved lemma. It is a declaration that packages data and assumptions.

## 5. Construction flow

To construct the structure, one supplies five proofs:

```lean
{
  hx  : 0 < x
  hy  : 0 < y
  hz  : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
}
```

After construction, each field is available as a projection:

```lean
p.hx
p.hy
p.hz
p.hxy
p.hEq
```

Because the structure lives in `Prop`, it is a proof package rather than a computational record.

## 6. Lean-specific processing

### 6.1 `structure ... : Prop`

`CounterexamplePack` lives in `Prop`, not in a data universe such as `Type`. Its purpose is therefore to organize proof assumptions, not to preserve runtime data.

By proof irrelevance, later proofs need not distinguish different proof terms inhabiting the structure. They use only the propositions exposed by its fields.

### 6.2 Parameterized structure

The numbers `x y z` are parameters rather than fields:

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
```

Consequently, the type of `p : CounterexamplePack x y z` already fixes the underlying triple. A closed record containing `x y z` as fields would also be possible, but the current form integrates naturally with theorem parameters and implicit arguments.

### 6.3 Reusing assumptions through projections

Instead of repeating a long list of hypotheses in each theorem, a theorem can accept one package and project only the fields it needs. This stabilizes the API and keeps proof terms organized.

## 7. Redundancy and duplication

The field `hz : 0 < z` may be logically derivable from `hx : 0 < x` together with the equation. If `x` is positive, then `z^5` cannot be zero. The same observation can be made using `hy`.

This is a mathematical audit observation, not an already established preceding lemma in the repository. Keeping `hz` as an explicit field lets later theorems use it directly instead of rederiving it. It can therefore be viewed as an intentional cached consequence rather than accidental duplication.

Conversely, storing only `hxy` and not the two coprimality statements involving `z` is a deliberate reduction of redundancy. The module comment explicitly states that the other coprimality facts are derived from the equation.

## 8. Optimization candidates

### 8.1 Derive `hz` instead of storing it

A minimal structure could omit `hz` and provide a lemma deriving it. This should not be done without measuring downstream use, proof-term size, and tactic stability.

### 8.2 Naming scope

`CounterexamplePack` does not assert that a counterexample exists; it packages a hypothetically assumed candidate. A neutral name such as `PrimitiveFermat5Data` is conceivable, but the present name accurately signals its role as the input to a proof by contradiction and descent.

### 8.3 Sharing a generic structure

Positivity and primitivity could be abstracted into an exponent-independent structure. However, the equation field and all later local theories are exponent-five specific. Until several exponents genuinely share the same API, the local structure is likely clearer.

## 9. Mathlib import audit

The standalone artifact uses:

```lean
import Mathlib
```

This structure itself needs only natural numbers and order, `Nat.Coprime`, and the preceding `Fermat5Equation` definition. A gcd-related Mathlib module providing `Nat.Coprime` is the principal import-minimization candidate.

The exact minimal module and its transitive dependencies were not build-tested in this run. Since the standalone is a generated concatenation containing later tactics, algebra, and number theory, its global `import Mathlib` should not be changed on the basis of this declaration alone. The proper audit target is the original split module `DkMath/FLT/Five/Basic.lean` using `#min_imports` or an isolated clean build.

## 10. Comparator challenge suitability

Comparator challenge conversion is **suitable**, especially for comparing structure construction, elimination, and minimal-hypothesis design.

### Challenge A — Construction

```lean
theorem mkCounterexamplePack
    {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : Nat.Coprime x y)
    (hEq : Fermat5Equation x y z) :
    CounterexamplePack x y z := by
  exact ⟨hx, hy, hz, hxy, hEq⟩
```

One can compare tuple syntax, repeated `constructor`, and named-field construction.

### Challenge B — Elimination

```lean
theorem unpackCounterexamplePack
    {x y z : ℕ}
    (p : CounterexamplePack x y z) :
    0 < x ∧ 0 < y ∧ 0 < z ∧ Nat.Coprime x y ∧
      Fermat5Equation x y z := by
  exact ⟨p.hx, p.hy, p.hz, p.hxy, p.hEq⟩
```

This supports comparison of projections, `rcases`, and simplification-based proofs.

## 11. Evidence and inference

Directly supported by the Lean source are:

- the five fields and their exact types;
- the fact that `CounterexamplePack ... : Prop`;
- the choice to store only `Nat.Coprime x y`;
- the module comment identifying it as the primitive input for gap, five-adic, and quadratic-order reductions.

The possible redundancy of `hz`, renaming, generic abstraction, and import minimization are audit proposals. No Lean build was run in this publication step.

## 12. Next declaration

The next declaration is:

```lean
DkMath.FLT.Five.fifth_sub_eq_of_add_eq
```

After the assumptions of a primitive candidate have been packaged, the first algebraic transformation needed by the proof route converts the additive equation

$$
x^5+y^5=z^5
$$

into the difference form

$$
z^5-y^5=x^5.
$$

That form opens the route to the natural-number gap and the `GN5` factorization.

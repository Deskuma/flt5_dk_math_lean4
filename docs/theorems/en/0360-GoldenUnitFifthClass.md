# 0360 — `GoldenUnitFifthClass`

## Declaration kind

This declaration is a **`def`**.

```lean
/-- Existence of `i < 5` and `delta` with `x = phi^i * delta^5`. -/
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

`GoldenUnitFifthClass x` states that the golden integer `x`, modulo fifth powers, belongs to one of the five representative classes `1, φ, φ², φ³, φ⁴`.

## Lean type

```lean
GoldenUnitFifthClass : GoldenInt → Prop
```

It is a predicate assigning a proposition to an input `x : GoldenInt`.

Internally it is written as

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

so the representative exponent `i` is constrained at the type level by

$$
0 \le i < 5.
$$

`i.val : ℕ` extracts the natural-number value of the `Fin 5` element, and `goldenPow goldenPhi i.val` is the representative unit `φ^i`.

## Mathematical meaning

In standard notation the definition says

$$
\operatorname{GoldenUnitFifthClass}(x)
\iff
\exists i\in\{0,1,2,3,4\},\ \exists \delta\in\mathbb Z[\varphi],
\quad
x=\varphi^i\delta^5.
$$

Here `GoldenInt` is the coordinate implementation of the golden integer order

$$
a+b\varphi,
\qquad
\varphi^2=\varphi+1.
$$

An important point is that the definition itself does not assume `GoldenUnit x`. It is a general predicate on every `x : GoldenInt`, asking whether such a fifth-class representation exists.

The later theorem

```lean
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x
```

proves that every actual unit satisfies this predicate.

## Role in the whole proof

By 0359 `goldenUnit_descent`, every golden unit whose coordinate measure is greater than one can be shortened strictly by multiplying once by `φ` or by its integral inverse `φ⁻¹`.

0360 fixes the **target proposition of that descent**.

The intended final form is

$$
x=\varphi^i\delta^5,
\qquad
0\le i<5.
$$

Only the exponent modulo five remains visible; multiples of five are absorbed into the fifth-power factor `delta^5`.

Thus this predicate is the interface that reduces unit classes modulo fifth powers to the five finite representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4.
$$

After this definition, the file proves lemmas describing how the class changes under multiplication by `φ` or `φ⁻¹`. Then `goldenUnitFifthClass_of_unit` iterates the strict descent of 0359 by `Nat.strong_induction_on` and completes the classification of all units.

Later, in `SignedGoldenUnitClasses.lean`, this classification is applied to a stripped packet representation

$$
\beta=\epsilon\gamma^5
$$

so that the arbitrary unit `epsilon` can be replaced by one of the five representatives `φ^i`. This is the step that turns infinitely many possible units into five finite algebraic sectors.

## Direct dependencies

The body of this `def` directly refers to the following project declarations:

- `GoldenInt` — the coordinate type of golden integers.
- `goldenPhi : GoldenInt` — the distinguished unit `φ`.
- `goldenPow : GoldenInt → ℕ → GoldenInt` — natural powers in the explicit golden API.
- `goldenMul : GoldenInt → GoldenInt → GoldenInt` — multiplication in the golden order.

At the type level it uses basic Lean / Mathlib objects:

- `Prop`,
- existential quantification `∃`,
- `Fin 5`,
- `Fin.val`,
- the natural-number literal `5`.

0359 `goldenUnit_descent` is not a direct dependency of the definition. The dependency direction is the reverse: the later theorem `goldenUnitFifthClass_of_unit` uses 0359 to prove this predicate for every unit.

## Construction flow

Because this declaration is a `def`, it contains no proof script. It only builds the proposition that later theorems must establish.

### 1. Choose a representative exponent in `Fin 5`

```lean
∃ i : Fin 5,
```

This forces `i` to range over exactly `0,1,2,3,4`.

Instead of taking `i : ℕ` and adding a separate hypothesis `i < 5`, finiteness is encoded directly in the type.

### 2. Choose a fifth-power base

```lean
∃ delta : GoldenInt,
```

The witness `delta` is the golden integer whose fifth power absorbs the multiple-of-five part of the unit exponent.

### 3. Require equality with a representative unit times a fifth power

```lean
x = goldenMul
      (goldenPow goldenPhi i.val)
      (goldenPow delta 5)
```

That is exactly

$$
x=\varphi^i\delta^5.
$$

This equality is the substantive content of the predicate.

## Lean-specific details

### `Fin 5`

Using `Fin 5` places the exponent bound in the type itself.

This is especially useful later because `fin_cases i` can enumerate all five cases completely and mechanically, matching the finite unit-sector structure of the FLT5 proof.

### `i.val`

`goldenPow` expects a natural-number exponent, so the natural value stored in `i : Fin 5` is extracted as `i.val`.

The proof `i.isLt : i.val < 5` is not written explicitly in this definition because it is already part of the `Fin 5` object.

### `Prop` and witnesses

This is a proposition rather than a data structure. The witnesses `i` and `delta` therefore live inside an existential proof.

Later theorems unpack a class certificate with code of the form

```lean
rcases hx with ⟨i, delta, hx⟩
```

and then reason about the corresponding sector.

## Redundancy and duplication

The definition is already very small and contains essentially no internal redundancy.

An alternative encoding could be

```lean
∃ i : ℕ, i < 5 ∧ ∃ delta : GoldenInt, ...
```

or an abstract quotient by fifth powers. The current `Fin 5` representation, however, connects directly to later `fin_cases` proofs and is well suited to the explicit five-sector FLT5 argument.

Likewise, `goldenMul` and `goldenPow` are later identified with ordinary ring `*` and `^`, but retaining the explicit golden API at this layer keeps the proof interface tied to the audited coordinate model.

## Optimization candidates

1. `GoldenUnitFifthClass` could in principle be merged with or aliased to `GoldenUnitClassesModFifth`. However, the former is a predicate for one `x`, while the latter universally quantifies over all units, so the current separation has a clear interface role.
2. The equation could be shortened to
   ```lean
   x = goldenPhi ^ i.val * delta ^ 5
   ```
   using ordinary ring notation, but this would reduce the visibility of the explicit golden API.
3. A future quotient-group formulation could model classes modulo fifth powers abstractly. The present proof, however, relies heavily on concrete `Fin 5` case analysis, so such abstraction would not automatically simplify the development.

These are design possibilities only. No Lean build was run in this task, so compatibility of such changes is unverified.

## Required Mathlib imports and import optimization

The generated standalone `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

but this definition itself uses no tactics at all. Externally it needs little beyond `Fin 5` and basic logic, assuming `GoldenInt`, `goldenPhi`, `goldenPow`, and `goldenMul` are already available.

A minimal Comparator environment would therefore likely need only the foundational import providing `Fin` plus the local golden-integer API, rather than all of `Mathlib`.

The **exact minimal import set at the repository module level is unverified**, because this run does not perform a Lean build.

## Comparator challenge suitability

As a standalone hole-filling challenge, this definition is very easy: reconstructing it is mostly a matter of restating the specification.

It can nevertheless serve as a specification-reading micro challenge:

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ?_
```

A correct solution must identify that

- the representative exponent should be `Fin 5`,
- a fifth-power base `delta : GoldenInt` must be existentially quantified,
- the target equation is `x = φ^i * delta^5` expressed through the explicit golden API.

A more meaningful Comparator challenge is to take this definition as given and ask for the following sector-shift lemmas or for `goldenUnitFifthClass_of_unit`, where one must actually combine 0359's descent with finite `Fin 5` case analysis.

## Next declaration to read

The next declaration is 0361 `golden_phi_four_mul_inv_five`. Its declaration kind is **`private theorem`**.

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  ...
```

It is the concrete identity needed when multiplication by `φ⁻¹` wraps class exponent zero around to class exponent four.

Conceptually,

$$
\varphi^4(\varphi^{-1})^5
=\varphi^{-1},
$$

which is the explicit golden-unit certificate for the congruence

$$
-1\equiv4\pmod5.
$$

Thus 0360 defines the target class predicate, while 0361 begins the lemmas that describe how those classes move under multiplication by `φ` and `φ⁻¹`.
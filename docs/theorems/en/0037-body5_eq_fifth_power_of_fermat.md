# 0037 — `body5_eq_fifth_power_of_fermat`

## Declaration

```lean
theorem body5_eq_fifth_power_of_fermat
    {x y z : ℕ}
    (hyz : y ≤ z)
    (hEq : Fermat5Equation x y z) :
    Body5 (z - y) y = x ^ 5 := by
  calc
    Body5 (z - y) y = z ^ 5 - y ^ 5 := by
      simpa [Nat.sub_add_cancel hyz] using
        (body5_eq_add_pow_sub (z - y) y)
    _ = x ^ 5 := fifth_sub_eq_of_add_eq hEq
```

## Lean type

```lean
body5_eq_fifth_power_of_fermat :
  {x y z : ℕ} →
  y ≤ z →
  Fermat5Equation x y z →
  Body5 (z - y) y = x ^ 5
```

For natural numbers `x`, `y`, and `z`, if the Fermat-five equation holds and `y ≤ z` is available to restore the natural-number gap safely, then the full body in gap coordinates is equal to `x^5`.

## Mathematical statement

Set `g=z-y`. By the previous article,

$$
Body5(g,y)=(g+y)^5-y^5.
$$

Since `y≤z`, we have $(z-y)+y=z$, and therefore

$$
Body5(z-y,y)=z^5-y^5.
$$

On the other hand,

$$
x^5+y^5=z^5
$$

implies

$$
z^5-y^5=x^5.
$$

Hence

$$
Body5(z-y,y)=x^5.
$$

## Role in the complete proof

This theorem specializes the general `Body5` identity to a candidate satisfying the Fermat equation.

Later clean-channel refuters show that a prime occurring only once in `Body5 (z-y) y` prevents that body from being a fifth power. The present theorem supplies the opposite fact forced by the Fermat equation: the same body is exactly `x^5`. It is therefore the bridge that lets a local valuation obstruction collide directly with the original equation.

## Direct dependencies

### `Fermat5Equation`

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

### `Body5`

```lean
def Body5 (g y : ℕ) : ℕ :=
  g * GN5 g y
```

### `body5_eq_add_pow_sub`

```lean
theorem body5_eq_add_pow_sub (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5
```

### `fifth_sub_eq_of_add_eq`

```lean
theorem fifth_sub_eq_of_add_eq
    {x y z : ℕ}
    (hEq : Fermat5Equation x y z) :
    z ^ 5 - y ^ 5 = x ^ 5
```

### `Nat.sub_add_cancel`

From `hyz : y ≤ z`, this restores `(z-y)+y=z` and returns from gap coordinates to the original variable `z`.

## Proof flow

1. Use `calc` to expose the intermediate expression `z^5-y^5`.
2. Apply `body5_eq_add_pow_sub (z-y) y`.
3. Simplify `(z-y)+y` to `z` with `Nat.sub_add_cancel hyz`.
4. Apply `fifth_sub_eq_of_add_eq hEq` to replace the difference by `x^5`.

## Lean-specific processing

### Natural-number subtraction

Subtraction on `Nat` is truncated. The hypothesis `hyz : y ≤ z` is required to treat `z-y` as the intended nonnegative gap and to use `Nat.sub_add_cancel hyz`.

### `simpa ... using`

The preceding theorem produces `((z-y)+y)^5-y^5`. The simplifier changes only the coordinate restoration step and matches the target `z^5-y^5`.

### `calc`

The proof explicitly composes two independent bridges: from `Body5` to a fifth-power difference, and from the Fermat equation to the value of that difference.

## Redundancy and duplication

The theorem is a direct composition of `body5_eq_add_pow_sub` and `fifth_sub_eq_of_add_eq`; it contains no new number theory. It is nevertheless an important API lemma because later proofs do not need to repeat the gap restoration and subtraction argument.

Although a `CounterexamplePack` can provide `hyz` through `right_lt_of_fermat5Equation`, the theorem accepts only the weaker inputs it truly needs: a Fermat equation and an order hypothesis. This improves reuse.

## Optimization candidates

The current `calc` proof mirrors the two mathematical stages and is easy to audit. A denser alternative could try to compose the two equalities in one expression, but that would make the intermediate type alignment less transparent.

One could also derive `hyz` internally from positivity of `x`, but positivity is deliberately absent from this theorem. Keeping the current general signature is preferable.

## Required Mathlib imports and import optimization

The generated standalone source uses `import Mathlib`. This theorem itself needs natural-number powers and subtraction, `Nat.sub_add_cancel`, equality reasoning, and the project declarations `Fermat5Equation`, `Body5`, `body5_eq_add_pow_sub`, and `fifth_sub_eq_of_add_eq`.

No advanced algebra tactic is used. The exact minimal import set has not been checked by a Lean build.

## Comparator challenge suitability

This is suitable for a beginner-to-intermediate Comparator challenge.

```lean
theorem body5_eq_fifth_power_of_fermat_challenge
    {x y z : ℕ}
    (hyz : y ≤ z)
    (hEq : Fermat5Equation x y z) :
    Body5 (z - y) y = x ^ 5 := by
  -- connect the general body identity, gap restoration, and Fermat equation
  sorry
```

Possible comparisons are the current `calc` proof, a rewrite-oriented proof, and a compressed `simpa ... using` proof. The main evaluation points are safe handling of `Nat` subtraction and reuse of existing bridge lemmas.

## Sources and explicit conjectural remarks

The declaration type, two-stage proof structure, direct dependencies, and source order are grounded in the generated `DkMath/FLT/Five/BranchB.lean` section of `Flt5DkMath/FLT5StandAlone.lean` in the repository.

The import-minimization and proof-compression remarks are unverified design suggestions. No Lean build was run. Existing PDFs provide narrative context, while the Lean source remains the formal authority.

## Next declaration to read

The next declaration in `BranchB.lean` consumes this theorem and refutes a Fermat candidate when a clean channel is available. Its exact declaration name will be reconfirmed from the current branch before the next article is issued.

# 0415 `padicValNat_clean_body_eq_one`

## Declaration kind

`theorem`

## Lean type

```lean
theorem padicValNat_clean_body_eq_one
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
  exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

This theorem shows that, given `CleanGN5Channel g y q`, the prime `q` occurs in the full fifth-power body

```lean
g * GN5 g y
```

with `padicValNat` exactly equal to 1.

## Mathematical statement

A `CleanGN5Channel g y q` already provides the following two full-body facts:

```lean
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

The first says

$$
q\mid g\,GN_5(g,y),
$$

so, once the body is known to be nonzero,

$$
1\le v_q(g\,GN_5(g,y)).
$$

The previous theorem, 0414 `padicValNat_clean_body_upper_bound`, uses the second fact to prove

$$
v_q(g\,GN_5(g,y))\le1.
$$

Combining the two opposite inequalities yields

$$
v_q(g\,GN_5(g,y))=1.
$$

In Lean, the two inequalities are combined with

```lean
Nat.le_antisymm
```

to obtain the equality.

## Role in the full proof

0413 `padicValNat_lower_bound_d5` shows that if a prime `q` divides a positive natural number `x`, then

$$
5\le v_q(x^5).
$$

0414 `padicValNat_clean_body_upper_bound` gives, for a clean channel,

$$
v_q(g\,GN_5(g,y))\le1.
$$

0415 sharpens this further by using `h.dvd_body` to add the lower bound and conclude

$$
v_q(g\,GN_5(g,y))=1.
$$

This exact valuation is used directly by the next declaration,

```lean
counterexample_false_of_clean_GN5Channel_by_padicValNat
```

which uses the Fermat-five body identity

$$
(z-y)GN_5(z-y,y)=x^5.
$$

The same natural number is therefore viewed in two ways. On the fifth-power side,

$$
5\le v_q(x^5),
$$

while on the clean-body side,

$$
v_q((z-y)GN_5(z-y,y))=1.
$$

After transporting across the body identity, the contradiction is reduced to

$$
5\le1.
$$

Thus 0415 is the **exact local multiplicity certificate** in the valuation route, linking the fifth-power lower bound from 0413 to the final contradiction theorem.

## Direct dependencies

### `CleanGN5Channel`

`CleanGN5Channel g y q` represents a clean prime channel in which `q` divides `GN5 g y`, does not divide the gap `g`, and does not lift to a square divisor of `GN5 g y`.

0415 directly uses:

```lean
h.prime : Nat.Prime q
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

`h.dvd_body` supplies the valuation lower bound, while `h.not_sq_dvd_body`, through 0414, supplies the upper bound.

### `padicValNat_clean_body_upper_bound`

The immediately preceding theorem 0414:

```lean
padicValNat_clean_body_upper_bound h :
  padicValNat q (g * GN5 g y) ≤ 1
```

0415 passes this theorem directly as the first argument of `Nat.le_antisymm`.

### `padicValNat_dvd_iff_le`

For a nonzero natural number `n`, this Mathlib bridge conceptually states

$$
q^k\mid n
\Longleftrightarrow
k\le v_q(n).
$$

0415 sets `k = 1` and uses the `.mp` direction to turn

```lean
q ∣ g * GN5 g y
```

into

```lean
1 ≤ padicValNat q (g * GN5 g y)
```

### `Nat.le_antisymm`

This combines

```lean
v ≤ 1
1 ≤ v
```

into

```lean
v = 1
```

in the natural-number order.

## Proof flow

### 1. Install primality as a typeclass instance

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

This supplies the primality hypothesis required by the relevant `padicValNat` API through local typeclass inference.

### 2. Prove that the full body is nonzero

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

If the body were zero, then

$$
q^2\mid0,
$$

contradicting `h.not_sq_dvd_body`.

This proof is identical to the one in 0414.

### 3. Obtain the upper bound from 0414

```lean
apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
```

Applying `Nat.le_antisymm` to the goal

```lean
padicValNat q (g * GN5 g y) = 1
```

uses 0414 to close the first direction

```lean
padicValNat q (g * GN5 g y) ≤ 1
```

immediately.

The remaining goal is

```lean
1 ≤ padicValNat q (g * GN5 g y)
```

### 4. Convert body divisibility into the valuation lower bound

```lean
exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

`h.dvd_body` has the form

```lean
q ∣ g * GN5 g y
```

while the `k = 1` side of `padicValNat_dvd_iff_le` expects

```lean
q ^ 1 ∣ g * GN5 g y
```

The `simpa` invocation normalizes `q ^ 1 = q` and supplies the required divisibility statement.

Then `.mp` yields

$$
1\le v_q(g\,GN_5(g,y)),
$$

and antisymmetry finishes the equality.

## Lean-specific processing

### 1. Repackaging a proposition as a `Fact` instance

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

introduces no new mathematical assumption. It merely exposes the already available proof `h.prime` to typeclass search.

### 2. Exposing implicit and instance arguments with `@`

```lean
@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 1 hBodyNe
```

makes the theorem's implicit and instance arguments explicit and fixes the application shape.

0413, 0414, and 0415 all use this style, so the valuation section is internally consistent.

### 3. Symmetry between `.mp` here and `.mpr` in 0414

0414 used `.mpr` to obtain

$$
2\le v_q(body)
\Longrightarrow q^2\mid body.
$$

0415 uses `.mp` in the reverse conceptual direction:

$$
q\mid body
\Longrightarrow1\le v_q(body).
$$

The two adjacent theorems therefore use opposite directions of the same valuation/divisibility equivalence.

### 4. Eliminating `q ^ 1` with `simpa`

`h.dvd_body` is stated as `q ∣ body`, whereas the bridge theorem at exponent one uses `q ^ 1 ∣ body`.

```lean
by simpa using h.dvd_body
```

absorbs this normalization.

### 5. `Nat.le_antisymm`

No `omega` or `linarith` is needed here. Both inequalities are already available explicitly, so order antisymmetry alone constructs the exact valuation equality.

## Redundancy and duplication

### `hBodyNe` is duplicated verbatim from 0414

Both 0414 and 0415 contain:

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

This is a clear local duplication.

A helper theorem such as `CleanGN5Channel.body_ne` in `CleanChannel.lean` would remove it from both valuation theorems.

### Duplication between `letI` and `Fact.mk h.prime`

After installing

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

the proof still passes

```lean
Fact.mk h.prime
```

explicitly.

This may be intentional for elaboration stability, but it could potentially be shortened if typeclass inference is sufficient.

### The exact-one theorem is logically thin

The mathematical core of 0415 is simply

```text
upper bound ≤ 1
+ divisibility gives lower bound ≥ 1
= exact valuation 1
```

so it adds little new arithmetic beyond 0414.

Nevertheless, the `= 1` interface is extremely convenient for the final contradiction theorem, so retaining this wrapper theorem has clear API value.

## Optimization candidates

### 1. Add `CleanGN5Channel.body_ne`

This is the clearest local refactoring opportunity.

Conceptually:

```lean
theorem CleanGN5Channel.body_ne
    (h : CleanGN5Channel g y q) :
    g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

would remove the duplicated nonzero proof from 0414 and 0415.

### 2. Move exact valuation closer to the clean-channel API

Semantically, a `CleanGN5Channel` represents a channel whose local exponent in the body is exactly one.

If valuation is intended as a primary public API, one could place `padicValNat_clean_body_eq_one` closer to `CleanChannel.lean`.

However, the current architecture deliberately separates the direct divisibility contradiction from the independent valuation route, so keeping the theorem in `Valuation.lean` is also well motivated.

### 3. Factor the bridge-theorem boilerplate

0413–0415 repeatedly expose `Fact` and `padicValNat_dvd_iff_le` explicitly.

A local helper for “prime + divisibility + nonzero implies valuation at least one” could shorten the code.

The current direct use of the Mathlib bridge is also pedagogically useful, so this is optional rather than necessary.

### 4. Name the `q ^ 1` divisibility fact

For readability, one could write

```lean
have hqPowOne : q ^ 1 ∣ g * GN5 g y := by
  simpa using h.dvd_body
```

before invoking the bridge theorem.

The current inline form is shorter and remains clear once the API is familiar.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib functionality directly required by 0415 includes at least:

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- `Nat.le_antisymm`
- natural-number divisibility and power simplification

The **exact minimal import set for the Mathlib version pinned by this repository has not been verified**. No Lean build is performed in this task, so it would be unsafe to claim a precise reduced import list.

A safe import-minimization procedure would first identify the module defining the required `padicValNat` API, then add the imports needed by the clean-channel and GN5 definitions.

## Comparator challenge suitability

**Yes. It is suitable as a small-to-medium challenge.**

A natural challenge is:

> From `CleanGN5Channel g y q`, prove `padicValNat q (g * GN5 g y) = 1`. The existing upper-bound theorem may be used.

The essential ideas are only:

1. Derive nonzeroness of the body from `not_sq_dvd_body`.
2. Use 0414 to obtain `v_q(body) ≤ 1`.
3. Use `dvd_body` and `padicValNat_dvd_iff_le` to obtain `1 ≤ v_q(body)`, then apply `Nat.le_antisymm`.

For a harder challenge, forbid use of 0414 and require reconstruction of the upper bound directly from `h.not_sq_dvd_body`. That version exercises both directions of `padicValNat_dvd_iff_le` in one task.

The main difficulty is Mathlib API use rather than new mathematical invention, so this is better characterized as a **Lean API / proof-refactoring challenge** than as a research-style Comparator challenge.

## Next declaration to read

Next is 0416 `counterexample_false_of_clean_GN5Channel_by_padicValNat`.

```lean
theorem counterexample_false_of_clean_GN5Channel_by_padicValNat
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z := Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  have hBodyEq : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hBodyEq]
    exact hClean.dvd_body
  have hqDivX : q ∣ x := hClean.prime.dvd_of_dvd_pow hqDivPow
  have hlower : 5 ≤ padicValNat q (x ^ 5) :=
    padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
  have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
    simpa [Body5] using padicValNat_clean_body_eq_one hClean
  rw [hBodyEq] at hexact
  omega
```

0416 directly collides 0413 and 0415 on the Fermat-five body identity.

Its structure is simply

$$
\text{Fermat body}=x^5,
$$

$$
5\le v_q(x^5),
$$

$$
v_q(\text{Fermat body})=1,
$$

and the independent proof route in `Valuation.lean` is completed there.
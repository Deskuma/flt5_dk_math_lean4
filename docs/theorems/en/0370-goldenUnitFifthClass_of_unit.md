# 0370 `goldenUnitFifthClass_of_unit`

## Declaration kind

`theorem`

## Lean code

```lean
/-- The direct coordinate descent classifies every golden unit modulo fifth powers. -/
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := by
  generalize hm : goldenUnitMeasure x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      have hpos : 0 < n := by rw [← hm]; exact goldenUnitMeasure_pos hx
      rcases eq_or_lt_of_le (show 1 ≤ n by omega) with hn | hn
      · have hm1 : goldenUnitMeasure x = 1 := by omega
        rcases goldenUnit_measure_one_cases hx hm1 with h | h | h | h
        · simpa [h] using goldenUnitFifthClass_one
        · simpa [h] using goldenUnitFifthClass_neg_one
        · simpa [h] using goldenUnitFifthClass_phi
        · simpa [h] using goldenUnitFifthClass_neg_phi
      · obtain ⟨y, hy, hylt, hrec⟩ := goldenUnit_descent hx (by omega)
        have hyClass : GoldenUnitFifthClass y :=
          ih (goldenUnitMeasure y) (by omega) y hy rfl
        rcases hrec with hrec | hrec
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phi hyClass
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phiInv hyClass
```

## Lean type

```lean
goldenUnitFifthClass_of_unit
  (x : GoldenInt)
  (hx : GoldenUnit x) :
  GoldenUnitFifthClass x
```

For every golden integer `x`, if `x` is a `GoldenUnit`, then `x` belongs to one of the five fifth-power classes represented by `1, φ, φ², φ³, φ⁴`.

Expanding `GoldenUnitFifthClass x`, the conclusion is

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Mathematically,

$$
x = \varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

## Mathematical statement

The units of the golden integer ring collapse modulo fifth powers to five classes, indexed by the exponent of `φ` modulo 5.

Thus for every unit $x$ there exist $i\in\{0,1,2,3,4\}$ and a golden integer $\delta$ such that

$$
x=\varphi^i\delta^5.
$$

Because 5 is odd, the sign can be absorbed into the fifth-power factor:

$$
(-\delta)^5=-\delta^5.
$$

Therefore no extra representatives `-1`, `-φ`, and so on are needed.

The theorem does not directly invoke an abstract classification of the full unit group. Instead, it proves the required finite classification by a coordinate measure and certified strict descent.

## Role in the full proof

This is the central theorem of `GoldenUnitClassification.lean`.

The preceding development has prepared three ingredients.

1. A positive natural-number measure `goldenUnitMeasure` on golden units.
2. A classification of measure-one units as

$$
1,\quad -1,\quad \varphi,\quad -\varphi.
$$

3. A strict descent for every unit of measure greater than one, producing a smaller unit `y` from which `x` is reconstructed as either

$$
x=y\varphi
$$

or

$$
x=y\varphi^{-1}.
$$

This theorem combines those ingredients with `Nat.strong_induction_on`.

The already established transport theorems

```lean
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

lift the fifth-class property from the smaller unit `y` back to the original unit `x`.

Once this theorem is available, the next theorem

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

is essentially a wrapper. That public contract is then used to reduce arbitrary unit factors of stripped FLT5 packets to the five finite algebraic sectors.

## Direct dependencies

### `GoldenUnitFifthClass`

The conclusion predicate:

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

### `goldenUnitMeasure`

The natural-valued measure on which strong induction is performed.

### `goldenUnitMeasure_pos`

This proves that the measure of a unit is positive. In the proof it yields

```lean
have hpos : 0 < n := by
  rw [← hm]
  exact goldenUnitMeasure_pos hx
```

and hence $1\le n$.

### `goldenUnit_measure_one_cases`

The terminal classification theorem for units of measure one:

$$
1,-1,\varphi,-\varphi.
$$

### `goldenUnitFifthClass_one`

Provides

$$
1=\varphi^0 1^5.
$$

### `goldenUnitFifthClass_neg_one`

Provides

$$
-1=\varphi^0(-1)^5.
$$

### `goldenUnitFifthClass_phi`

Provides

$$
\varphi=\varphi^1 1^5.
$$

### `goldenUnitFifthClass_neg_phi`

Provides

$$
-\varphi=\varphi^1(-1)^5.
$$

### `goldenUnit_descent`

The strict-descent theorem. The portion of its output used here is conceptually

```lean
∃ y,
  GoldenUnit y ∧
  goldenUnitMeasure y < goldenUnitMeasure x ∧
  (x = goldenMul y goldenPhi ∨
   x = goldenMul y goldenPhiInv)
```

### `goldenUnitFifthClass_mul_phi`

Preserves the class property after multiplying by $\varphi$; the sector changes as

$$
i\mapsto i+1\pmod5.
$$

### `goldenUnitFifthClass_mul_phiInv`

Preserves the class property after multiplying by $\varphi^{-1}$; the sector changes as

$$
i\mapsto i-1\pmod5.
$$

### `Nat.strong_induction_on`

Strong induction is required because the descent reaches an arbitrary strictly smaller measure, not necessarily the immediate predecessor.

## Proof flow

### 1. Generalize the measure

```lean
generalize hm : goldenUnitMeasure x = n
```

This replaces the compound measure expression by a natural-number variable `n` suitable for induction.

### 2. Strongly induct on `n`

```lean
induction n using Nat.strong_induction_on generalizing x with
| h n ih =>
```

The `generalizing x` clause is essential. After one descent step, the induction hypothesis must be applied to a different unit `y`, rather than only to the original `x`.

### 3. Establish positivity of the measure

```lean
have hpos : 0 < n := by
  rw [← hm]
  exact goldenUnitMeasure_pos hx
```

Thus $1\le n$.

### 4. Split into `n = 1` and `1 < n`

```lean
rcases eq_or_lt_of_le (show 1 ≤ n by omega) with hn | hn
```

This is exactly the boundary between the terminal base cases and the descent case.

### 5. Close the measure-one case

From `n = 1`, the proof obtains

```lean
have hm1 : goldenUnitMeasure x = 1 := by omega
```

and then performs the finite classification

```lean
rcases goldenUnit_measure_one_cases hx hm1 with h | h | h | h
```

Each branch is discharged by transporting one of the four explicit fifth-class theorems along the equality `h`:

```lean
simpa [h] using goldenUnitFifthClass_one
simpa [h] using goldenUnitFifthClass_neg_one
simpa [h] using goldenUnitFifthClass_phi
simpa [h] using goldenUnitFifthClass_neg_phi
```

### 6. Perform strict descent when the measure is larger

```lean
obtain ⟨y, hy, hylt, hrec⟩ :=
  goldenUnit_descent hx (by omega)
```

This supplies a smaller unit `y`, its unit proof, the strict inequality of measures, and a reconstruction of `x` by multiplying `y` by either `φ` or `φ⁻¹`.

### 7. Apply the induction hypothesis to `y`

```lean
have hyClass : GoldenUnitFifthClass y :=
  ih (goldenUnitMeasure y) (by omega) y hy rfl
```

This is the core strong-induction step. From `hylt` and `hm`, `omega` proves

$$
goldenUnitMeasure(y)<n.
$$

The induction hypothesis can therefore classify `y`.

### 8. Reconstruct the original unit

The reconstruction proof is split:

```lean
rcases hrec with hrec | hrec
```

If $x=y\varphi$,

```lean
rw [hrec]
exact goldenUnitFifthClass_mul_phi hyClass
```

and if $x=y\varphi^{-1}$,

```lean
rw [hrec]
exact goldenUnitFifthClass_mul_phiInv hyClass
```

finishes the theorem.

Mathematically, strict descent proves the property below the current measure, while closure under multiplication by the two generators transports the classification back upward to the original unit.

## Lean-specific processing

### `generalize ... = n`

This is the Lean management step corresponding to introducing the notation $n=m(x)$ before induction.

### `generalizing x`

Without this clause, the induction hypothesis would be specialized too narrowly to the original `x`, making it unsuitable for the descended unit `y`.

This is an important dependent-context pattern when combining a measure with strong induction.

### `omega`

Here `omega` handles natural-number order bookkeeping rather than golden-integer algebra. Its uses include:

- deriving `1 ≤ n` from `0 < n`,
- reconciling the `n = 1` branch with `hm`,
- providing the `1 < measure` premise required by descent,
- combining `hylt` and `hm` into the strict inequality needed by `ih`.

### `simpa [h] using ...`

In each base branch, the equality returned by `goldenUnit_measure_one_cases` rewrites the current `x` into the corresponding explicit unit, after which an already-proved fifth-class theorem has exactly the required type.

### Passing `rfl` to the induction hypothesis

When applying `ih` to `y`, the generalized measure equality becomes

```lean
goldenUnitMeasure y = goldenUnitMeasure y
```

so reflexivity is sufficient.

## Redundancy and duplication

The proof is compact and its architecture is clear. The main local repetition is the four nearly identical base-case lines:

```lean
simpa [h] using goldenUnitFifthClass_one
simpa [h] using goldenUnitFifthClass_neg_one
simpa [h] using goldenUnitFifthClass_phi
simpa [h] using goldenUnitFifthClass_neg_phi
```

This duplication is inherited from the four-way output of `goldenUnit_measure_one_cases`.

The explicit form is nevertheless valuable for a theorem museum because it makes the exact terminal unit and its fifth-class witness visible.

The final two branches are similarly symmetric, differing only between multiplication by `φ` and by `φ⁻¹`.

## Optimization candidates

### 1. Combine measure-one classification with fifth-class closure

A helper theorem of the shape

```lean
goldenUnitMeasure x = 1 → GoldenUnitFifthClass x
```

would collapse the four base branches to one line.

However, keeping `goldenUnit_measure_one_cases` as an equality classification is more reusable, so the present separation has a sound design justification.

### 2. Abstract the reconstruction step

A helper theorem conceptually of the form

```lean
GoldenUnitFifthClass y →
(x = y * φ ∨ x = y * φ⁻¹) →
GoldenUnitFifthClass x
```

could hide the final two branches.

For explanatory code, however, the present theorem exposes the descent/reconstruction mechanism more clearly.

### 3. Reduce local reliance on `omega`

Some order steps could likely be written with explicit natural-number lemmas such as successor inequalities and rewriting. This may reduce tactic dependence, but it would probably increase code size.

### 4. Alternative proof from an abstract unit-group classification

If an abstract theorem identifying the unit group with elements of the form $\pm\varphi^k$ were imported, the theorem might be shortened to reducing the exponent modulo 5.

That would not necessarily be an architectural improvement here: the current development deliberately proves the required classification internally by coordinate descent.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The Mathlib-side facilities directly visible in this theorem are mainly:

- `Nat.strong_induction_on`,
- natural-number order lemmas,
- the `omega` tactic,
- standard elaboration/tactic infrastructure used by `rcases`, `obtain`, `simpa`, and `rw`.

The golden integer, unit measure, descent, and fifth-class declarations are project-local dependencies.

It is very likely that `import Mathlib` could be narrowed to modules providing natural-number strong induction, Presburger arithmetic via `omega`, and the project modules defining the golden-unit API.

The exact minimal import set is not verified here because this task does not run Lean builds, so this remains an optimization candidate rather than a confirmed replacement.

## Comparator challenge suitability

**Yes. This is a particularly good medium-sized Comparator challenge.**

Unlike the preceding micro challenges based on `decide` or `ring`, this theorem compares proof architecture rather than only local tactic selection.

A challenge can expose the following API:

```lean
GoldenUnitFifthClass
goldenUnitMeasure
goldenUnitMeasure_pos
goldenUnit_measure_one_cases
goldenUnit_descent
goldenUnitFifthClass_one
goldenUnitFifthClass_neg_one
goldenUnitFifthClass_phi
goldenUnitFifthClass_neg_phi
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

with goal

```lean
theorem challenge (x : GoldenInt) (hx : GoldenUnit x) :
  GoldenUnitFifthClass x
```

Useful comparison points include whether a solver can:

- choose strong induction rather than ordinary successor induction,
- generalize the measure correctly,
- recognize why `generalizing x` is required,
- connect the strict-descent inequality to the induction hypothesis,
- handle all four terminal units,
- transport the class back through multiplication by `φ` or `φ⁻¹`.

This makes it a substantially more informative proof-engineering challenge than a closed arithmetic equality.

## Technical meaning

The essential achievement is a machine-checked compression of an infinite unit family into five finite classes by strict descent.

The unit population may be infinite through repeated multiplication by `φ` and `φ⁻¹`. Modulo fifth powers, however, only the exponent modulo 5 matters.

Rather than merely citing this intuition, the formal proof realizes it as

$$
\text{strictly decreasing measure}
\;\Longrightarrow\;
\text{finite terminal cases}
\;\Longrightarrow\;
\text{sector transport}.
$$

`goldenUnit_descent` pushes the infinite process into the well-founded order on natural numbers, and the two multiplication-closure theorems guarantee that classification survives reconstruction.

Consequently, the downstream FLT5 arithmetic no longer needs to reason about an arbitrary unit `epsilon`; it needs only five sectors

$$
0,1,2,3,4.
$$

This theorem is therefore the decisive bridge from arbitrary algebraic unit factors to finite sector arithmetic.

## Next declaration to read

The next declaration is

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

It wraps the present theorem in the public contract `GoldenUnitClassesModFifth`. That contract is then consumed by `signedGoldenFiniteUnitSectorCore_of_unitClasses` to reduce every stripped packet to one of the five algebraic unit sectors.
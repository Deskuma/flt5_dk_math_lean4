# 0356 — `goldenUnit_measure_one_cases`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  have hsum : x.fst.natAbs + x.snd.natAbs = 1 := hm
  have hcases :
      (x.fst.natAbs = 0 ∧ x.snd.natAbs = 1) ∨
      (x.fst.natAbs = 1 ∧ x.snd.natAbs = 0) := by omega
  rcases hcases with h | h
  · have ha0 : x.fst = 0 := Int.natAbs_eq_zero.mp h.1
    have hb : x.snd = 1 ∨ x.snd = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.2)
    rcases hb with hb | hb
    · right; right; left; ext <;> simp [goldenPhi, ha0, hb]
    · right; right; right; ext <;> simp [goldenPhi, ha0, hb]
  · have ha : x.fst = 1 ∨ x.fst = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.1)
    have hb0 : x.snd = 0 := Int.natAbs_eq_zero.mp h.2
    rcases ha with ha | ha
    · left; ext <;> simp [goldenOne, ha, hb0]
    · right; left; ext <;> simp [goldenOne, ha, hb0]
```

## Lean type

```lean
goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
  x = goldenOne ∨ x = -goldenOne ∨
    x = goldenPhi ∨ x = -goldenPhi
```

For an arbitrary golden integer `x`, if `x` is a unit and its coordinate measure is 1, the theorem returns that `x` is one of `goldenOne`, `-goldenOne`, `goldenPhi`, or `-goldenPhi`.

A notable Lean-level fact is that the assumption `_hx : GoldenUnit x` is not used in the proof body. The classification actually follows from `hm : goldenUnitMeasure x = 1` alone.

## Mathematical statement

Write a golden integer as

$$
x=a+b\varphi.
$$

Using the measure defined in 0354,

$$
\mu(x)=|a|+|b|,
$$

the hypothesis

$$
\mu(x)=1
$$

forces, because the two terms are nonnegative integers,

$$
(|a|,|b|)=(1,0)
\quad\text{or}\quad
(|a|,|b|)=(0,1).
$$

In the first case,

$$
a=\pm1,\qquad b=0,
$$

so

$$
x=\pm1.
$$

In the second case,

$$
a=0,\qquad b=\pm1,
$$

so

$$
x=\pm\varphi.
$$

Hence

$$
x\in\{1,-1,\varphi,-\varphi\}.
$$

This is not a deep unit-theoretic fact specific to the golden order. It is the complete classification of integral lattice points having coordinate $\ell^1$ measure 1.

## Role in the whole proof

This theorem supplies the **base-case classification** for the natural-number strong induction used in `GoldenUnitClassification`.

The preceding theorem 0355 `goldenUnitMeasure_pos` proves that every unit satisfies

$$
0<\mu(x),
$$

so the smallest possible value is 1. The present theorem identifies all objects at that minimum.

Later, `goldenUnitFifthClass_of_unit` generalizes `goldenUnitMeasure x = n` and performs strong induction on $n$. In the `n=1` branch it invokes this theorem directly. The four resulting branches are discharged by

```text
1       → goldenUnitFifthClass_one
-1      → goldenUnitFifthClass_neg_one
phi     → goldenUnitFifthClass_phi
-phi    → goldenUnitFifthClass_neg_phi
```

Thus the descent architecture is

```text
unit x
  ↓
0 < μ(x)                    -- 0355
  ↓
if μ(x) = 1: four base points -- 0356
  ↓
if μ(x) > 1: strict descent
  ↓
a smaller unit
  ↓
strong induction
```

## Direct dependencies

The main direct dependencies are:

- `GoldenInt` — the two-integer coordinate model of the golden order.
- `GoldenUnit` — appears as an assumption, although `_hx` is unused in the proof body.
- `goldenUnitMeasure` — 0354, defined as `x.fst.natAbs + x.snd.natAbs`.
- `goldenOne` — the golden integer with coordinates `⟨1, 0⟩`.
- `goldenPhi` — the golden integer with coordinates `⟨0, 1⟩`.
- `Int.natAbs_eq_zero` — converts `natAbs a = 0` into `a = 0`.
- `Int.natAbs_eq_iff` — used to recover `a = 1 ∨ a = -1` from `natAbs a = 1`.
- `omega` — classifies the nonnegative solutions of a two-term sum equal to 1.
- `ext` — reduces equality of `GoldenInt` structures to coordinate equalities.
- `simp` — unfolds `goldenOne`, `goldenPhi`, signs, and concrete coordinates to close each branch.

The preceding theorem 0355 is conceptually important but is not a direct dependency. The present theorem follows from `hm` alone.

## Proof flow

### 1. Extract the coordinate sum

```lean
have hsum : x.fst.natAbs + x.snd.natAbs = 1 := hm
```

Here Lean can use the defining equation of `goldenUnitMeasure`, so the hypothesis is reused directly as a statement about the two coordinate absolute values.

### 2. Classify the two absolute values

```lean
have hcases :
    (x.fst.natAbs = 0 ∧ x.snd.natAbs = 1) ∨
    (x.fst.natAbs = 1 ∧ x.snd.natAbs = 0) := by omega
```

This is the discrete core of the proof. For natural numbers $A,B$ satisfying

$$
A+B=1,
$$

the only possibilities are

$$
(A,B)=(0,1),(1,0).
$$

### 3. First coordinate equal to zero

The proof first obtains

```lean
have ha0 : x.fst = 0 := Int.natAbs_eq_zero.mp h.1
```

and then recovers the sign of the second coordinate:

```lean
have hb : x.snd = 1 ∨ x.snd = -1 := by
  simpa using (Int.natAbs_eq_iff.mp h.2)
```

The two branches are converted by `ext` and `simp` into `goldenPhi` and `-goldenPhi`.

### 4. Second coordinate equal to zero

Similarly,

```lean
have ha : x.fst = 1 ∨ x.fst = -1 := by
  simpa using (Int.natAbs_eq_iff.mp h.1)
have hb0 : x.snd = 0 := Int.natAbs_eq_zero.mp h.2
```

produces `goldenOne` and `-goldenOne`.

## Lean-specific processing

### The unused `_hx`

The argument

```lean
(_hx : GoldenUnit x)
```

is intentionally named with a leading underscore because it is unused. The proof body would establish the result even without unithood.

So the logically stronger statement

```lean
goldenUnitMeasure x = 1 →
  x = goldenOne ∨ x = -goldenOne ∨
    x = goldenPhi ∨ x = -goldenPhi
```

is already implicit in the implementation.

### The role of `omega`

`omega` does not reason about the golden norm or units. It only solves the Presburger-arithmetic problem

```lean
A + B = 1
```

for natural numbers and enumerates the two possible pairs.

### Recovering signs with `Int.natAbs_eq_iff`

The measure lives in `ℕ`, while the coordinates live in `ℤ`. The proof must therefore recover signed coordinate information from `natAbs = 1`; this is exactly the bridge supplied by `Int.natAbs_eq_iff`.

### `ext <;> simp`

Equality of golden integers is reduced to equality of the `.fst` and `.snd` coordinates. Each of the four resulting goals is a closed coordinate calculation, so no number-theoretic reasoning remains.

## Redundancy and duplication

The clearest redundancy is that `_hx : GoldenUnit x` is completely unused.

It may have been retained to keep the theorem's public API aligned with its intended use as the measure-one base case for units. Logically, however, it is unnecessary and the result can be separated into a more general lattice lemma.

The two major branches also have the same shape: one coordinate has absolute value 0, the other has absolute value 1, signs are recovered, and `ext <;> simp` closes the concrete coordinate equality. A helper lemma could compress this, although the current explicit four-way classification is quite readable.

## Optimization candidates

Three plausible improvements are:

1. Prove a more general lemma without `_hx`, for example `goldenUnitMeasure_eq_one_cases`, and make the present theorem a thin wrapper.
2. Remove the intermediate `hsum` and derive `hcases` directly from `hm` if elaboration and `omega` remain clear. The current line is nevertheless useful documentation.
3. Extract the repeated `natAbs = 1` sign-recovery pattern into a helper only if it is reused elsewhere; otherwise that may be over-abstraction.

From an API-design perspective, the first option is the strongest because it cleanly separates a pure integral-lattice fact from unit-specific logic.

## Required Mathlib imports and import optimization

The generated standalone `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the whole generated artifact.

The external facilities used by this theorem include at least:

- `Int.natAbs`
- `Int.natAbs_eq_zero`
- `Int.natAbs_eq_iff`
- `omega`
- structure extensionality
- `simp`

The project-side definitions `GoldenInt`, `GoldenUnit`, `goldenUnitMeasure`, `goldenOne`, and `goldenPhi` must of course come from preceding project modules.

`import Mathlib` is almost certainly broader than this declaration alone requires. However, no Lean build is performed in this task, so the exact minimal set of Mathlib modules is not confirmed. In particular, the smallest import combination providing both the integer `natAbs` API and `omega` would need to be checked by an actual build.

## Comparator challenge suitability

**Suitable; beginner difficulty.**

This is a particularly good micro challenge because it is almost entirely local and does not require understanding the global FLT5 development.

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  ?_
```

Useful evaluation points are whether a solver can:

1. notice that `_hx` is unnecessary,
2. reduce `A+B=1` to exactly two natural-number cases,
3. recover `±1` from `natAbs = 1`,
4. finish structure equalities with extensionality.

A harder variant could forbid `omega` and require use of standard `Nat` lemmas to classify the sum.

## Next declaration to read

The next declaration is **0357 `unit_order_pos_pos`**, a **`private theorem`**.

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  by_contra h
  have hab : b + 1 ≤ a := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

With the measure-one base case now complete, the development turns to local inequalities needed to shorten units of larger measure. In the positive-positive quadrant, the golden norm condition

$$
a^2+ab-b^2=\pm1
$$

forces

$$
a\le b.
$$

This inequality is later used in `goldenUnit_descent` so that multiplication by $\varphi^{-1}$ produces the coordinate difference $b-a\ge0$ and strictly decreases the measure.
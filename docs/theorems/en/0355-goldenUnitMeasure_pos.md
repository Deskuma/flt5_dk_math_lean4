# 0355 — `goldenUnitMeasure_pos`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
  simp only [goldenUnitMeasure]
  by_contra h
  have hz : x.fst.natAbs + x.snd.natAbs = 0 := Nat.eq_zero_of_not_pos h
  have haf : x.fst.natAbs = 0 := by omega
  have hbf : x.snd.natAbs = 0 := by omega
  have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
  have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
  rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

## Lean type

```lean
goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
  0 < goldenUnitMeasure x
```

Given a golden integer `x` together with a proof `hx : GoldenUnit x`, the theorem proves that its coordinate measure

$$
\mu(x)=|x.\mathrm{fst}|+|x.\mathrm{snd}|
$$

is positive.

## Mathematical statement

Write

$$
x=a+b\varphi.
$$

Declaration 0354 defined

$$
\mu(x)=|a|+|b|.
$$

The present theorem states that if `x` is a unit, then

$$
0<|a|+|b|.
$$

The reason is elementary. If

$$
|a|+|b|=0,
$$

then nonnegativity of natural numbers forces

$$
a=0,
\qquad
b=0.
$$

Thus `x` is the zero element. But a golden-order unit must have norm $1$ or $-1$, while the norm of the zero element is $0$, which is impossible.

Therefore a unit never lies at the coordinate origin, and its natural-valued coordinate measure is at least one.

## Role in the full proof

This theorem supplies the **lower-bound condition** for the natural-number descent in `GoldenUnitClassification`.

Later the proof sets `goldenUnitMeasure x = n` and performs strong induction on `n` using `Nat.strong_induction_on`. For this to work cleanly on units, the case $n=0$ must be impossible. The present theorem provides exactly that fact:

$$
1\le \mu(x).
$$

The proof architecture is therefore

```text
GoldenUnit x
    ↓
goldenNorm x = ±1
    ↓
x ≠ 0
    ↓
goldenUnitMeasure x ≠ 0
    ↓
0 < goldenUnitMeasure x
    ↓
measure = 1 becomes the base case
    ↓
measure > 1 is shortened by goldenUnit_descent
```

Thus 0354 introduced the descent measure itself, while 0355 controls its minimum value on units.

## Direct dependencies

The main direct dependencies are:

- `GoldenUnit` — the predicate asserting that `x` is a unit in the golden order;
- `goldenUnitMeasure` — declaration 0354, defined as `x.fst.natAbs + x.snd.natAbs`;
- `goldenNorm_eq_one_or_neg_one_of_unit` — gives that the norm of a unit is $1$ or $-1$;
- `goldenNorm` — the quadratic norm on golden integers;
- `Nat.eq_zero_of_not_pos` — converts failure of positivity of a natural number into equality with zero;
- `Int.natAbs_eq_zero` — relates `natAbs a = 0` to `a = 0`;
- `omega` — derives that each summand is zero from a natural-number sum equal to zero;
- `simp` — computes the norm at zero coordinates and closes the contradictions $0=1$ and $0=-1$.

Declarations 0352 `golden_mul_phi_coords` and 0353 `golden_mul_phiInv_coords` are not direct dependencies of this theorem. They are used later to prove strict decrease of `goldenUnitMeasure`.

## Proof flow

### 1. Extract the unit norm information

```lean
have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
```

This produces information equivalent to

```lean
hn : goldenNorm x = 1 ∨ goldenNorm x = -1
```

### 2. Unfold the measure

```lean
simp only [goldenUnitMeasure]
```

The goal becomes

```lean
0 < x.fst.natAbs + x.snd.natAbs
```

### 3. Assume that positivity fails

```lean
by_contra h
```

Since the quantity is natural-valued, failure of positivity implies that it is zero:

```lean
have hz : x.fst.natAbs + x.snd.natAbs = 0 :=
  Nat.eq_zero_of_not_pos h
```

### 4. Show that both coordinate absolute values are zero

```lean
have haf : x.fst.natAbs = 0 := by omega
have hbf : x.snd.natAbs = 0 := by omega
```

Here `omega` solves only the Presburger-arithmetic fact that if natural numbers $A,B$ satisfy $A+B=0$, then $A=B=0$.

### 5. Recover zero integer coordinates

```lean
have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
```

Now `x` is known to be the coordinate origin.

### 6. Contradict the unit norm

```lean
rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

After computing `goldenNorm ⟨0,0⟩ = 0`, the two branches reduce to

$$
0=1,
\qquad
0=-1,
$$

both of which are discharged by `simp`.

## Lean-specific processing

### `by_contra` and natural-number order

On paper one may simply start with “suppose the measure is zero.” In Lean the goal is `0 < ...`, so the proof first obtains `¬ 0 < ...` with `by_contra h`, then converts that statement into equality with zero using `Nat.eq_zero_of_not_pos`.

### Returning from `natAbs` to integers

Using `Int.natAbs` makes the descent measure natural-valued, which is ideal for well-founded induction. At the contradiction stage, however, the proof must return to integer coordinates in order to evaluate `goldenNorm`. The bridge is

```lean
Int.natAbs_eq_zero.mp
```

which converts

```text
natAbs coordinate = 0
        ↓
integer coordinate = 0
```

### The role of `omega`

`omega` is not proving any algebra about the golden order here. It is used only for the arithmetic consequence of

```lean
A + B = 0
```

over natural numbers.

### The final `<;>` compression

```lean
rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

splits the $+1$ and $-1$ norm cases and applies the same simplification to both branches.

## Redundancy and duplication

The proof is short and contains little genuine redundancy. Two possible cleanup points are:

1. `haf` and `hbf` are separately extracted from `hz` by two calls to `omega`; if a suitable standard theorem such as an additive zero decomposition lemma fits the exact types, both facts could potentially be obtained by one structural decomposition.
2. If the surrounding API already provides a convenient theorem that every unit is nonzero, one could prove measure positivity from `x ≠ 0` instead of routing through `goldenNorm_eq_one_or_neg_one_of_unit`.

The second route is not necessarily shorter. The current argument uses an important local theorem about unit norms and makes the contradiction mathematically explicit.

## Optimization candidates

Possible local refinements are:

- replace the two `omega` calls that split `A + B = 0` with a standard addition-equals-zero theorem if one integrates cleanly;
- prove a reusable lemma `goldenUnitMeasure x = 0 ↔ x = 0`, after which the present theorem could be obtained by combining that lemma with nonzeroness of units;
- introduce `goldenUnitMeasure_ne_zero` if the nonzero form is repeatedly needed downstream.

However, the current proof has the advantage that it does not over-abstract a fact used only locally. Unless later reuse is established, the present formulation is already reasonable.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` imports

```lean
import Mathlib
```

for the entire development.

At the level of this theorem, the externally needed facilities include at least:

- `Int.natAbs` and `Int.natAbs_eq_zero`;
- natural-number order and addition;
- `omega`;
- `simp`.

The real module must additionally import the project modules that provide `GoldenInt`, `GoldenUnit`, `goldenNorm`, `goldenNorm_eq_one_or_neg_one_of_unit`, and `goldenUnitMeasure`.

The standalone-wide `import Mathlib` is almost certainly broader than this declaration alone requires. No Lean build is performed in this task, so the exact minimal set of Mathlib module imports is not confirmed. Any import minimization should be validated by an actual build, especially for the integer absolute-value API and `omega`.

## Comparator challenge suitability

**Yes. Difficulty: beginner to intermediate.**

A good challenge form is to provide the definition and the unit-norm theorem and leave only the proof hole:

```lean
theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  ?_
```

The essential reasoning chain is:

1. a unit has norm $\pm1$;
2. if the measure is not positive, then as a natural number it is zero;
3. a sum of two absolute values is zero only when both coordinates are zero;
4. zero coordinates give norm zero;
5. $0\neq\pm1$.

For Comparator, one can make two variants: one permitting `omega`, and another requiring only standard decomposition lemmas for a zero sum. This separates tactic-based Presburger reasoning from library-search ability.

## Next declaration to read

The next declaration is **0356 `goldenUnit_measure_one_cases`**, again a **`theorem`**.

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  ...
```

Now that 0355 excludes measure zero for units, the next theorem completely classifies the minimum case

$$
\mu(x)=1.
$$

For integer coordinates, an absolute-value sum equal to one forces

$$
(|a|,|b|)=(1,0)
\quad\text{or}\quad
(0,1).
$$

Restoring signs gives

$$
x\in\{1,-1,\varphi,-\varphi\}.
$$

These four elements become the concrete base cases for the later strong-induction classification of all golden units.
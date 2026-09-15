# 0358 — `unit_order_pos_neg`

## Declaration kind

This declaration is a **`private theorem`**.

It is an internal auxiliary theorem of `GoldenUnitClassification.lean`, not part of the public API. It is the sign-split companion of 0357 `unit_order_pos_pos`.

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  by_contra h
  have hab : a + 1 ≤ -b := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a + b)]
```

## Lean type

```lean
unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a)
    (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) :
  -b ≤ a
```

If a positive integer `a` and a negative integer `b` make the quadratic form appearing in the golden norm,

$$
a^2+ab-b^2,
$$

equal to either $1$ or $-1$, then the absolute size of the negative coordinate cannot exceed the positive one:

$$
-b\le a.
$$

Since `b < 0`, one has $-b=|b|$, so the mathematical content is

$$
|b|\le a.
$$

## Mathematical statement

For a golden integer

$$
x=a+b\varphi,
$$

write the norm quadratic form as

$$
Q(a,b)=a^2+ab-b^2.
$$

The theorem assumes

$$
a>0,\qquad b<0,\qquad Q(a,b)=\pm1
$$

and proves

$$
-b\le a.
$$

Negating the conclusion gives

$$
a<-b.
$$

Because `a` and `b` are integers, this strengthens discretely to

$$
a+1\le -b.
$$

That one-step gap is incompatible with $Q(a,b)=\pm1$.

The explicit nonnegativity fact supplied to the nonlinear arithmetic solver is

$$
(a+b)^2\ge0.
$$

In the positive-negative sign region, `a + b` directly measures the signed difference between the two coordinate magnitudes, so `(a+b)^2` is the natural companion to the `(a-b)^2` used in 0357.

## Role in the full proof

This theorem supplies the **order constraint needed for the two mixed-sign branches of `goldenUnit_descent`**.

The later descent theorem splits the coordinates of a unit `x` into four sign regions. In the mixed-sign regions:

- for `x.fst < 0 < x.snd`, signs are flipped and this theorem is applied to the negated coordinates;
- for `0 < x.fst` and `x.snd < 0`, this theorem is applied directly.

In the latter branch, the source uses

```lean
have hord : -x.snd ≤ x.fst := unit_order_pos_neg ha hb hn
let y := goldenMul x goldenPhi
```

By 0352 `golden_mul_phi_coords`, multiplication by $\varphi$ acts by

$$
(a,b)\xmapsto{\cdot\varphi}(b,a+b).
$$

Because $a>0>b$ and $-b\le a$, one gets

$$
a+b\ge0.
$$

Hence the new measure is

$$
\mu((a+b\varphi)\varphi)
  =|b|+|a+b|
  =-b+(a+b)
  =a.
$$

The original measure is

$$
\mu(a+b\varphi)=a+(-b).
$$

Since $b<0$, one has $-b>0$, and therefore

$$
a<a-b.
$$

Thus the measure strictly decreases.

The theorem therefore converts the algebraic condition that the golden norm is $\pm1$ into the signed coordinate inequality needed for a natural-number strict descent.

## Direct dependencies

The theorem is deliberately localized to integer arithmetic: its type mentions neither `GoldenInt` nor `GoldenUnit`.

Its direct ingredients are:

- `ℤ` for the coordinate type;
- integer order and negation;
- `omega`, which turns `¬ (-b ≤ a)` into the discrete inequality
  $$
  a+1\le -b;
  $$
- `sq_nonneg (a + b)`, supplying
  $$
  0\le(a+b)^2;
  $$
- `nlinarith`, which combines the sign assumptions, the discrete order bound, and each of the norm cases $+1$ and $-1$;
- `rcases`, which splits the disjunction `hn`.

Conceptually, `goldenNorm_eq_one_or_neg_one_of_unit hx` later supplies the hypothesis `hn` inside `goldenUnit_descent`, but this private theorem itself does not depend on that project-specific API.

## Proof flow

### 1. Negate the conclusion

```lean
by_contra h
```

This negates the target `-b ≤ a`.

### 2. Extract the discrete integer gap

```lean
have hab : a + 1 ≤ -b := by omega
```

Over the integers,

$$
-b>a
$$

implies

$$
a+1\le-b.
$$

`omega` handles this one-step lattice strengthening.

### 3. Split the norm sign

```lean
rcases hn with hn | hn
```

The proof now treats separately

$$
Q(a,b)=1
$$

and

$$
Q(a,b)=-1.
$$

### 4. Close both branches by nonlinear arithmetic

```lean
nlinarith [sq_nonneg (a + b)]
```

The assumptions `ha`, `hb`, `hab`, the relevant branch of `hn`, and

$$
(a+b)^2\ge0
$$

are sufficient for `nlinarith` to derive a contradiction in either case.

The `<;>` combinator applies the same closing tactic to both branches of the disjunction.

## Lean-specific processing

### `private theorem`

Mathematically this is an independent fact about an integer quadratic form, but in the current design it is intentionally kept as an implementation detail of `GoldenUnitClassification`. This avoids expanding the public namespace while isolating the local arithmetic needed by the descent.

### Division of labor between `omega` and `nlinarith`

The tactics solve different parts of the proof.

`omega` handles the **linear discrete order** of integers and extracts

$$
\neg(-b\le a)\Longrightarrow a+1\le-b.
$$

`nlinarith` then handles the **nonlinear polynomial relations** involving

$$
a^2,\quad ab,\quad b^2,\quad (a+b)^2.
$$

The explicit one-unit gap obtained by `omega` is important: it gives more information than the corresponding real strict inequality and is what clashes with the norm value $\pm1$.

### `sq_nonneg (a + b)`

In the mixed-sign region, `a+b` is essentially $a-|b|$. Its square is supplied explicitly so that `nlinarith` can compare the quadratic form with the coordinate-order assumptions.

## Redundancy and duplication

The proof skeleton is almost identical to 0357 `unit_order_pos_pos`.

0357 uses

```lean
have hab : b + 1 ≤ a := by omega
rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

whereas 0358 uses

```lean
have hab : a + 1 ≤ -b := by omega
rcases hn with hn | hn <;> nlinarith [sq_nonneg (a + b)]
```

The differences are exactly the order target and the auxiliary square dictated by the sign region.

This duplication could potentially be abstracted, but the current short pair of lemmas maps very directly onto the sign cases of the descent and is easy to read.

## Optimization candidates

1. Investigate whether `unit_order_pos_pos` and `unit_order_pos_neg` can be derived from one common lemma after an appropriate sign transformation.
2. Since this theorem is independent of `GoldenInt`, consider making it reusable outside the module if the same quadratic-form order fact is needed elsewhere.
3. Replace the `nlinarith` proof with an explicit factorization or lower-bound lemma if reducing tactic dependence is desirable.
4. The positive-negative and negative-positive branches of `goldenUnit_descent` may themselves admit a symmetry abstraction by sign negation.

The validity of such replacement proofs has not been checked here because no Lean build is performed in this task.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` imports

```lean
import Mathlib
```

for the development as a whole.

For this theorem alone, the main facilities are:

- integers `ℤ` and their linear order;
- `omega`;
- `nlinarith`;
- `sq_nonneg`.

Therefore `import Mathlib` is likely broader than necessary for the isolated declaration. A smaller set based around `Mathlib.Tactic.Omega`, `Mathlib.Tactic.Nlinarith`, and the basic integer/order/ring imports may suffice.

However, because no Lean build is run here, the **exact minimal import set is unverified**.

## Comparator challenge suitability

 **Suitable. Difficulty: beginner to intermediate.**

It can be extracted almost unchanged as a small integer-arithmetic challenge with no project-specific definitions:

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  ?_
```

A Comparator task can test whether a solver can:

1. derive `a + 1 ≤ -b` from the negated goal;
2. split the $+1/-1$ disjunction correctly;
3. identify `(a+b)^2 ≥ 0` as the useful auxiliary inequality;
4. combine `omega` and `nlinarith` with the right division of labor.

Pairing it with 0357 is even more informative: the challenge can ask the model to choose between `(a-b)^2` and `(a+b)^2` according to the sign region, which tests structural understanding rather than tactic imitation.

## Next declaration to read

The next declaration is 0359 `goldenUnit_descent`, of kind **`theorem`**.

```lean
/-- Every non-base golden unit can be shortened by one multiplication by `phi`
or its integral inverse. -/
theorem goldenUnit_descent {x : GoldenInt} (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
    ∃ y : GoldenInt,
      GoldenUnit y ∧
      goldenUnitMeasure y < goldenUnitMeasure x ∧
      (x = goldenMul y goldenPhi ∨
        x = goldenMul y goldenPhiInv) := by
  ...
```

With 0357 and 0358, the sign-specific order lemmas are complete. Declaration 0359 applies them across all four coordinate quadrants and constructs the actual descent step by multiplying once by `goldenPhi` or `goldenPhiInv`, strictly decreasing `goldenUnitMeasure`.
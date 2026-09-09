# 0357 — `unit_order_pos_pos`

## Declaration kind

This declaration is a **`private theorem`**.

Because it is `private`, it is an internal helper theorem of `GoldenUnitClassification.lean`, not part of the module's public API.

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  by_contra h
  have hab : b + 1 ≤ a := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

## Lean type

```lean
unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) :
  a ≤ b
```

For positive integer coordinates `a` and `b`, if the quadratic form appearing as the golden-integer norm,

$$
a^2+ab-b^2,
$$

has value $1$ or $-1$, then necessarily

$$
a\le b.
$$

The helper itself does not take a `GoldenInt` or a `GoldenUnit`. It isolates only the integer-arithmetic conditions needed later.

## Mathematical statement

For a golden integer

$$
x=a+b\varphi,
$$

the norm used in this development appears in coordinates as

$$
N(x)=a^2+ab-b^2.
$$

For a unit, an earlier result supplies

$$
N(x)\in\{1,-1\}.
$$

This theorem handles the first quadrant

$$
a>0,\qquad b>0.
$$

If one assumes instead that $a>b$, discreteness of the integers strengthens this to

$$
b+1\le a.
$$

Under that condition the quadratic form $a^2+ab-b^2$ cannot equal either $1$ or $-1$, giving a contradiction. Hence

$$
a\le b.
$$

Intuitively, positive-positive coordinates of a golden unit cannot grow in an arbitrary direction: the norm-$\pm1$ hyperbolic constraint forces the `a` coordinate not to exceed the `b` coordinate in this sign region.

## Role in the full proof

This theorem is the first **sign-specific ordering lemma that makes the strict descent work** in `GoldenUnitClassification`.

It is followed immediately by `unit_order_pos_neg`, which handles a mixed-sign region. Later, `goldenUnit_descent` chooses multiplication by `goldenPhi` or `goldenPhiInv` according to coordinate signs so that the coordinate measure decreases.

In the branch where both coordinates are positive, the repository uses the theorem exactly in this way:

```lean
have hord : x.fst ≤ x.snd := unit_order_pos_pos ha hb hn
let y := goldenMul x goldenPhiInv
refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
```

Using the coordinate formula from 0353,

$$
(a,b)\xmapsto{\cdot\varphi^{-1}}(b-a,a),
$$

the inequality $a\le b$ supplied here guarantees $b-a\ge0$. Therefore the new measure is

$$
\mu((a+b\varphi)\varphi^{-1})
  =|b-a|+|a|
  =(b-a)+a
  =b.
$$

The original measure is

$$
\mu(a+b\varphi)=a+b.
$$

Since $a>0$,

$$
b<a+b,
$$

so the measure decreases strictly.

Thus this helper is not merely an ordering fact: it is the sign control that converts the coordinate transformation of 0353 into a well-founded descent on natural numbers.

## Direct dependencies

This `private theorem` is deliberately factored into local arithmetic and directly refers to no project-specific definitions.

Its direct ingredients are:

- `ℤ` — the type of coordinates `a` and `b`.
- `omega` — derives `b + 1 ≤ a` from `¬ a ≤ b` using discrete integer order.
- `sq_nonneg (a - b)` — supplies
  $$
  0\le(a-b)^2
  $$
  to `nlinarith`.
- `nlinarith` — combines positivity, ordering, the norm equation, and square nonnegativity to close both contradiction branches.
- `rcases` — splits the two alternatives in `hn`.

Conceptually, `goldenNorm_eq_one_or_neg_one_of_unit` supplies `hn` later in the descent proof, but that theorem does not occur in this helper's type. This is a clean separation of dependencies.

## Proof flow

### 1. Negate the desired ordering

```lean
by_contra h
```

The goal `a ≤ b` is negated, giving an integer-order hypothesis

```lean
h : ¬ a ≤ b
```

in the contradiction context.

### 2. Strengthen strict order using discreteness

```lean
have hab : b + 1 ≤ a := by omega
```

For integers, `a > b` means there is at least one full integer step between the coordinates:

$$
a>b
\quad\Longrightarrow\quad
b+1\le a.
$$

`omega` extracts precisely this discrete-order consequence.

### 3. Split the two possible norm values

```lean
rcases hn with hn | hn
```

The proof now treats separately

$$
a^2+ab-b^2=1
$$

and

$$
a^2+ab-b^2=-1.
$$

### 4. Close both branches by nonlinear arithmetic

```lean
nlinarith [sq_nonneg (a - b)]
```

Together with `ha`, `hb`, `hab`, the branch-specific `hn`, and

$$
(a-b)^2\ge0,
$$

`nlinarith` derives a contradiction in either branch.

The `<;>` combinator applies the same `nlinarith` call to both branches produced by `rcases`, keeping the proof compact.

## Lean-specific processing

### `private theorem`

The helper does not enlarge the namespace's public API and is used only inside `GoldenUnitClassification`. Mathematically it is an independent lemma about an integer quadratic form, but the current design treats it as an implementation detail of unit descent.

### Division of labor between `omega` and `nlinarith`

The tactics perform different tasks.

`omega` handles **discrete linear integer order**, producing

$$
\neg(a\le b)\Longrightarrow b+1\le a.
$$

`nlinarith` then handles the **nonlinear polynomial relations** involving

$$
a^2,\ ab,\ b^2,\ (a-b)^2.
$$

This split assigns integer discreteness and nonlinear algebra to tools suited to each job.

### `sq_nonneg`

`nlinarith` should not be assumed to invent every useful square-nonnegativity fact automatically, so the proof explicitly passes

```lean
sq_nonneg (a - b)
```

as an additional polynomial inequality.

## Redundancy and duplication

There is little obvious redundancy inside this short proof itself.

However, subsequent local lemmas such as `unit_order_pos_neg` treat the same quadratic-form condition

$$
a^2+ab-b^2=\pm1
$$

in different sign regions. They potentially share the same skeleton:

1. negate the desired order,
2. use `omega` to obtain a one-step integer separation,
3. split the two norm values,
4. close with `nlinarith` and an appropriate square-nonnegativity fact.

On the other hand, each sign region requires a different ordering conclusion and later selects a different unit action in the descent, so keeping the helpers small and separate improves readability.

## Optimization candidates

Possible improvements are:

1. investigate whether the common nonlinear arithmetic of the positive-positive, positive-negative, and other sign cases can be factored into a general lemma about the norm quadratic form;
2. because `unit_order_pos_pos` does not depend on `GoldenInt`, consider making it a reusable public quadratic-form lemma if another module needs the same fact;
3. investigate whether `sq_nonneg (a - b)` is the best minimal auxiliary inequality, or whether a more explicit factorization or lower-bound lemma could reduce tactic dependence.

Candidates 1 and 3 require an actual Lean build to confirm replacement proofs, so they are recorded only as optimization possibilities here.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

for the whole development.

The principal external facilities needed by this theorem itself are:

- integers `ℤ` and their linear order,
- `omega`,
- `nlinarith`,
- `sq_nonneg`.

Therefore `import Mathlib` is likely broader than necessary for this declaration alone. A smaller set involving `Mathlib.Tactic.Omega`, `Mathlib.Tactic.Nlinarith`, and the basic integer ordered-ring modules may suffice.

Because no Lean build is run in this task, **the exact minimal import set is not verified**.

## Suitability as a Comparator challenge

 **Yes. Difficulty: beginner to intermediate.**

The statement can be isolated as a local integer-quadratic-form problem without requiring knowledge of the whole FLT5 development.

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  ?_
```

Useful evaluation points are whether a solver can:

1. turn `by_contra` into the discrete integer bound `b + 1 ≤ a`,
2. split the disjunction in `hn` correctly,
3. discover the useful auxiliary fact `sq_nonneg (a - b)`,
4. assign the linear and nonlinear parts appropriately to `omega` and `nlinarith`.

A stronger variant could forbid `nlinarith` and require an explicit lower-bound derivation for the quadratic form, making the mathematical structure more visible.

## Next declaration to read

The next declaration is 0358 `unit_order_pos_neg`, also a **`private theorem`**.

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  by_contra h
  have hab : a + 1 ≤ -b := by omega
  ...
```

Where 0357 establishes $a\le b$ in the positive-positive region, 0358 establishes

$$
-b\le a
$$

in the positive-negative region. This supplies the corresponding sign control for choosing the unit action that decreases the measure in the next branch of `goldenUnit_descent`.

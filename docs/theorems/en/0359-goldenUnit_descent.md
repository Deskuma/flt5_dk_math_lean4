# 0359 — `goldenUnit_descent`

## Declaration kind

This declaration is a **`theorem`**.

It is the central strict-descent theorem for unit classification in `GoldenUnitClassification.lean`, combining the inverse identities, coordinate transformations, natural-valued measure, and sign-dependent order lemmas prepared in 0352–0358.

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
  have hn : x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = 1 ∨
      x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = -1 := by
    simpa [goldenNorm] using goldenNorm_eq_one_or_neg_one_of_unit hx
  have ha0 : x.fst ≠ 0 := by
    intro ha
    have hb2 : x.snd ^ 2 = 1 := by
      rcases hn with hn | hn
      · rw [ha] at hn
        norm_num at hn
        nlinarith [sq_nonneg x.snd]
      · rw [ha] at hn
        norm_num at hn ⊢
        exact hn
    have hb : x.snd = 1 ∨ x.snd = -1 := sq_eq_one_iff.mp hb2
    rcases hb with hb | hb <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  have hb0 : x.snd ≠ 0 := by
    intro hb
    have ha2 : x.fst ^ 2 = 1 := by
      rcases hn with hn | hn
      · simpa [hb] using hn
      · simp [hb] at hn
        nlinarith [sq_nonneg x.fst]
    have ha : x.fst = 1 ∨ x.fst = -1 := sq_eq_one_iff.mp ha2
    rcases ha with ha | ha <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  rcases lt_or_gt_of_ne ha0 with ha | ha <;>
    rcases lt_or_gt_of_ne hb0 with hb | hb
  · -- both coordinates are negative
    have hord : -x.fst ≤ -x.snd := by
      apply unit_order_pos_pos (a := -x.fst) (b := -x.snd) <;> try omega
      simpa only [neg_sq, neg_mul_neg] using hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have hba : x.snd - x.fst ≤ 0 := by omega
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ x.fst - x.snd by omega)
      rw [show (x.snd - x.fst).natAbs = (x.fst - x.snd).natAbs by
        rw [show x.snd - x.fst = -(x.fst - x.snd) by ring, Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp
  · -- negative, positive
    have hord : x.snd ≤ -x.fst := by
      have h := unit_order_pos_neg (a := -x.fst) (b := -x.snd)
        (by omega) (by omega) (by simpa only [neg_sq, neg_mul_neg] using hn)
      omega
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg hb.le
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -(x.fst + x.snd) by omega)
      rw [show (x.fst + x.snd).natAbs = (-(x.fst + x.snd)).natAbs by
        rw [Int.natAbs_neg]]
      have h3 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- positive, negative
    have hord : -x.snd ≤ x.fst := unit_order_pos_neg ha hb hn
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ -x.snd by omega)
      rw [show x.snd.natAbs = (-x.snd).natAbs by rw [Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ x.fst + x.snd by omega)
      have h3 := Int.natAbs_of_nonneg ha.le
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- both coordinates are positive
    have hord : x.fst ≤ x.snd := unit_order_pos_pos ha hb hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (sub_nonneg.mpr hord)
      have h2 := Int.natAbs_of_nonneg ha.le
      have h3 := Int.natAbs_of_nonneg hb.le
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp
```

## Lean type

```lean
goldenUnit_descent {x : GoldenInt}
    (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
  ∃ y : GoldenInt,
    GoldenUnit y ∧
    goldenUnitMeasure y < goldenUnitMeasure x ∧
    (x = goldenMul y goldenPhi ∨
      x = goldenMul y goldenPhiInv)
```

The inputs are a golden integer `x` together with

- `hx : GoldenUnit x`, asserting that `x` is a unit, and
- `hlarge : 1 < goldenUnitMeasure x`, asserting that `x` is not one of the measure-one base units.

The output is the existence of a smaller unit `y` satisfying

$$
\mu(y)<\mu(x),
$$

while preserving an exact one-step reconstruction of the original element:

$$
x=y\varphi
$$

or

$$
x=y\varphi^{-1}.
$$

Here

$$
\mu(a+b\varphi)=|a|+|b|.
$$

## Mathematical statement

For a golden integer

$$
x=a+b\varphi
$$

that is a unit, its norm satisfies

$$
N(x)=a^2+ab-b^2=\pm1.
$$

If in addition $\mu(x)>1$, neither coordinate can be zero. Thus $(a,b)$ lies in one of the four open sign quadrants. The norm condition, together with the order lemmas 0357 and 0358, determines whether one should set

$$
y=x\varphi
$$

or

$$
y=x\varphi^{-1}.
$$

The coordinate transformations from 0352 and 0353 are

$$
(a,b)\xmapsto{\cdot\varphi}(b,a+b),
$$

and

$$
(a,b)\xmapsto{\cdot\varphi^{-1}}(b-a,a).
$$

In every quadrant the appropriate choice strictly decreases the coordinate measure. This supplies a well-founded descent on natural numbers.

## Role in the whole proof

This theorem is the core of `GoldenUnitClassification.lean`.

The later theorem `goldenUnitFifthClass_of_unit` performs strong induction on `goldenUnitMeasure x`:

- at measure 1, 0356 `goldenUnit_measure_one_cases` classifies the unit as one of `±1, ±φ`;
- above measure 1, the present theorem descends to a smaller unit `y`, and the induction hypothesis is applied to `y`.

The reconstruction clause

```lean
x = goldenMul y goldenPhi ∨
x = goldenMul y goldenPhiInv
```

is essential. It is not enough to know merely that a smaller unit exists. After classifying `y` modulo fifth powers, the proof must move one step by `φ` or `φ⁻¹` to recover the class of `x`.

Conceptually, the theorem provides the bridge

$$
\text{unit norm }\pm1
\longrightarrow
\text{sign-dependent order constraints}
\longrightarrow
\text{strict coordinate descent}
\longrightarrow
\text{finite unit-class classification}.
$$

## Direct dependencies

The project-level definitions and lemmas used directly or essentially are:

- `GoldenInt` — the coordinate type of golden integers;
- `GoldenUnit` — the predicate expressing existence of a two-sided inverse;
- `goldenNorm` — the quadratic norm $a^2+ab-b^2$;
- `goldenNorm_eq_one_or_neg_one_of_unit` — a unit has norm $\pm1$;
- `goldenUnitMeasure` — the measure $|a|+|b|$;
- `unit_order_pos_pos` — 0357, giving the same-sign order constraint;
- `unit_order_pos_neg` — 0358, giving the mixed-sign order constraint;
- `goldenPhi`, `goldenPhiInv` — the unit used for the descent and its integral inverse;
- `goldenUnit_phi`, `goldenUnit_phiInv` — proofs that these elements are units;
- `goldenUnit_mul` — closure of units under multiplication;
- `golden_mul_phi_coords` — the map $(a,b)\mapsto(b,a+b)$;
- `golden_mul_phiInv_coords` — the map $(a,b)\mapsto(b-a,a)$;
- `golden_phi_mul_inv`, `golden_inv_mul_phi` — the two inverse identities.

The main Mathlib-level tools are:

- `sq_eq_one_iff`,
- `lt_or_gt_of_ne`,
- `Int.natAbs_of_nonneg`, `Int.natAbs_neg`,
- `omega`, `nlinarith`, `norm_num`, `simp`, and `ring`.

## Proof / construction flow

### 1. Expand the unit norm into coordinates

The proof first turns the abstract unit condition into an integer quadratic equation:

```lean
have hn : x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = 1 ∨
    x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = -1 := by
  simpa [goldenNorm] using goldenNorm_eq_one_or_neg_one_of_unit hx
```

Thus the remaining argument works with explicit coordinates.

### 2. Exclude zero coordinates

If `x.fst = 0`, the norm equation forces

$$
x.snd^2=1,
$$

hence `x.snd = ±1`. Then the measure equals 1, contradicting `hlarge`.

Similarly, if `x.snd = 0`, then

$$
x.fst^2=1,
$$

again forcing measure 1.

Therefore

$$
a\ne0,\qquad b\ne0.
$$

This makes the four-quadrant split exhaustive.

### 3. Split into four sign quadrants

```lean
rcases lt_or_gt_of_ne ha0 with ha | ha <;>
  rcases lt_or_gt_of_ne hb0 with hb | hb
```

produces the four cases

1. $a<0,b<0$,
2. $a<0,b>0$,
3. $a>0,b<0$,
4. $a>0,b>0$.

### 4. Negative / negative

Applying 0357 to $(-a,-b)$ yields

$$
-a\le-b.
$$

The proof chooses

$$
y=x\varphi^{-1}.
$$

Its coordinates are

$$
y=(b-a)+a\varphi.
$$

The sign conditions and order constraint allow the `natAbs` terms to be rewritten so that `omega` proves strict decrease.

Unitness is preserved by

```lean
goldenUnit_mul hx goldenUnit_phiInv
```

and reconstruction follows from

$$
y\varphi=x\varphi^{-1}\varphi=x,
$$

using `golden_inv_mul_phi`. Thus this branch returns

```lean
x = goldenMul y goldenPhi.
```

### 5. Negative / positive

After sign reversal, 0358 gives

$$
b\le-a.
$$

Here the proof chooses

$$
y=x\varphi,
$$

whose coordinates are

$$
y=b+(a+b)\varphi.
$$

Since $b>0$ and $a+b\le0$,

$$
\mu(y)=b-(a+b)=-a,
$$

whereas

$$
\mu(x)=-a+b.
$$

Because $b>0$,

$$
\mu(y)<\mu(x).
$$

Reconstruction is

$$
y\varphi^{-1}=x,
$$

so the right reconstruction branch is returned.

### 6. Positive / negative

Using 0358 directly gives

$$
-b\le a.
$$

Again set

$$
y=x\varphi.
$$

Now $a+b\ge0$, so

$$
\mu(y)=-b+(a+b)=a,
$$

while

$$
\mu(x)=a-b.
$$

Since $b<0$, strict decrease follows.

The reconstruction is again the right branch via `golden_phi_mul_inv`.

### 7. Positive / positive

Lemma 0357 gives

$$
a\le b.
$$

The proof chooses

$$
y=x\varphi^{-1},
$$

with coordinates

$$
y=(b-a)+a\varphi.
$$

Both coordinates are nonnegative, hence

$$
\mu(y)=(b-a)+a=b.
$$

The original measure is

$$
\mu(x)=a+b.
$$

Since $a>0$,

$$
\mu(y)<\mu(x).
$$

The reconstruction is the left branch, using `golden_inv_mul_phi`.

## Lean-specific processing

### `sq_eq_one_iff`

When one coordinate is zero, the norm equation gives `x.snd ^ 2 = 1` or `x.fst ^ 2 = 1`. `sq_eq_one_iff` converts this into the concrete alternatives `= 1 ∨ = -1`.

This lets

```lean
simp [goldenUnitMeasure, ...] at hlarge
```

close the contradiction with the assumption that the measure is greater than 1.

### `lt_or_gt_of_ne`

A nonzero coordinate in a linear order is either negative or positive. Applying this to both coordinates enumerates the four quadrants with no omitted case.

### `Int.natAbs_of_nonneg` and `Int.natAbs_neg`

Because `goldenUnitMeasure` is natural-valued, the proof must eliminate integer absolute values before `omega` can solve the final strict inequalities cleanly. Once each sign is known, the `natAbs` terms are rewritten into ordinary nonnegative integer expressions.

### `let y := ...` and `dsimp [y]`

Each branch fixes an explicit descent witness. The same term is then returned as the existential witness, while `dsimp [y]` unfolds it before applying the coordinate formulas 0352 or 0353.

### `mul_assoc` in reconstruction

To recover `x` from `y=xφ^{-1}` or `y=xφ`, multiplication is reassociated so that

$$
\varphi^{-1}\varphi=1,
\qquad
\varphi\varphi^{-1}=1
$$

can be rewritten using 0349 and 0350.

## Redundancy and repeated structure

The four branches follow nearly the same pattern:

1. obtain an order inequality,
2. define `y := x * φ` or `x * φInv`,
3. preserve unitness with `goldenUnit_mul`,
4. expand coordinates,
5. remove `natAbs` using sign information,
6. use `omega` for strict decrease,
7. reconstruct `x` with an inverse identity.

The negative/positive and positive/negative branches are especially close because both use `φ`. Likewise, the negative/negative and positive/positive branches both use `φInv`.

However, the explicit four-quadrant form has an important readability advantage: the direction of contraction is visible directly from the code. Aggressive abstraction could hide the descent geometry.

## Optimization candidates

1. Extract the quadrant-specific measure calculations into lemmas about `natAbs`, shortening the body of `goldenUnit_descent`.
2. Use sign-reversal symmetry to unify the negative/negative with positive/positive branches, and the negative/positive with positive/negative branches.
3. Combine 0357, 0358, and the sign analysis into a higher-level lemma choosing a contraction direction for every norm-$\pm1$ unit.
4. Replace repeated `natAbs` rewrites with intermediate lemmas formulated using signed linear expressions or absolute values.
5. Factor the two reconstruction branches through common cancellation lemmas based on `golden_phi_mul_inv` and `golden_inv_mul_phi`.

These are design possibilities only. No Lean build was run in this pass, so the exact viability of the refactorings is unverified.

## Required Mathlib imports and import optimization

The generated standalone `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main Mathlib facilities exercised by this theorem are:

- integers `ℤ` and their linear order,
- `Int.natAbs`, `Int.natAbs_of_nonneg`, `Int.natAbs_neg`,
- `sq_eq_one_iff`, `sq_nonneg`,
- `lt_or_gt_of_ne`,
- `omega`,
- `nlinarith`,
- `norm_num`,
- `simp`,
- `ring`.

A Comparator-oriented standalone challenge could probably replace the broad `import Mathlib` with substantially narrower imports. On the tactic side, `Mathlib.Tactic.Omega`, `Mathlib.Tactic.Nlinarith`, `Mathlib.Tactic.Ring`, and `Mathlib.Tactic.NormNum` are natural candidates.

The **exact minimal import set is unverified**, because no Lean build was performed in this pass and the supporting `GoldenInt` / unit API also contributes dependencies.

## Comparator challenge suitability

 **Yes. Difficulty: intermediate to advanced.**

Unlike 0357 and 0358, this theorem is not merely an isolated integer-arithmetic lemma. It coordinates a significant part of the project-specific golden-integer API.

A useful challenge should provide at least

- `GoldenInt`,
- `GoldenUnit`,
- `goldenNorm`,
- `goldenUnitMeasure`,
- `goldenPhi`, `goldenPhiInv`,
- coordinate formulas 0352 and 0353,
- inverse identities 0349 and 0350,
- `goldenUnit_mul`, `goldenUnit_phi`, `goldenUnit_phiInv`,
- order lemmas 0357 and 0358,

and ask the solver to complete

```lean
theorem goldenUnit_descent {x : GoldenInt} (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
    ∃ y : GoldenInt,
      GoldenUnit y ∧
      goldenUnitMeasure y < goldenUnitMeasure x ∧
      (x = goldenMul y goldenPhi ∨
        x = goldenMul y goldenPhiInv) := by
  ?_
```

This tests whether the solver can

1. exclude zero coordinates from norm $\pm1$ and the large-measure hypothesis,
2. split the proof exhaustively into four sign quadrants,
3. choose the correct `φ` / `φInv` contraction direction,
4. apply 0357 and 0358 with the correct sign transformations,
5. normalize `natAbs` expressions and prove strict decrease,
6. reconstruct the original element using the inverse laws.

It is therefore a strong Comparator challenge for structural understanding, not merely tactic search.

## Next declaration to read

The next declaration is 0360 `GoldenUnitFifthClass`, of kind **`def`**.

```lean
/-- Existence of `i < 5` and `delta` with `x = phi^i * delta^5`. -/
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

By 0359, every non-base unit can be shortened by one descent step. Declaration 0360 now defines the target predicate that this descent will eventually establish.

Mathematically, it records membership in one of five unit classes modulo fifth powers:

$$
x=\varphi^i\delta^5,
\qquad 0\le i<5.
$$
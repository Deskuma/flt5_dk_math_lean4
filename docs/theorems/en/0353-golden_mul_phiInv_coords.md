# 0353 — `golden_mul_phiInv_coords`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ext <;> simp [goldenMul, goldenPhiInv]
  all_goals ring
```

## Lean type

```lean
golden_mul_phiInv_coords
    (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩
```

`GoldenInt` is the coordinate model for the golden integer ring $\mathbb Z[\varphi]$. For

$$
x=a+b\varphi,
$$

we read `x.fst = a` and `x.snd = b`.

Declaration 0348 introduced

```lean
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

which represents

$$
\varphi^{-1}=\varphi-1.
$$

The present theorem gives the exact coordinates obtained by multiplying an arbitrary golden integer by `goldenPhiInv`.

## Mathematical statement

Let $x=a+b\varphi$. Using

$$
\varphi^2=\varphi+1,
$$

we have

$$
(a+b\varphi)(\varphi-1)
=a\varphi-a+b\varphi^2-b\varphi.
$$

Substituting $\varphi^2=\varphi+1$ gives

$$
(a+b\varphi)(\varphi-1)
=b-a+a\varphi.
$$

Hence the coordinate transformation is

$$
(a,b)\longmapsto(b-a,a).
$$

The Lean right-hand side

```lean
⟨x.snd - x.fst, x.fst⟩
```

is exactly this transformation encoded as a `GoldenInt` constructor.

Together with 0352 `golden_mul_phi_coords`, which gives

$$
(a,b)\longmapsto(b,a+b),
$$

this theorem supplies the two coordinate actions corresponding to multiplication by $\varphi$ and $\varphi^{-1}$.

## Role in the whole proof

The purpose of `GoldenUnitClassification` is to move an arbitrary golden unit by multiplication with $\varphi$ or $\varphi^{-1}$ so that a coordinate measure strictly decreases until a base unit is reached.

Declaration 0352 gives the coordinate formula for the $\varphi$ direction. The present theorem 0353 gives the formula for the $\varphi^{-1}$ direction.

Immediately afterward the source defines

```lean
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

and `goldenUnit_descent` later uses the present theorem directly in branches of the form

```lean
let y := goldenMul x goldenPhiInv
```

followed by

```lean
rw [golden_mul_phiInv_coords]
```

This turns an abstract comparison of the measure after multiplication into an integer absolute-value inequality of the schematic form

$$
|b-a|+|a|<|a|+|b|.
$$

Thus the dependency flow is roughly

```text
goldenPhiInv + goldenMul
          ↓
golden_mul_phiInv_coords
          ↓
goldenUnitMeasure
          ↓
goldenUnit_descent
          ↓
goldenUnitFifthClass_of_unit
          ↓
goldenUnitClassesModFifth
```

So the theorem is not merely a convenience lemma: it is the computational interface translating golden-order multiplication into integer coordinates suitable for finite descent.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt` — the coordinate type for $a+b\varphi$.
- `goldenMul` — multiplication in the golden order with $\varphi^2=\varphi+1$ built into the coordinate formula.
- `goldenPhiInv` — `⟨-1,1⟩`, representing $\varphi-1$.
- extensionality for `GoldenInt` — used by `ext` to split structure equality into coordinate equalities.
- commutative-ring normalization — used by the final `ring` tactic.

The multiplication definition is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

Substituting `y = goldenPhiInv = ⟨-1,1⟩`, the first coordinate becomes

$$
a(-1)+b=b-a,
$$

while the second becomes

$$
a+b(-1)+b=a.
$$

Declarations 0349 `golden_phi_mul_inv` and 0350 `golden_inv_mul_phi` establish mathematically that this element is indeed an inverse of $\varphi$, but they are not directly referenced by the proof body here. The theorem computes from the coordinate definitions rather than deriving the coordinates from inverse laws.

## Proof flow

The proof is

```lean
by
  ext <;> simp [goldenMul, goldenPhiInv]
  all_goals ring
```

Its steps are:

1. `ext` reduces equality of two `GoldenInt` values to equality of their `fst` and `snd` coordinates.
2. `<;>` applies `simp [goldenMul, goldenPhiInv]` to every generated subgoal.
3. `simp` unfolds `goldenMul` and `goldenPhiInv`, reduces constructor projections, and simplifies basic arithmetic involving $0$, $1$, and $-1$.
4. `all_goals ring` normalizes and closes the remaining polynomial identities over the integers.

Conceptually Lean is proving

```text
fst:
  a * (-1) + b * 1 = b - a

snd:
  a * 1 + b * (-1) + b * 1 = a
```

## Lean-specific processing

### Structure equality via `ext`

Because `GoldenInt` is a coordinate structure, it is natural to write

```lean
ext
```

and reduce the goal to fieldwise equalities instead of manipulating constructor equality directly.

This is the same proof pattern as in 0352 and illustrates one of the main advantages of the explicit coordinate model.

### Division of labor between `simp` and `ring`

Here `simp` handles definition unfolding and elementary simplification. `ring` handles normalization of the remaining integer polynomial expressions.

In particular, the right-hand side contains

```lean
x.snd - x.fst
```

so a little more algebraic normalization is required than in the purely additive coordinate formula of 0352. `ring` is not reasoning about order or divisibility; it closes the goals as identities in a commutative ring.

### `all_goals ring`

Since `ext` creates more than one goal, `all_goals ring` applies the same ring-normalization tactic to every remaining coordinate goal.

This is a concise Lean-specific way to finish all subgoals without manually naming them.

## Redundancy and overlap

The present theorem is strongly symmetric with 0352 `golden_mul_phi_coords`.

Writing

$$
M_\varphi=
\begin{pmatrix}
0&1\\
1&1
\end{pmatrix},
\qquad
M_{\varphi^{-1}}=
\begin{pmatrix}
-1&1\\
1&0
\end{pmatrix},
$$

the two theorems say that these matrices act on the coordinate column vector $(a,b)^T$.

Moreover,

$$
M_\varphi M_{\varphi^{-1}}=I.
$$

Therefore one could abstract the pair as mutually inverse coordinate actions.

However, the current `goldenUnit_descent` proof works directly with concrete `natAbs` inequalities in each sign branch. The explicit coordinate formulas are therefore especially convenient. Introducing a matrix abstraction would likely require converting back to explicit coordinates later, so it is not obviously a local simplification.

## Optimization candidates

The current proof is already small. Possible refinements include:

1. The tactic script could potentially be compressed to `ext <;> simp [goldenMul, goldenPhiInv] <;> ring`.
2. Additional simp lemmas might reduce the residual goals before `ring`.
3. Marking the theorem `[simp]` could allow downstream uses such as `rw [golden_mul_phiInv_coords]` to become automatic.
4. Declarations 0352 and 0353 could be grouped into a small API for coordinate actions of the unit generators, with a separate theorem showing that the actions are inverse.

Candidate 3 changes the simplifier's normal form: `goldenMul x goldenPhiInv` would automatically expand to an explicit constructor. That may be too aggressive in proofs where the abstract multiplicative form should be preserved, so such an attribute should only be introduced after checking downstream behavior.

Candidate 1 is mostly stylistic; the current `all_goals ring` version makes the distinction between simplification and algebraic normalization quite clear.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the whole development.

The theorem itself directly needs mainly:

- the `ext` tactic for structure extensionality,
- `simp`,
- basic integer addition, subtraction, multiplication, and sign simplification,
- the `ring` normalization tactic,
- the previously defined project declarations `GoldenInt`, `goldenMul`, and `goldenPhiInv`.

It does not use `omega`, `nlinarith`, or `norm_num` directly.

Therefore a substantially smaller import set than all of `Mathlib` is likely sufficient. However, the **exact minimal import cannot be confirmed without a Lean build**, because it depends on the actual imports for `ring`, the module containing the golden-order definitions, and the project module boundary before generation.

No Lean build is performed here, so concrete minimal import names remain unverified.

## Comparator challenge suitability

**Suitable. Difficulty: beginner-to-intermediate.**

A challenge could present

```lean
example (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ?_
```

with the definitions of `goldenMul` and `goldenPhiInv` available. A compact expected solution is

```lean
ext <;> simp [goldenMul, goldenPhiInv]
all_goals ring
```

Useful evaluation points are whether the solver can:

- reduce structure equality with `ext`,
- recognize that `goldenPhiInv` must be unfolded,
- separate simplification from ring normalization,
- avoid unnecessary `omega` or `nlinarith`,
- recognize that direct coordinate computation is shorter than invoking abstract inverse properties.

Together with 0352, this makes a particularly clean two-part Comparator micro-challenge covering the coordinate actions of $\varphi$ and $\varphi^{-1}$.

## Next declaration to read

The next declaration is **0354 `goldenUnitMeasure`**, whose kind is **`def`**.

```lean
/-- Coordinate size used for the elementary unit descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

Mathematically it defines the $\ell^1$-type coordinate measure

$$
\mu(a,b)=|a|+|b|.
$$

Substituting the coordinate transformations from 0352 and 0353 into this measure lets the later `goldenUnit_descent` prove, in the appropriate sign branch, either

$$
\mu(x\varphi)<\mu(x)
$$

or

$$
\mu(x\varphi^{-1})<\mu(x).
$$

This is where the finite descent underlying the unit classification begins in earnest.
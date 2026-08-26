# 0167 — `goldenNorm_phi`

## Lean type

```lean
/-- The basis unit `φ` has norm `-1`. -/
@[simp] theorem goldenNorm_phi : goldenNorm goldenPhi = -1 := by
  norm_num [goldenNorm, goldenPhi]
```

This is a `theorem` stating that the generator `goldenPhi` of the golden integer order has norm `-1`. It is also marked `@[simp]` so that this basic value becomes part of the normalization API.

## Mathematical statement and meaning of the declaration

Declaration 0161 defines

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

and 0164 defines

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

Therefore

$$
N(\varphi)=0^2+0\cdot1-1^2=-1.
$$

In the usual quadratic-field interpretation, $\varphi=(1+\sqrt5)/2$ has conjugate $1-\varphi$, and

$$
\varphi(1-\varphi)=-1.
$$

The theorem records this norm value as an explicit Lean API fact.

## Role in the overall proof

Declaration 0165 `golden_phi_sq` exposes the defining relation

$$
\varphi^2=\varphi+1,
$$

and 0166 `goldenConj_phi` exposes

$$
\overline\varphi=1-\varphi.
$$

The present theorem adds the third basic arithmetic fact about the generator:

$$
N(\varphi)=-1.
$$

Norm `±1` is the key arithmetic criterion used later for units in the golden order, so this gives the numerical certificate that `goldenPhi` is a unit. Indeed, the later theorem `goldenUnit_phi` applies `goldenUnit_of_norm_eq_neg_one` and recomputes exactly the same norm value.

This unit property is then used when powers of `goldenPhi` appear as unit factors in fifth-power and unit-sector arguments.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0161 `goldenPhi`
- 0164 `goldenNorm`
- integer arithmetic and the `norm_num` tactic

Although 0165 `golden_phi_sq` and 0166 `goldenConj_phi` are mathematically adjacent, this proof does not depend on them. Lean evaluates the coordinate definition directly.

## Proof / construction flow

The proof is only

```lean
by
  norm_num [goldenNorm, goldenPhi]
```

After unfolding `goldenPhi` to `⟨0,1⟩` and `goldenNorm` to the quadratic form

$$
a^2+ab-b^2,
$$

the goal reduces to the closed integer computation

$$
0^2+0\cdot1-1^2=-1.
$$

`norm_num` then closes the arithmetic goal.

## Lean-specific processing

`norm_num` normalizes concrete numerical expressions. Here it is not performing abstract ring reasoning; it is evaluating a closed integer expression after unfolding two definitions.

The `@[simp]` attribute also turns

```lean
goldenNorm goldenPhi
```

into a direct simplification rule to

```lean
-1
```

so later unit and norm computations involving the generator do not need to unfold its coordinates repeatedly.

## Redundancy and duplication

The value `-1` is immediately computable from the definitions of `goldenNorm` and `goldenPhi`, so the theorem is formally derivable without introducing new mathematics. Nevertheless, the norm of the generator is a central quadratic-order fact and deserves a named `@[simp]` theorem.

There is a concrete downstream duplication: the later theorem

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

repeats the same norm computation instead of reusing `goldenNorm_phi`. That proof could plausibly be shortened to a direct reuse such as `simpa using goldenNorm_phi`, subject to the exact goal shape.

## Optimization candidates

Possible alternatives are:

1. keep the current `norm_num [goldenNorm, goldenPhi]` proof;
2. check by Lean build whether the statement is definitional enough for `rfl`;
3. compare with `decide` as a closed computation;
4. reuse this theorem in the later `goldenUnit_phi` proof and remove the duplicated norm calculation;
5. coordinate this API with a conjugate-product theorem such as `goldenPhi * goldenConj goldenPhi = -1`.

No Lean build is performed in this museum pass, so option 2 is explicitly unverified.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself mainly needs the upstream `GoldenInt`, `goldenNorm`, and `goldenPhi` definitions, integer arithmetic, and `norm_num`.

Therefore the theorem alone is unlikely to require all of Mathlib. The real minimal import set is governed by the complete `GoldenOrder` module, which also uses algebraic typeclasses, `ring`, and `Zsqrtd`. Since no build is run here, an exact reduced import set remains unverified.

## Comparator challenge suitability

Yes. Useful proof variants include:

- `norm_num [goldenNorm, goldenPhi]`
- `rfl`, if it actually works
- `decide`
- a `ring_nf` / `norm_num` combination

The comparison can measure proof-term simplicity, robustness under definition changes, error clarity, import dependencies, and transparency of the calculation.

At the API level, it is also useful to compare a version in which downstream `goldenUnit_phi` explicitly reuses this theorem against the current version that recomputes the norm from definitions.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following this theorem in the Lean source is

```lean
/-- Conjugation fixes the embedded rational integers. -/
@[simp] theorem goldenConj_ofInt (a : ℤ) :
    goldenConj (goldenOfInt a) = goldenOfInt a := by
  ...
```

Therefore the natural next museum entry is **0168 `goldenConj_ofInt`**. After checking conjugation on the generator `φ`, the development now records that the embedded integer axis is fixed by conjugation.

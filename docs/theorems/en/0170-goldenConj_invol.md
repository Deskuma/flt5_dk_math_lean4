# 0170 — `goldenConj_invol`

## Lean type

```lean
/-- Conjugation is an involution. -/
theorem goldenConj_invol (x : GoldenInt) :
    goldenConj (goldenConj x) = x := by
  ext <;> simp [goldenConj]
```

This is a `theorem` stating that applying `goldenConj` twice to any golden integer returns the original element.

## Mathematical statement and meaning of the declaration

Declaration 0163 defines conjugation by

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

Reading an element of `GoldenInt` as

$$
x=a+b\varphi,
$$

conjugation acts on the generator by

$$
\varphi\mapsto1-\varphi,
$$

which in coordinates is

$$
(a,b)\mapsto(a+b,-b).
$$

Applying the same transformation again gives

$$
(a+b,-b)\mapsto((a+b)+(-b),-(-b))=(a,b),
$$

hence

$$
\overline{\overline{x}}=x.
$$

The theorem therefore establishes that the quadratic conjugation is an involution, i.e. an order-two symmetry on all of `GoldenInt`.

## Role in the overall proof

Declaration 0166 `goldenConj_phi` recorded the action of conjugation on the generator $\varphi$, while 0168 `goldenConj_ofInt` showed that conjugation fixes the embedded integer axis. The present theorem upgrades those local facts to a global statement: conjugation is genuinely self-inverse on every golden integer.

This is a foundational property for treating conjugation as more than an explicit coordinate function. Immediately afterward, `goldenConj_mul` proves that conjugation preserves multiplication. Taken together, 0170 and 0171 provide major pieces of the structure that could later be bundled as a ring automorphism.

The theorem is also part of the mathematical background for later facts such as invariance of the norm under conjugation and multiplication by a conjugate. In the nearby source inspected here, however, those later results are proved directly by coordinate calculations rather than by explicitly rewriting with `goldenConj_invol`.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0163 `goldenConj`
- `GoldenInt.ext`
- the `fst` and `snd` coordinates of `GoldenInt`
- elementary simplifier lemmas for integer addition and negation

Declarations 0166 `goldenConj_phi` and 0168 `goldenConj_ofInt` are mathematically adjacent examples, but they are not direct dependencies of the Lean proof.

Conceptually, the dependency chain is

$$
\texttt{goldenConj},\ \texttt{GoldenInt.ext}
\longrightarrow
\texttt{goldenConj_invol}.
$$

## Proof / construction flow

The proof is only

```lean
by
  ext <;> simp [goldenConj]
```

The `ext` tactic reduces equality of `GoldenInt` structures to equality of their first and second integer coordinates. Unfolding `goldenConj` twice then produces the coordinate identities

$$
(a+b)+(-b)=a
$$

and

$$
-(-b)=b.
$$

Thus the proof flow is

```text
goldenConj (goldenConj x) = x
→ split the GoldenInt equality into fst / snd goals
→ unfold goldenConj twice
→ simplify integer addition and double negation
→ both coordinates agree
```

## Lean-specific processing

`ext` uses `GoldenInt.ext` to reduce structure equality to coordinate equality, avoiding a manual `cases x` proof.

The `<;>` combinator then applies the same `simp [goldenConj]` command to every generated goal. The simplifier unfolds conjugation and normalizes expressions such as

```lean
x.fst + x.snd + -x.snd
```

and

```lean
-(-x.snd).
```

The theorem itself is not marked `@[simp]`. If the intended API is for all occurrences of `goldenConj (goldenConj x)` to normalize automatically to `x`, adding `@[simp]` is a possible design option. Such an addition should still be evaluated in the context of the future bundled conjugation API and the global simp set.

## Redundancy and duplication

The mathematical content follows immediately from the coordinate definition of `goldenConj`, so the proof is intentionally tiny. Nevertheless, having the result as a named theorem is valuable.

Declarations 0166 and 0168 record the behavior of conjugation on the generator and on the integer axis, whereas this theorem records the global involution law. These are therefore better viewed as local and global API layers rather than accidental duplication.

A more structured design could bundle conjugation as something like `GoldenInt ≃+* GoldenInt`. In that setting, additive and multiplicative preservation, bijectivity, and inverse behavior would be grouped in a single object, and an involution theorem could potentially be obtained from generic equivalence lemmas rather than reproved at the coordinate level.

## Optimization candidates

Possible alternatives include:

1. retain the current `ext <;> simp [goldenConj]` proof;
2. mark the theorem `@[simp]` so double conjugation normalizes automatically;
3. compare against a lower-level proof using `cases x` and direct simplification;
4. bundle `goldenConj` first as an additive or multiplicative homomorphism;
5. ultimately expose conjugation as a ring equivalence `GoldenInt ≃+* GoldenInt` and obtain involution through the equivalence API.

The current proof is already short and preserves the transparency of the coordinate implementation, so local proof-term optimization has little value. The more significant optimization opportunity is structural: if many downstream results accumulate, a bundled automorphism API may reduce repetition.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself primarily needs the upstream definitions `GoldenInt`, `GoldenInt.ext`, and `goldenConj`, together with elementary simplifier infrastructure for integer addition and negation.

Thus importing all of Mathlib is likely excessive for this theorem in isolation. The full `GoldenOrder` module, however, also uses `CommRing`, `Zsqrtd`, `ring`, `omega`, `norm_num`, and related infrastructure, so the true minimal import set has to be tested at module scope. No exact reduced import set is claimed here because this museum pass does not run a Lean build.

## Comparator challenge suitability

Yes. This theorem is especially suitable for comparing explicit coordinate proofs with a bundled automorphism design.

Useful variants include:

- the current `ext <;> simp [goldenConj]` proof;
- a direct `cases x` coordinate proof;
- the same theorem marked `@[simp]`;
- conjugation bundled as an additive equivalence;
- conjugation bundled as a ring equivalence.

Comparison criteria include proof-term size, simp normal forms, downstream reuse, compatibility with standard algebra APIs, and generalizability to other quadratic orders.

In particular, it provides a clean benchmark for deciding at what point an explicit coordinate development should be lifted into an abstract automorphism API without losing transparency.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following this theorem in the Lean source is

```lean
/-- Conjugation respects multiplication. -/
theorem goldenConj_mul (x y : GoldenInt) :
    goldenConj (goldenMul x y) =
      goldenMul (goldenConj x) (goldenConj y) := by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

Therefore the next museum entry is **0171 `goldenConj_mul`**. After 0170 establishes that conjugation is self-inverse, the next step proves the multiplicative law

$$
\overline{xy}=\overline{x}\,\overline{y},
$$

which is the next major condition for understanding conjugation as a ring automorphism.
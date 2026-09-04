# 0168 — `goldenConj_ofInt`

## Lean type

```lean
/-- Conjugation fixes the embedded rational integers. -/
@[simp] theorem goldenConj_ofInt (a : ℤ) :
    goldenConj (goldenOfInt a) = goldenOfInt a := by
  ext <;> simp [goldenConj, goldenOfInt]
```

This is a `theorem` stating that an integer `a : ℤ`, after embedding into the golden integer order as `goldenOfInt a`, is fixed by the conjugation `goldenConj`. The theorem is marked `@[simp]` so this fixed-point behavior is available to the simplifier.

## Mathematical statement and meaning of the declaration

Declaration 0162 defines the integer embedding by

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

and 0163 defines conjugation by

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

Reading a golden integer as $a+b\varphi$, conjugation corresponds to

$$
\overline{a+b\varphi}=(a+b)-b\varphi.
$$

For an embedded integer the second coordinate is $b=0$, so

$$
\overline{a}=a.
$$

In coordinates,

$$
(a,0)\longmapsto(a+0,-0)=(a,0).
$$

Thus the theorem verifies, inside the explicit coordinate model, that the nontrivial quadratic conjugation fixes the embedded base ring `ℤ` pointwise.

## Role in the overall proof

Declaration 0166 `goldenConj_phi` showed that the generator moves by

$$
\overline{\varphi}=1-\varphi.
$$

The present theorem gives the complementary fact that the integer axis is fixed. Together they describe conjugation on the two basic directions of `GoldenInt`:

- the integer component $a$ is fixed;
- the $\varphi$ component transforms nontrivially.

This API sits at the beginning of the conjugation-and-norm layer that continues with `goldenNorm_ofInt`, `goldenConj_invol`, `goldenConj_mul`, `goldenNorm_conj`, and `golden_mul_conj`. The `@[simp]` attribute is also useful whenever later expressions contain conjugation of an embedded integer, because such terms normalize automatically.

In the source inspected for this entry, no later explicit `rw [goldenConj_ofInt]` use was identified. It is therefore safest to regard the theorem primarily as part of the simp API and the mathematical interface for conjugation.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0162 `goldenOfInt`
- 0163 `goldenConj`
- `GoldenInt.ext`
- basic simplification facts for integer addition and negation

Although 0166 `goldenConj_phi` and 0167 `goldenNorm_phi` are mathematically adjacent, the Lean proof of this theorem does not use them. It closes directly from the coordinate definitions.

## Proof / construction flow

The proof is

```lean
by
  ext <;> simp [goldenConj, goldenOfInt]
```

The `ext` tactic reduces equality of `GoldenInt` structures to equality of their first and second coordinates. After unfolding `goldenConj` and `goldenOfInt`, the two goals are conceptually

$$
a+0=a
$$

and

$$
-0=0.
$$

Both are discharged by `simp`.

Thus the proof flow is

```text
GoldenInt equality
→ coordinate equality by extensionality
→ unfold the definitions
→ elementary ℤ simplification
```

and remains completely transparent at the coordinate level.

## Lean-specific processing

The `ext` tactic uses the upstream declaration

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  ...
```

to turn structure equality into two coordinate goals.

The `<;>` combinator applies `simp [goldenConj, goldenOfInt]` to every goal produced by `ext`, avoiding separate scripts for the two coordinates.

The `@[simp]` attribute then provides the rewrite

```lean
goldenConj (goldenOfInt a)
```

to

```lean
goldenOfInt a
```

as a standard normalization rule. This keeps expressions involving the fixed integer subring in a natural normal form.

## Redundancy and duplication

The theorem is directly derivable from the definitions of `goldenConj` and `goldenOfInt`, so it introduces no new mathematical information. Nevertheless, “conjugation fixes the embedded integers” is a fundamental quadratic-order API fact and is worth exposing as a named `@[simp]` theorem.

The proof explicitly uses `ext` to split the structure equality into two coordinate equalities. It is plausible that `simp [goldenConj, goldenOfInt]` alone could close the entire structure equality, but this was not verified because this museum pass does not run a Lean build.

There is also API-level overlap between `goldenOfInt` and the standard cast `(a : GoldenInt)`, because the upstream `intCast` uses the same coordinate rule `⟨a,0⟩`. An explicit bridge between the raw coordinate API and the standard cast API could make this duplication more deliberate and easier to use.

## Optimization candidates

Possible alternatives are:

1. retain the current `ext <;> simp [goldenConj, goldenOfInt]` proof;
2. check by Lean build whether `simpa [goldenConj, goldenOfInt]` closes the theorem directly;
3. check whether the statement reduces far enough for `rfl`;
4. add a bridge theorem `goldenOfInt a = (a : GoldenInt)` and connect the raw embedding to the standard cast API;
5. eventually bundle `goldenConj` as a ring endomorphism or automorphism and derive the result from a generic `map_intCast`-style law.

Options 2 and 3 are explicitly unverified in this pass.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself mainly depends on the upstream definitions `GoldenInt`, `goldenOfInt`, and `goldenConj`, together with extensionality, `simp`, and elementary integer operations.

Therefore the theorem in isolation is unlikely to require all of Mathlib. However, the complete `GoldenOrder` module also uses ring structures, `Zsqrtd`, `ring`, `omega`, `norm_num`, and other infrastructure, so the real minimal import set must be tested at module scope. Since no Lean build is run in this museum pass, an exact reduced import set remains unverified.

## Comparator challenge suitability

Yes. The theorem is small enough to expose differences in proof style and abstraction clearly.

Useful variants include:

- the current `ext <;> simp` proof;
- a single `simpa`, if it works;
- `rfl`, if definitional reduction is sufficient;
- a bundled ring-homomorphism / automorphism implementation of conjugation, deriving the statement from a generic integer-cast preservation theorem.

Comparison criteria include proof-term simplicity, robustness under definition changes, simp normal forms, import requirements, generalizability, and downstream reuse. In particular, this makes a clean comparison between explicit coordinate transparency and reuse of abstract algebraic interfaces.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following this theorem in the Lean source is

```lean
/-- The norm of an embedded integer is its square. -/
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

Therefore the next museum entry is **0169 `goldenNorm_ofInt`**. After showing that conjugation fixes the embedded integer axis, the development next records that the norm of the same embedded integer is the square $a^2$.
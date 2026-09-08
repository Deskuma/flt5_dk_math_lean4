# 0354 — `goldenUnitMeasure`

## Declaration kind

This declaration is a **`def`**.

```lean
/-- Coordinate size used for the elementary unit descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

It is not a theorem. It defines a natural-number-valued size attached to the coordinates of a golden integer.

## Lean type

```lean
goldenUnitMeasure (x : GoldenInt) : ℕ
```

The input is a golden integer `x : GoldenInt`, and the output is a natural number.

Writing

$$
x=a+b\varphi
$$

with `x.fst = a` and `x.snd = b`, the definition is

$$
\mu(x)=|a|+|b|.
$$

Lean uses `Int.natAbs`, whose codomain is `ℕ`, so the measure is natural-valued from the outset.

## Mathematical meaning

`goldenUnitMeasure` is the $\ell^1$-type coordinate size

$$
\mu(a,b)=|a|+|b|
$$

for the golden integer $a+b\varphi$.

This is not the golden-order norm

$$
N(a+b\varphi)=a^2+ab-b^2.
$$

For units, the algebraic norm is fixed at $\pm1$, so it cannot itself serve as a strictly decreasing quantity in a unit descent. The coordinate absolute-value sum can change when the element is multiplied by $\varphi$ or $\varphi^{-1}$, and in the appropriate sign regions it can be made strictly smaller.

The two immediately preceding declarations give the coordinate actions

$$
(a,b)\mapsto(b,a+b)
$$

and

$$
(a,b)\mapsto(b-a,a)
$$

for multiplication by $\varphi$ and $\varphi^{-1}$. The present definition compresses those two coordinates into a single natural-number measure.

## Role in the full proof

The central strategy of `GoldenUnitClassification` is an elementary finite descent on golden-order units: multiply a unit by $\varphi$ or $\varphi^{-1}$ so that a coordinate measure strictly decreases, continue until a base unit is reached, and then reverse the descent to classify all units.

The role of this definition is therefore

```text
GoldenInt coordinates
      ↓
goldenUnitMeasure : GoldenInt → ℕ
      ↓
strict decrease in ℕ
      ↓
well-founded / strong induction
      ↓
base unit cases
      ↓
classification as signed powers of φ
```

The next theorem, `goldenUnitMeasure_pos`, proves that this measure is positive on units. Later descent lemmas combine the coordinate formulas from 0352 and 0353 with this definition to show that one of the two generator moves decreases the measure.

Thus this declaration is the bridge that turns an algebraic unit problem into a well-founded descent over natural numbers, which Lean can handle directly.

## Direct dependencies

The definition itself has very few direct dependencies:

- `GoldenInt` — the integer-coordinate type representing $a+b\varphi$.
- `GoldenInt.fst` — the first integer coordinate $a$.
- `GoldenInt.snd` — the second integer coordinate $b$.
- `Int.natAbs` — absolute value of an integer as a natural number.
- natural-number addition — used to add the two coordinate absolute values.

0352 `golden_mul_phi_coords` and 0353 `golden_mul_phiInv_coords` are not syntactic dependencies of the definition, but they are the immediate mathematical motivation for choosing this measure and are used downstream together with it.

Likewise, `GoldenUnit` and `goldenNorm` do not appear in the definition body. They enter in the next positivity theorem and in the later descent arguments.

## Construction flow

The definition body is a single expression:

```lean
x.fst.natAbs + x.snd.natAbs
```

Lean performs only the following operations:

1. project `x.fst : ℤ`;
2. convert it to `x.fst.natAbs : ℕ`;
3. project `x.snd : ℤ`;
4. convert it to `x.snd.natAbs : ℕ`;
5. add the two natural numbers.

There are no tactics, case splits, coercion tactics, or proof terms involved.

This simplicity is deliberate. Downstream measure comparisons are reduced to inequalities involving `natAbs`, so the measure itself introduces no unnecessary algebraic structure.

## Lean-specific processing

### Why `Int.natAbs` is used

On paper one simply writes $|a|+|b|$, but in Lean the codomain of the absolute value matters.

Using

```lean
Int.natAbs : ℤ → ℕ
```

makes

```lean
goldenUnitMeasure : GoldenInt → ℕ
```

immediate. This lets later proofs use natural-number well-foundedness and tools such as `Nat.strong_induction_on` without repeatedly proving nonnegativity and converting an integer-valued measure into a natural number.

### Field projections

`x.fst` and `x.snd` are the coordinate projections of the concrete `GoldenInt` model. The definition therefore works directly in coordinates rather than through a more abstract ring representation.

### Definitional unfolding

Because this is a `def`, later proofs can unfold it explicitly with

```lean
simp [goldenUnitMeasure]
```

or, as the next theorem does,

```lean
simp only [goldenUnitMeasure]
```

when they need to expose the sum of coordinate absolute values.

## Redundancy and duplication

There is essentially no redundancy in the declaration itself.

One possible source of duplication would be a project-wide generic $\ell^1$ measure for integer coordinate pairs. In the checked `GoldenUnitClassification` code, however, this definition is local and purpose-built for the unit descent.

It would also be possible to introduce a general height/size API on `GoldenInt` and move this definition there. The current source does not establish that $|a|+|b|$ is intended as a canonical height for all golden integers, only that it is the measure chosen for this descent. The local name is therefore appropriate to the verified use.

## Optimization candidates

The current definition is already near-minimal. Possible refinements are mostly library-design choices rather than proof shortening:

1. add a dedicated unfolding/simplification lemma if the same expansion becomes frequent downstream;
2. promote the measure into a more general `GoldenInt` API if later developments reuse exactly the same notion extensively;
3. if the coordinate actions are later abstracted as matrices, package general lemmas describing how the $\ell^1$ measure behaves under those transformations.

The first point does not imply that the definition itself should always be a simp rule: preserving the abstract name `goldenUnitMeasure` can make later statements substantially clearer.

The second and third points are structural refactorings, not local optimizations required by the present proof.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the whole development.

This declaration alone externally needs essentially only

- `ℤ` and `ℕ`,
- `Int.natAbs`,
- natural-number addition.

It does not use tactics such as `ring`, `omega`, `nlinarith`, or `norm_num`.

However, the real `GoldenUnitClassification` module must also import the preceding module that defines `GoldenInt` and the unit infrastructure. Therefore **the minimum Mathlib imports for this isolated declaration and the minimum imports for the real module are not the same question**.

No Lean build is performed in this task, so the exact smallest Mathlib module list is not confirmed. What can be stated safely is that the standalone-wide `import Mathlib` is much broader than this declaration itself requires.

## Comparator challenge suitability

**Yes. Difficulty: beginner, and better as a definition-design challenge than as a proof challenge.**

For example:

```lean
/-- A natural-valued coordinate measure for descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  ?_
```

with the conditions that

- `GoldenInt` has two integer coordinates;
- the measure should ignore coordinate signs;
- its codomain should be `ℕ`;
- it will be used for strict descent / strong induction.

The intended compact answer is

```lean
x.fst.natAbs + x.snd.natAbs
```

A proof-style Comparator challenge could instead expose the definition and ask for

```lean
example (x : GoldenInt) :
    goldenUnitMeasure x = x.fst.natAbs + x.snd.natAbs := by
  ?_
```

but this is essentially `rfl` and has little discriminating power. The interesting part is the design decision to choose a natural-valued `natAbs` measure suitable for well-founded descent.

## Next declaration to read

The next declaration is **0355 `goldenUnitMeasure_pos`**, and its kind is **`theorem`**.

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

The definition alone allows the zero element to satisfy

$$
\mu(0,0)=0.
$$

Declaration 0355 adds the hypothesis `GoldenUnit x` and uses the fact that a unit has golden norm $\pm1$ to exclude the zero element, obtaining

$$
0<\mu(x).
$$

This removes the anomalous possibility of a measure-zero unit and prepares the natural-number descent for its genuine base cases.

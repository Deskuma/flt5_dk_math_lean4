# 0175 — `goldenNorm_conj`

## Lean type

```lean
/-- Conjugation preserves the golden norm. -/
theorem goldenNorm_conj (x : GoldenInt) :
    goldenNorm (goldenConj x) = goldenNorm x := by
  simp [goldenNorm, goldenConj]
  ring
```

This is a `theorem` stating that conjugation `goldenConj` preserves the integer-valued norm `goldenNorm` on `GoldenInt`.

## Mathematical statement and meaning of the declaration

Write an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

Conjugation is determined by

$$
\overline{\varphi}=1-\varphi,
$$

and 0163 `goldenConj` implements the coordinate transformation

$$
(a,b)\longmapsto(a+b,-b).
$$

The norm from 0164 is

$$
N(a+b\varphi)=a^2+ab-b^2.
$$

The theorem proves

$$
N(\overline{x})=N(x).
$$

Indeed, after substituting the conjugated coordinates,

$$
N((a+b)-b\varphi)=(a+b)^2-(a+b)b-b^2=a^2+ab-b^2.
$$

Thus this is the explicit-coordinate form of the standard fact that the norm in a quadratic extension is invariant under the nontrivial Galois conjugation.

## Role in the overall proof

0174 `goldenNorm_mul` established the multiplicativity law

$$
N(xy)=N(x)N(y).
$$

The present theorem supplies the complementary conjugation law

$$
N(\overline{x})=N(x).
$$

Together, these results make `goldenNorm` compatible with both multiplication and the quadratic symmetry of the golden order.

Downstream, conjugation, multiplication, and norm are combined in results relating an element to its conjugate, and later in arguments about units, divisibility, and Euclidean-domain structure. This theorem therefore serves as the basic norm API on the conjugation side.

Conceptually,

```text
goldenConj
    │
    ▼
goldenNorm_conj
    │
    ├─ conjugate pair has the same norm
    ├─ unit / divisibility arguments
    └─ quadratic-order symmetry
```

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0163 `goldenConj`
- 0164 `goldenNorm`
- `simp`
- `ring`

0170 `goldenConj_invol` and 0171 `goldenConj_mul` are mathematically close, but are not used directly by this proof. Likewise, 0174 `goldenNorm_mul` is the immediately preceding major norm theorem, yet the current proof closes independently as a coordinate polynomial identity.

## Proof / construction flow

The proof has two steps:

```lean
simp [goldenNorm, goldenConj]
ring
```

First, `goldenConj x` unfolds to the coordinates `⟨x.fst + x.snd, -x.snd⟩`, and those coordinates are substituted into the quadratic expression defining `goldenNorm`.

Writing `x.fst=a` and `x.snd=b`, the left-hand side becomes

$$
(a+b)^2+(a+b)(-b)-(-b)^2.
$$

`simp` handles projections, signs, and definitional unfolding; `ring` then normalizes the remaining identity in `ℤ` and closes the goal.

## Lean-specific processing

Because both `goldenConj` and `goldenNorm` are explicit coordinate definitions, Lean does not need an abstract ring automorphism or bundled norm map. After unfolding, the goal is ordinary commutative-ring polynomial arithmetic.

This makes the proof short and easy to audit at the representation level. The trade-off is that the structural reason for the theorem—norm invariance under quadratic conjugation—is not represented as reusable typeclass or morphism structure.

## Redundancy and duplication

Conjugation laws are currently distributed across several standalone theorems, including:

- `goldenConj_invol`
- `goldenConj_mul`
- later additive compatibility results
- `goldenNorm_conj`

These could potentially be organized more systematically by bundling `goldenConj` as a `RingEquiv GoldenInt GoldenInt`.

Likewise, the present theorem is proved by direct coordinate expansion. If norm were instead structured through the product of an element with its conjugate, conjugation invariance might follow from involutivity and commutativity rather than from a separate polynomial calculation.

## Optimization candidates

1. Keep the current `simp [goldenNorm, goldenConj]; ring` proof.
2. Bundle `goldenConj` as a `RingEquiv` and derive conjugation laws through a common API.
3. Structure `goldenNorm` through the product `x * goldenConj x`, deriving invariance from involutivity.
4. Reuse generic conjugation/norm infrastructure from `AdjoinRoot (X^2-X-1)` or a quadratic algebra.
5. Prove invariance first for the existing binary quadratic form `GoldenNorm`, then reuse it for the structure-level norm.

The local proof is already minimal, so the main optimization question is abstraction and API consolidation rather than line count.

## Required Mathlib imports and import optimization

This theorem directly needs integer arithmetic, simplification, ring normalization, and the upstream definitions of `GoldenInt`, `goldenConj`, and `goldenNorm`.

The standalone artifact uses `import Mathlib`, which is likely broader than necessary for this theorem alone. However, the full `GoldenOrder` module also uses `Zsqrtd`, `omega`, `norm_num`, `interval_cases`, and substantial algebraic typeclass infrastructure. Therefore the exact minimal import set should be validated at module level with Lean. No Lean build is performed in this museum pass, so no precise minimal list is claimed.

## Comparator challenge suitability

Yes.

Useful implementations to compare are:

- explicit coordinate expansion followed by `ring`;
- a structural proof using a bundled `RingEquiv` conjugation;
- a norm defined through element-times-conjugate;
- generic `AdjoinRoot` / quadratic-algebra norm and conjugation theorems.

Comparison criteria include proof size, definitional transparency, reuse, reduction of duplicated conjugation laws, and ergonomics for later unit, divisibility, and Euclidean-domain arguments.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` generated source embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch, together with the source ordering recorded by the preceding 0174 entry.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

On the next pass, the declaration immediately after `goldenNorm_conj` should be re-read from the repository before selection. The nearby source continues by relating an element and its conjugate to the norm, so after establishing conjugation invariance the development naturally moves toward an identity of the form

$$
x\overline{x}=N(x).
$$

The repository remains the source of truth for the exact next declaration and numbering.
# 0164 — `goldenNorm`

## Lean type

```lean
/-- The integral norm `N(a+b*φ)=a^2+a*b-b^2`. -/
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

This is a `def`, not a theorem. It defines the integral norm of a golden integer `x = a + bφ` as an explicit quadratic form.

## Mathematical statement and meaning of the declaration

Read an element of `GoldenInt` as

$$
x=a+b\varphi
$$

with

$$
\varphi^2=\varphi+1.
$$

Declaration 0163 `goldenConj` represents

$$
\overline{x}=(a+b)-b\varphi.
$$

Their product is therefore

$$
x\overline{x}=a^2+ab-b^2,
$$

so `goldenNorm` directly records the integer value

$$
N(a+b\varphi)=a^2+ab-b^2.
$$

The Lean definition

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

is exactly this quadratic form in the two coordinates.

## Role in the overall proof

`goldenNorm` is one of the central numerical invariants used after `GoldenOrder`. It compresses the conjugation symmetry introduced in 0163 into an integer and transfers multiplicative information about golden integers into ordinary integer arithmetic.

Downstream development uses this norm for, among other things,

- invariance under conjugation;
- multiplicativity of the norm;
- the identity relating `x * goldenConj x` to the embedded integer `goldenNorm x`;
- unit criteria through norm `±1`;
- size estimates for Euclidean remainders;
- the measure needed to build a Euclidean-domain structure on `GoldenInt`.

Thus this definition is not merely a convenience function. It is the numerical interface through which multiplication, invertibility, and Euclidean descent become integer statements.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`;
- `GoldenInt.fst`;
- `GoldenInt.snd`;
- integer addition, multiplication, and subtraction;
- the standard power operation `^ 2` on integers.

No theorem is required to construct the value; it is defined directly from coordinates.

Semantically, the most important preceding declaration is 0163 `goldenConj`, because the quadratic form is naturally understood as the product of an element with its conjugate.

## Proof / construction flow

There is no proof script. The construction is one line:

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

Mathematically, for `x = a+bφ`, one expands

$$
(a+b\varphi)((a+b)-b\varphi)
$$

and uses `φ² = φ + 1`. The `φ` coefficient cancels and leaves

$$
a^2+ab-b^2.
$$

The development chooses to make that resulting integer formula the definition itself. Later theorems then verify its compatibility with conjugation and multiplication.

## Lean-specific processing

The codomain of `goldenNorm` is `ℤ`, not `GoldenInt`. Therefore later statements that place the norm back inside the golden ring must use `goldenOfInt` or a standard integer cast.

The exponent `^ 2` here is the ordinary integer power operation; it is unrelated to the raw `GoldenInt` recursion `goldenPow`. Since the whole expression is an integer polynomial, downstream identities are naturally suited to tactics such as `ring` and `nlinarith`.

The norm is introduced as a raw function rather than immediately as a multiplicative homomorphism. Its multiplicativity is established separately in later theorems, preserving the explicit-coordinate style of the file.

## Redundancy and duplication

The definition itself is essentially minimal.

Abstractly, once conjugation exists one could instead define a norm from

$$
N(x)=x\overline{x}
$$

and then prove that the result lies in the integer subring. The present development takes the opposite direction: it defines the integer quadratic form first, then proves that it coincides with the conjugate product.

This is useful duplication rather than accidental repetition. Keeping the norm explicitly integer-valued makes unit tests and Euclidean-size estimates much more direct.

## Optimization candidates

1. Keep the present explicit quadratic form.
2. Define norm through conjugate multiplication and extract its integer value afterward.
3. Package multiplicativity into a suitable homomorphism structure rather than keeping it only as separate theorems.
4. Separate `|goldenNorm x|` as a dedicated Euclidean-measure API.
5. Generalize trace and norm to a reusable quadratic-order abstraction and obtain the golden case by specialization.
6. Connect the implementation to existing `AdjoinRoot` or quadratic-algebra norm infrastructure.

For the FLT5 audit goal, the present formula has a major advantage: the invariant is visible immediately as an integer polynomial. Optimization should therefore be evaluated by downstream reuse rather than local line count.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. In isolation, `goldenNorm` needs only `GoldenInt` and basic integer ring operations and powers; it invokes no advanced theorem directly.

The downstream norm theory uses ring normalization, numerical tactics, absolute-value estimates, and Euclidean-domain infrastructure. Because no Lean build is performed in this museum pass, the exact minimal import set is not verified; import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful comparison families are:

- the present coordinate quadratic form `a^2 + a*b - b^2`;
- a norm defined from conjugate multiplication;
- a generic quadratic-order norm;
- an `AdjoinRoot` / quadratic-algebra norm.

Useful metrics include proof size for multiplicativity, compatibility with conjugation, proof burden for the Euclidean estimate, simp normal forms, generalizability, import dependencies, and downstream FLT5 code volume.

The direct integer-valued representation is especially interesting because it may substantially simplify Euclidean-domain arguments.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, 0163 `goldenConj` is followed by this `goldenNorm` definition.

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page corresponding to this declaration was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is `golden_phi_sq`:

```lean
@[simp] theorem golden_phi_sq :
    goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne := by
  rfl
```

After introducing the numerical invariant `goldenNorm`, the development next exposes the defining golden-ratio identity

$$
\varphi^2=\varphi+1,
$$

as a Lean theorem, providing a basic rewrite fact for the conjugation and norm arithmetic that follows.
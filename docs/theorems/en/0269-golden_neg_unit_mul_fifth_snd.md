# 0269 — `golden_neg_unit_mul_fifth_snd`

## Declaration kind

This is a `theorem`.

## Lean type

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
  rw [neg_mul]
  rfl
```

As a type, it states that for arbitrary `epsilon gamma : GoldenInt`, negating the left factor `epsilon` negates exactly the second coordinate of its product with `gamma^5`.

## Mathematical statement

Treat `GoldenInt` as the coordinate model of the golden integers and write

$$
\epsilon=a+b\varphi,\qquad \gamma^5=A+B\varphi.
$$

Using $\varphi^2=\varphi+1$, the second coordinate of the product is

$$
\operatorname{snd}(\epsilon\gamma^5)=bA+(a+b)B.
$$

Replacing `epsilon` by `-epsilon=-a-b\varphi` gives

$$
\operatorname{snd}((-\epsilon)\gamma^5)
=(-b)A+(-a-b)B
=-\bigl(bA+(a+b)B\bigr).
$$

Hence

$$
\operatorname{snd}((-\epsilon)\gamma^5)
=-\operatorname{snd}(\epsilon\gamma^5).
$$

The theorem proves this sign rule not by expanding coordinates, but by using the general ring identity $(-x)y=-(xy)$.

## Role in the full proof

Theorems 0264–0268 computed the second coordinate obtained by multiplying the positive representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

by a fifth power. The resulting table is

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B.
$$

Actual unit-class representatives may also carry a sign $\pm$. There is no need to duplicate the five coordinate computations for the negative representatives. This theorem transfers every positive-sector formula to its negative counterpart by a single sign change.

Thus 0269 is the bridge that prevents the sector arithmetic from doubling in size. Instead of storing ten separate polynomial formulas for positive and negative representatives, the proof pushes the minus sign back into the ring structure and reuses the positive-sector calculations.

Immediately after this theorem, `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` moves from representative-level coordinate arithmetic to the packet's five-adic second-coordinate information. In this sense 0269 is the small normalization lemma that closes the sign-handling stage just before packet-level divisibility enters.

## Direct dependencies

The proof directly relies on the following definitions and lemmas.

- `GoldenInt`
  - The integer-coordinate model of elements $a+b\varphi$.
  - It is the type of `epsilon` and `gamma` here.
- `goldenMul`
  - Multiplication in the explicit golden-order API.
  - It is definitionally aligned with the ring multiplication `(*)` through `golden_mul_eq`.
- `goldenPow`
  - Natural powers in the explicit golden-order API.
  - It is definitionally aligned with `(^)` through `golden_pow_eq`.
- `neg_mul`
  - The standard Mathlib ring lemma expressing $(-a)b=-(ab)$.
- The `Neg`, `Mul`, and power/ring instances for `GoldenInt`
  - These are what make the target after `change` an ordinary ring expression.

The repository contains the bridge lemmas

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) : goldenMul x y = x * y := rfl
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) : goldenPow x n = x ^ n := rfl
```

showing that the explicit API and typeclass-based ring operations agree definitionally. The `change` step in this theorem exploits that alignment.

## Proof flow

The proof first executes

```lean
change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
```

The original goal is written with `goldenMul` and `goldenPow`. Because these are definitionally the same as ring multiplication and exponentiation, `change` moves the goal to ordinary ring notation without expanding any coordinates.

Next,

```lean
rw [neg_mul]
```

uses

$$
(-\epsilon)\gamma^5=-(\epsilon\gamma^5).
$$

After this rewrite, the left product itself is under a single outer negation.

Finally,

```lean
rfl
```

closes the goal. Negation on `GoldenInt` is coordinatewise, so the second projection of a negated golden integer reduces definitionally to the negation of its original second projection.

## Lean-specific processing

Mathematically, the theorem uses only two facts: $(-x)y=-(xy)$ and the fact that second-coordinate projection commutes with coordinatewise negation.

The notable Lean move is that it does not unfold `goldenMul` into coordinate arithmetic. Instead, `change` switches from the explicit golden-order API to the already established ring instance. This avoids the `ring`-based computation used in 0264–0268.

The final `rfl` is also significant. No dedicated projection-negation lemma is required because the `GoldenInt` negation instance and `.snd` projection are definitionally compatible.

This makes the theorem a compact example of switching between an explicit structural API and an abstract algebraic API inside Lean.

## Redundancy and duplication

The theorem itself is extremely short and contains no obvious redundancy. Its purpose is, in fact, to remove duplication that would otherwise arise from re-proving all five sector formulas for negative units.

A proof such as

```lean
simp [golden_mul_eq, golden_pow_eq]
```

may possibly close the goal in one line. However, the existing

```lean
change ...
rw [neg_mul]
rfl
```

makes the exact algebraic law being used explicit and is therefore attractive from a proof-audit perspective.

Because `goldenMul` and `goldenPow` already agree by `rfl` with ring notation, there is also no need for a theorem-specific coordinate-expansion helper.

## Optimization candidates

If minimizing source lines were the only objective, a `simpa [golden_mul_eq, golden_pow_eq]`-style proof could be tested. This has not been verified here because this task does not run Lean builds.

Another possible generalization would state, for arbitrary `x y : GoldenInt`,

$$
\operatorname{snd}((-x)y)=-\operatorname{snd}(xy).
$$

However, the present theorem already leaves `epsilon` arbitrary and only specializes the right factor to `gamma^5`. Unless the same sign transformation is repeatedly needed for non-fifth-power right factors later in the development, that generalization would have little practical payoff.

The current `change` → `neg_mul` → `rfl` proof therefore appears well optimized for clarity, even if a shorter tactic proof may exist.

## Required Mathlib import and import optimization

The verified standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the generated development.

On the Mathlib side, this theorem directly needs only basic ring infrastructure, in particular `neg_mul`, together with ordinary rewriting support. `GoldenInt`, `goldenMul`, `goldenPow`, and the ring instance are project-side definitions.

Because this theorem uses none of `ring`, `omega`, or `norm_num`, its own Mathlib footprint is potentially smaller than that of 0264–0268. However, the repository's generated standalone artifact does not expose the exact import statement of the original source module, and no Lean build is performed here. Therefore the exact minimal import path is not asserted.

A plausible optimization is to depend only on the project module defining the golden ring structure plus the basic algebra modules needed for ring negation, but this remains unverified.

## Comparator challenge suitability

Yes. The difficulty is low, but the comparison is structurally interesting rather than computationally difficult.

Given the goal

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  ...
```

one can compare three styles:

1. A brute-force proof that unfolds `goldenMul` and finishes with polynomial normalization.
2. A proof that explicitly rewrites through `golden_mul_eq` / `golden_pow_eq` and then uses abstract ring laws.
3. The current minimal structural proof using `change`, `neg_mul`, and `rfl`.

The interesting metric is therefore not merely proof length, but whether the solver recognizes the existing algebraic structure and avoids unnecessary coordinate computation.

## PDF correspondence

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as verified repository files.

In this run, the GitHub connector could not provide the binary PDF body in an analyzable form, and an external attempt to retrieve the PDF body also did not succeed. Therefore no exact page number, section number, or one-to-one PDF correspondence is claimed for 0269. The technical explanation above is grounded in the Lean source held by the repository.

## Next declaration to read

The next declaration is `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq`.

In the canonical source it appears immediately after `golden_neg_unit_mul_fifth_snd`, with a comment stating that the packet's large five-adic coordinate survives in every finite unit sector.

This marks the transition from coordinate formulas for unit representatives to packet-level arithmetic: the second-coordinate information already carried by `SignedGoldenRamifierStrippedPacket.beta` is transported into the sector representation. With 0269, sign handling for the units is complete; the next theorem starts connecting that normalized sector description to the divisibility data used to eliminate nonzero sectors.
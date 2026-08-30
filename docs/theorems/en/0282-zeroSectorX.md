# 0282 — `zeroSectorX`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It introduces a new integer coordinate used by the zero-sector inversion layer. From the two coordinates `r,s` of `gamma = (r,s)`, it extracts the diagonal linear combination

$$
X=2r+s.
$$

## Lean type

```lean
/-- The diagonal coordinate `X = 2*r+s`. -/
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

Hence its complete Lean type is

```lean
zeroSectorX : ℤ → ℤ → ℤ
```

## Mathematical meaning

For inputs `r,s : ℤ`,

$$
\operatorname{zeroSectorX}(r,s)=2r+s.
$$

The definition itself proves no new proposition. Its importance is representational: the preceding zero-sector arithmetic manipulates the coordinates `r,s` and the quartic factor directly, whereas the inversion layer begins by changing coordinates.

At the beginning of `SignedGoldenZeroSectorInversion.lean`, this `X` is immediately followed by

$$
U=X^2+5s^2,
\qquad
W=4d^5.
$$

The Lean source indeed continues with

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2


def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

Thus `zeroSectorX` is not merely a local abbreviation: it is the first coordinate transformation of the whole inversion layer.

## Role in the full proof

By 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split`, the zero-sector second coordinate and fifth-power quartic factor have been normalized to

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Starting at 0282, the proof leaves the stage of directly tracking this factorization data and begins reorganizing the polynomial relations in `r,s` into quadratic quantities suitable for inversion.

The entry point is

$$
X=2r+s.
$$

With this variable, the next definition becomes

$$
U=(2r+s)^2+5s^2.
$$

Expanding gives

$$
U=4r^2+4rs+6s^2,
$$

so `X` packages the original coordinates into the basic linear quantity used by the following quadratic construction.

The term “diagonal coordinate” is taken directly from the Lean source docstring `The diagonal coordinate`. No stronger geometric or linear-algebraic interpretation is asserted here, because such an interpretation is not determined by this `def` alone.

## Direct dependencies

### Integer type `ℤ`

Both inputs and the output are integers. Unlike the immediately preceding factorization layer, which moved through natural-number absolute values, the inversion coordinates return to `ℤ` so that signs are retained.

### Integer multiplication and addition

The body is only

```lean
2 * r + s
```

and has no dependency on another DkMath-specific definition or theorem.

### Relation to 0281

0281 is not a Lean term dependency of `zeroSectorX`. However, in the proof architecture, 0281 closes the zero-sector arithmetic module and this definition is the first declaration of the next generated source module `SignedGoldenZeroSectorInversion.lean`.

Thus **the direct code dependency is almost empty, while the architectural predecessor is 0281**.

## Definition / construction flow

### 1. Receive `r,s` as integer coordinates

```lean
(r s : ℤ)
```

The function does not take a `GoldenInt` value directly; it takes only its two integer coordinates.

### 2. Define the diagonal coordinate as a linear combination

```lean
2 * r + s
```

No lemma, case split, coercion, or proof tactic is required.

### 3. Reuse the named coordinate in the next definition

The immediately following declaration is

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

Hence subsequent theorems can treat `X` as a named inversion coordinate instead of repeatedly expanding `(2*r+s)^2`.

## Lean-specific processing

There is no proof term here: the right-hand side of the `def` is the whole definition.

Consequently,

```lean
zeroSectorX r s
```

can be unfolded to

```lean
2 * r + s
```

by definitional reduction. In particular,

```lean
zeroSectorX r s = 2 * r + s
```

is provable by `rfl`.

Later proofs may expose the definition with `unfold zeroSectorX` or by supplying `[zeroSectorX]` to simplification. Since the purpose of the name is to preserve the inversion structure, however, unfolding it only where algebraic normalization requires it is usually clearer than expanding it everywhere.

## Redundancy and duplication

The definition body itself contains essentially no redundancy.

One could eliminate `zeroSectorX` entirely and inline `2 * r + s` into all later expressions. But then the structured expression

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

would become

```lean
(2 * r + s) ^ 2 + 5 * s ^ 2
```

and the named inversion-coordinate pattern `X,U,W,...` would be lost.

Therefore inlining is possible if code size alone is optimized, but the standalone `def` is better for proof architecture and documentation readability.

## Optimization candidates

### Replacing `def` by `abbrev`

If the name were intended only as a transparently reducible abbreviation, `abbrev zeroSectorX` would be a theoretical option. However, a normal `def` gives clearer control over when later proofs unfold the coordinate boundary.

Nothing in the currently inspected source establishes that `abbrev` would be preferable.

### Dedicated unfolding lemma

One could add

```lean
@[simp] theorem zeroSectorX_eq (r s : ℤ) :
    zeroSectorX r s = 2 * r + s := rfl
```

but the definition is a single line and `simp [zeroSectorX]` already exposes it. Such a lemma would therefore likely be redundant at this stage.

### Packaging inversion coordinates in a structure

If later proofs always transport `X,U,W,A,B` together, a future design could package the inversion coordinates into a structure. The complete downstream use pattern was not re-audited for this entry, so this remains only a design possibility rather than a concrete recommended change.

## Required Mathlib imports and import optimization

The repository's standalone source of record, `Flt5DkMath/FLT5StandAlone.lean`, uses

```lean
import Mathlib
```

and the generated manifest identifies this declaration as belonging to `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`.

Taken in isolation, this `def` requires only integers `ℤ`, integer literals, multiplication, and addition, so `import Mathlib` is much broader than the declaration itself needs. However, the standalone artifact does not preserve the exact import lines of the original source module, and this run does not perform a Lean build. Therefore it is **not verified** that the whole module can safely be reduced to a particular minimal import such as `Mathlib.Data.Int.Basic`.

The sound import-optimization candidate is therefore: audit all declarations used by `SignedGoldenZeroSectorInversion.lean`, then replace the umbrella `Mathlib` dependency by specific imports if the module-level dependency graph permits it. No exact minimal import is asserted from 0282 alone.

## Comparator challenge suitability

**Low priority as a standalone challenge.**

For this definition alone, a challenge such as

```lean
example (r s : ℤ) : zeroSectorX r s = 2 * r + s := by
  rfl
```

has almost no proof-engineering space for Comparator to compare.

A more meaningful challenge would combine 0282 with later `zeroSectorU` or factorization identities and compare whether introducing `X=2r+s` materially shortens a nontrivial quartic or quadratic proof. Such a challenge should therefore target a later inversion theorem rather than 0282 by itself.

## Correspondence with the PDFs

The target branch contains the existing Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

In this run, the GitHub connector could not provide the PDF binary content in an analyzable form, so the exact page, section number, and prose corresponding to 0282 could not be verified. This document therefore does not invent a PDF page or section mapping.

All definite Lean statements in this entry are grounded in the generated source `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` contained in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is **0283 `zeroSectorU`**, also a `def`:

```lean
/-- The positive quadratic quantity `U = X^2+5*s^2`. -/
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

It directly uses the coordinate introduced in 0282,

$$
X=2r+s,
$$

to construct the quadratic inversion quantity

$$
U=X^2+5s^2.
$$

Thus the dependency order 0282 → 0283 is an explicit direct Lean dependency.

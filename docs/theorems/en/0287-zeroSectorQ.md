# 0287 — `zeroSectorQ`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It defines the natural-number auxiliary quantity `Q` used to package the product `A * B` in zero-sector inversion into a “constant coefficient times a fifth power” form.

## Lean type

```lean
/-- The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`. -/
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

Its full Lean type is

```lean
zeroSectorQ : ℕ → ℕ
```

For an input `c : ℕ`, it returns

$$
Q=5^5c^8.
$$

## Mathematical meaning

The purpose of this definition is to reorganize the variable `c` coming from the tenth-power split already obtained in the zero sector into a **fifth-power mass** suited to the subsequent inversion factorization.

Although `zeroSectorQ c` is only the product

$$
5^5c^8,
$$

its fifth power is

$$
Q^5=(5^5c^8)^5=5^{25}c^{40}.
$$

Thus the later product identity

$$
AB=4Q^5
$$

can treat the large power contribution coming from `c` as a single fifth-power block.

A key point is that `Q` is not a new independent variable. It is a deterministic abbreviation built from `c`, hiding the repeatedly occurring expression `5 ^ 5 * c ^ 8` behind a stable name.

## Role in the full proof

Declarations 0282 `zeroSectorX` through 0286 `zeroSectorB` introduced the inversion coordinates and the symmetric factor pair

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W.
$$

Declaration 0287 serves a different role. It does not define another coordinate on the `r,s,d` side. Instead, it packages the power structure on the `c` side coming from the earlier tenth-power split so that it matches the product of the inversion factors.

In the repository source, the later theorem `factor_product` uses the right-hand side

```lean
4 * (zeroSectorQ p.c : ℤ) ^ 5
```

and its final algebraic step unfolds the definition through

```lean
unfold zeroSectorQ
push_cast
ring
```

Hence this definition is best viewed as a **named boundary connecting the tenth-power data from zero-sector arithmetic with the inversion factor pair `(A,B)` in fifth-power factorization language**.

## Direct dependencies

The declaration itself has no direct dependency on a DkMath-specific definition or lemma.

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

is closed using only natural-number literals, multiplication, and exponentiation.

Its **semantic dependency**, however, is the variable `c` supplied by the preceding zero-sector tenth-power split. In the downstream `factor_product` theorem the input is `p.c`, so `c` is used as part of the inversion candidate data.

## Construction flow

Because this is a `def`, there is no proof tactic script. Lean simply registers the right-hand side as the definition value.

1. Receive `c : ℕ`.
2. Form `5 ^ 5 : ℕ`.
3. Form `c ^ 8 : ℕ`.
4. Multiply them and return the result in `ℕ`.

Mathematically this is the map

$$
c
\longmapsto
5^5c^8.
$$

## Lean-specific processing

No coercion appears in the body itself because both input and output live in `ℕ`.

In the later theorem `factor_product`, however, `A` and `B` are integer-valued, so Lean needs the coercion

```lean
(zeroSectorQ p.c : ℤ)
```

After unfolding `zeroSectorQ`, the source uses `push_cast` to move natural-number multiplication and powers into `ℤ`, after which `ring` can normalize the resulting polynomial expression.

Thus the declaration itself is cast-free, but it is intentionally designed to be transported from the natural-number fifth-power mass side into the integer-valued inversion-factor side.

## Redundancy and duplication

There is almost no redundancy in the declaration body.

Naming

```lean
5 ^ 5 * c ^ 8
```

as `zeroSectorQ` avoids repeating the same expression throughout `factor_product`, `A0_mul_B0`, `coprime_Q_d`, and the later factor-splitting layer.

In that sense this `def` is itself a duplication-reduction abstraction.

The short name `zeroSectorQ` does not by itself expose the exponents `5` and `8`, so the source docstring

```text
The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`.
```

is an important part of the interface documentation.

## Optimization candidates

### 1. The definition itself

The current form is already essentially minimal. A dedicated simplification theorem is not normally required because the definition unfolds by `rfl`.

### 2. Downstream cast API

If cast expansion is repeated often enough, one could introduce a helper such as

```lean
lemma zeroSectorQ_cast (c : ℕ) :
    (zeroSectorQ c : ℤ) = 5 ^ 5 * (c : ℤ) ^ 8 := by
  simp [zeroSectorQ]
```

However, the current repository source can already handle the relevant step using `unfold zeroSectorQ; push_cast; ring`, so whether such a helper actually reduces duplication should be decided from the downstream usage count.

### 3. Naming

`Q` is convenient for downstream algebra but semantically terse in isolation. For explanatory purposes, “fifth-power mass” is the appropriate companion phrase; the source docstring already uses exactly that description.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The declaration itself needs only very basic natural-number multiplication and exponentiation, so `import Mathlib` is clearly broader than necessary for this isolated `def`.

However, this theorem-museum task explicitly does not run a Lean build, and the **actual minimal import set of the original module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` has not been verified**. Therefore no exact reduced import list is asserted here.

## Comparator challenge suitability

**Low value as a standalone challenge.**

The declaration is only the one-line abbreviation

```lean
5 ^ 5 * c ^ 8
```

so there is little proof content to compare.

It becomes more interesting when combined with a downstream identity such as

```lean
4 * (zeroSectorQ c : ℤ) ^ 5 = ...
```

In particular, the `zeroSectorQ` expansion step inside `factor_product` combines a cast from `ℕ` to `ℤ`, powers, and ring normalization, making that fragment a reasonable small Comparator challenge.

Assessment: **definition alone: unsuitable / paired with a downstream fifth-power identity: suitable**.

## Relation to the PDFs

The target branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The normal GitHub connector text path does not expose the binary PDF body in a form usable for page-by-page analysis here, so the exact page and section corresponding to this declaration are **unverified**. This document therefore relies on the canonical Lean source and the repository-visible generated structure, and does not guess the PDF location.

## Next declaration to read

The next declaration is 0288 `sixteen_mul_goldenFifthSndFactor_eq`, and it is a **`theorem`**.

It appears immediately after `zeroSectorQ` in the canonical source.

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorU r s ^ 2 - 80 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorU zeroSectorX
  ring
```

This is the first exact diagonalization identity that reconnects the newly introduced coordinates `X,U` with the original quartic factor `goldenFifthSndFactor`.

Thus 0282–0287 complete the sequence of coordinate and mass definitions, while 0288 begins the stage where those definitions are used to prove the algebraic identities needed by the inversion argument.
# 0288 — `sixteen_mul_goldenFifthSndFactor_eq`

## Declaration kind

This declaration is a **`theorem`**.

It is the exact quartic diagonalization identity that rewrites the second-coordinate quartic factor `goldenFifthSndFactor r s` appearing in the fifth power of a golden integer by means of the zero-sector diagonal coordinate `X = 2*r+s`.

## Lean type

```lean
/-- Exact diagonalization of the quartic second-coordinate factor. -/
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorX
  ring
```

In Lean this is an unconditional polynomial identity for arbitrary integers `r s : ℤ`.

Writing

$$
X:=\texttt{zeroSectorX}(r,s)=2r+s,
$$

the mathematical statement is

$$
16H(r,s)=X^4+10X^2s^2+5s^4,
$$

where

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s).
$$

Expanding `goldenFifthSndFactor` as used in the canonical Lean source gives

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

Thus the theorem is exactly the integer polynomial identity

$$
16(r^4+2r^3s+4r^2s^2+3rs^3+s^4)
=(2r+s)^4+10(2r+s)^2s^2+5s^4.
$$

## Mathematical meaning

The quartic `goldenFifthSndFactor` looks asymmetric in the original coordinates `r,s`. After introducing

$$
X=2r+s,
$$

the same quartic becomes

$$
X^4+10X^2s^2+5s^4
$$

up to the harmless factor 16.

This is what the source docstring calls **exact diagonalization**.

Strictly speaking, this is not diagonalization of a quadratic form in the usual linear-algebraic sense. Rather, the mixed monomials are absorbed into the coordinate `X`, leaving only the even-degree blocks `X^4`, `X^2s^2`, and `s^4`. This form is especially well suited to later nonnegativity and difference-of-squares arguments.

In particular every term on the right is nonnegative over the integers, which is precisely what the next theorem `goldenFifthSndFactor_nonneg` exploits to deduce

$$
0\le H(r,s).
$$

## Role in the full proof

Declarations 0282–0287 introduced the inversion coordinates and auxiliary masses

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
B=U+W,
\qquad
Q=5^5c^8.
$$

The present theorem 0288 is the first proof that the new coordinate `X` is not merely notation: it reorganizes the original quartic factor `H(r,s)` into a form adapted to inversion.

The chapter comment of `SignedGoldenZeroSectorInversion.lean` states that this diagonal quartic identity, together with the zero-sector tenth-power split, is used downstream to obtain

$$
AB=4Q^5.
$$

Accordingly, this theorem is the **first substantive bridge from the quartic arithmetic left by the zero-sector analysis into the inversion geometry**.

## Direct dependencies

The direct dependencies are small.

### `goldenFifthSndFactor`

This is the quartic on the left-hand side. In expanded form,

$$
r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

The proof directly unfolds this definition with

```lean
unfold goldenFifthSndFactor
```

### `zeroSectorX`

Declaration 0282 introduced

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

and the proof unfolds it as well.

### `ring`

This is not a DkMath-specific lemma, but it is the Mathlib tactic that closes the proof by normalizing both sides as polynomial expressions in a commutative ring.

The definitions `zeroSectorU`, `zeroSectorW`, `zeroSectorA`, `zeroSectorB`, and `zeroSectorQ` do not occur directly in either the statement or proof of this theorem.

## Proof flow

The proof consists of only two commands:

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

The logical flow is:

1. unfold `goldenFifthSndFactor` and `zeroSectorX`;
2. reduce the goal to an equality of integer polynomials;
3. let `ring` normalize both sides and prove that the normal forms agree.

By hand, the right-hand side expands as

$$
(2r+s)^4+10(2r+s)^2s^2+5s^4
$$

and then as

$$
16r^4+32r^3s+64r^2s^2+48rs^3+16s^4,
$$

which is

$$
16(r^4+2r^3s+4r^2s^2+3rs^3+s^4).
$$

## Lean-specific processing

The theorem remains entirely in `ℤ`. It does not involve `Nat` coercions, `natAbs`, divisibility APIs, or coprimality APIs.

The main Lean-specific point is the combination of `unfold` and `ring`.

`ring` is designed to normalize polynomial expressions, but named definitions are first exposed explicitly by

```lean
unfold goldenFifthSndFactor zeroSectorX
```

after which the goal is a plain ring identity.

The result is a computational/algebraic proof with no hypotheses at all. This is notably different from the downstream theorems that depend on a particular zero-sector candidate and its arithmetic provenance.

## Redundancy and duplication

There is essentially no redundancy in the proof body.

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

is close to minimal for this kind of identity.

The statement repeats `zeroSectorX r s` twice. One could introduce

```lean
let X := zeroSectorX r s
```

for presentation purposes, but that would add local-definition bookkeeping to the Lean proof. The current form is therefore preferable as an API theorem.

## Optimization candidates

### 1. Proof tactic

The existing `unfold ...; ring` proof is already very good. Replacing `ring` by `ring_nf` would not provide a clear advantage.

### 2. API shape

One might be tempted to solve for `H` and state the result as the right-hand side divided by 16. Over `ℤ`, however, that would introduce integer-division or divisibility issues. The present multiplied identity is stronger and cleaner for Lean.

### 3. Connection with `zeroSectorU`

Since

$$
U=X^2+5s^2,
$$

the identity can later be transformed into equivalent expressions involving `U`. If the same conversion appears repeatedly downstream, a dedicated bridge lemma could be worthwhile. Nevertheless, the current three-term nonnegative form has independent value and should be retained.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem itself, the main requirements are integer ring operations, natural-number powers, the `ring` tactic, and the already-defined `goldenFifthSndFactor` and `zeroSectorX`.

Therefore `import Mathlib` is clearly broader than this theorem alone needs. However, this theorem-museum task does not run Lean builds, so the **actual minimal import set for `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` has not been verified**. No narrower import is asserted as fact.

## Comparator challenge suitability

**Highly suitable.**

The theorem has only two substantive definitions as dependencies and its core is a pure polynomial identity. A Comparator challenge can provide the definitions and ask for

```lean
theorem challenge (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  ...
```

A solver familiar with `ring` gets a short proof, while a manual expansion is also possible. This makes it useful for comparing proof styles and normalization strategies.

Verdict: **suitable**.

## Relation to the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the ordinary GitHub connector path cannot expose their binary PDF contents as analyzable UTF-8 text. Therefore the exact PDF page, section number, and wording corresponding to this theorem are **not verified**. No PDF location is guessed here; the canonical Lean source and repository structure are used as the authoritative evidence.

## Next declaration to read

The next declaration is 0289 `goldenFifthSndFactor_nonneg`, again a **`theorem`**:

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  have hdiag : 0 ≤
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
    positivity
  have hident := sixteen_mul_goldenFifthSndFactor_eq r s
  nlinarith
```

It proves nonnegativity of the right-hand side with `positivity` and then combines that fact with theorem 0288 using `nlinarith` to conclude

$$
0\le H(r,s).
$$

Thus the dependency progression is clean: 0288 converts the original quartic into a structured algebraic form, and 0289 converts that algebraic structure into order-theoretic information.
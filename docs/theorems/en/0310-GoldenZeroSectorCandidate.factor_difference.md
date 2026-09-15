# 0310 — `GoldenZeroSectorCandidate.factor_difference`

## Declaration kind

This declaration is a **`theorem`**.

Where 0309 `GoldenZeroSectorCandidate.factor_product` fixes the product of the inversion factors,

$$
AB = 4Q^5,
$$

this theorem fixes their exact difference,

$$
B-A = 8d^5.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Exact distance between the upper and lower inversion factors. -/
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

The conclusion is an equality over the integers `ℤ`:

$$
B(r,s,d)-A(r,s,d)=8d^5.
$$

Here

$$
A=U-W,
\qquad
B=U+W,
\qquad
W=4d^5.
$$

## Mathematical meaning

Substituting the definitions directly gives

$$
B-A=(U+W)-(U-W)=2W.
$$

Since

$$
W=4d^5,
$$

we obtain

$$
B-A=2\cdot4d^5=8d^5.
$$

Thus the theorem does not introduce a new number-theoretic hypothesis. It packages the symmetry already built into the definitions of the inversion factors as an exact reusable equality.

## Role in the whole proof

The zero-sector inversion has already produced in 0309 the multiplicative constraint

$$
AB=4Q^5.
$$

The present theorem supplies an independent additive constraint,

$$
B-A=8d^5.
$$

The product alone does not fully constrain the placement of `A` and `B`; the exact difference also fixes the distance between the two factors. Later, after positive natural representatives `A0` and `B0` are introduced, this theorem is converted into the subtraction-free natural-number identity

$$
B_0=A_0+8d^5,
$$

namely `B0_eq_A0_add`.

`GoldenZeroSectorInversionPacket` then stores that natural-number factor difference as a field, and downstream gcd and two-adic branch analysis uses it. Therefore, despite its very short proof, this theorem is a foundational API bridge from the symmetric integer factorization to natural-number factor arithmetic.

## Direct dependencies

### `zeroSectorA`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

This is the lower inversion factor

$$
A=U-W.
$$

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

This is the upper inversion factor

$$
B=U+W.
$$

### `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

This defines the fifth-power coordinate separating the two factors,

$$
W=4d^5.
$$

### `ring`

After unfolding `zeroSectorA`, `zeroSectorB`, and `zeroSectorW`, `ring` normalizes and closes the commutative-ring identity

$$
(U+4d^5)-(U-4d^5)=8d^5.
$$

## Proof / construction flow

1. `unfold zeroSectorA zeroSectorB zeroSectorW` expands the three definitions.
2. The left-hand side becomes the integer expression

$$
(U+4d^5)-(U-4d^5).
$$

3. `ring` cancels `U`, normalizes the coefficients, and produces

$$
8d^5.
$$

No hypothesis field of `GoldenZeroSectorCandidate` is used in the proof. Only the coordinates `p.r`, `p.s`, and `p.d` are substituted into the definitions.

## Lean-specific processing

Although `p.d : ℕ`, the definition `zeroSectorW` returns

```lean
4 * (p.d : ℤ) ^ 5
```

so the theorem is naturally stated over `ℤ`. The cast is already explicit inside `zeroSectorW`; therefore the proof needs neither `push_cast` nor `exact_mod_cast`.

Subtraction is another reason why the integer formulation is convenient. The later theorem `B0_eq_A0_add` moves to a subtraction-free identity over `ℕ` only after positivity and natural representatives have been established.

Once the definitions are unfolded, the goal is a pure polynomial identity, making `ring` the natural tactic.

## Redundancy and duplication

The proof consists only of

```lean
unfold zeroSectorA zeroSectorB zeroSectorW
ring
```

so there is essentially no local redundancy.

Mathematically, one could first isolate the generic identity

$$
(U+W)-(U-W)=2W
$$

and then apply `W=4d^5`. Unless that generic identity is reused elsewhere, however, the current direct unfolding is shorter and clearer.

## Optimization candidates

A possible API-level optimization is to introduce a candidate-independent theorem such as

```lean
zeroSectorB r s d - zeroSectorA r s d = 2 * zeroSectorW d
```

and let the present theorem reduce only the definition of `zeroSectorW`.

Whether this is worthwhile depends on downstream reuse: the current theorem already has a two-line proof, so adding a new declaration may increase surface area without reducing complexity.

There is no obvious need to combine `ring_nf` or `norm_num`; a single `ring` call is already concise. Because Lean builds are forbidden for this task, no claim is made that a shorter proof or a minimal import set has been mechanically verified.

## Required Mathlib imports and import-optimization candidates

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The present theorem directly requires at least:

- `ℕ` and `ℤ`,
- the cast from `Nat` to `Int`,
- integer addition, subtraction, multiplication, and powers,
- `unfold`,
- `ring`,
- `zeroSectorA`,
- `zeroSectorB`,
- `zeroSectorW`.

The proof does not directly use `omega`, `linarith`, `nlinarith`, `positivity`, `push_cast`, or `exact_mod_cast`.

The generated source module is `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`. It is likely possible to replace the broad `Mathlib` import by the ring tactic plus basic integer/natural algebra imports, but the exact minimal set has not been verified because Lean builds are explicitly excluded.

## Comparator challenge suitability

**Suitable. Difficulty: beginner to intermediate.**

Because the theorem itself is short, the interesting comparison is proof engineering rather than proof search:

- the minimal `unfold` + `ring` proof,
- a proof using `change` to expose the `U`,`W` structure,
- a design that first introduces a reusable theorem `zeroSectorB - zeroSectorA = 2 * zeroSectorW`,
- readability and stability of `ring` versus `ring_nf`.

An especially useful comparator criterion is whether the solver notices that no candidate-specific hypothesis is needed and that the theorem follows from definitions alone.

## Comparison with the PDFs

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The normal GitHub text fetch used in this run does not expose the binary PDF body, so the exact page, section, and equation number corresponding to this theorem have not been directly checked. No guess is made about that location.

The Lean code, declaration order, definitions, direct dependencies, and relation to subsequent declarations in this explanation are grounded in the repository canonical source `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0311 `GoldenZeroSectorCandidate.factor_sum`, again a **`theorem`**.

The Lean canonical source continues with

```lean
/-- Exact sum of the two inversion factors. -/
theorem factor_sum (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d + zeroSectorB p.r p.s p.d =
      2 * zeroSectorU p.r p.s := by
  unfold zeroSectorA zeroSectorB
  ring
```

Where 0310 fixes the difference

$$
B-A=8d^5,
$$

0311 fixes the sum

$$
A+B=2U.
$$

With product, difference, and sum all exposed, the arithmetic API for the inversion factors becomes substantially more complete.
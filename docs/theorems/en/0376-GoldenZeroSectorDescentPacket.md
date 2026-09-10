# 0376 `GoldenZeroSectorDescentPacket`

## Declaration kind

`structure`

This is not a theorem. It is a structure declaration bundling the conditions preserved at every stage of the zero-sector infinite descent into a single type.

## Lean code

```lean
/--
The invariant preserved by the fifth-power re-entry.  The visible coordinate
is five times a fifth power, and the quartic is itself a fifth power.  Keeping
both statements is what makes the construction genuinely recursive.
-/
structure GoldenZeroSectorDescentPacket where
  base : GoldenInt
  t : ℕ
  D : ℕ
  t_pos : 0 < t
  D_pos : 0 < D
  coprime_coords : Nat.Coprime base.fst.natAbs base.snd.natAbs
  snd_eq :
    base.snd = 5 * (t : ℤ) ^ 5 ∨
      base.snd = -(5 * (t : ℤ) ^ 5)
  H_eq :
    goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5
  five_not_dvd_norm : ¬ (5 : ℤ) ∣ goldenNorm base
```

## Lean type

Expanding the constructor type conceptually, the following data produce a value of `GoldenZeroSectorDescentPacket`.

```lean
GoldenZeroSectorDescentPacket.mk :
  (base : GoldenInt) →
  (t D : ℕ) →
  0 < t →
  0 < D →
  Nat.Coprime base.fst.natAbs base.snd.natAbs →
  (base.snd = 5 * (t : ℤ) ^ 5 ∨
    base.snd = -(5 * (t : ℤ) ^ 5)) →
  goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5 →
  (¬ (5 : ℤ) ∣ goldenNorm base) →
  GoldenZeroSectorDescentPacket
```

Each field is also available as a projection. For `p : GoldenZeroSectorDescentPacket`, one obtains `p.base`, `p.t`, `p.D`, `p.snd_eq`, `p.H_eq`, and so on.

## Mathematical meaning

Write `base = (r,s)`. The packet simultaneously records the following facts at one stage of the zero-sector descent:

$$
(r,s)\in\mathbb Z^2,
$$

$$
t>0,\qquad D>0,
$$

$$
\gcd(|r|,|s|)=1,
$$

$$
s=5t^5\quad\text{or}\quad s=-5t^5,
$$

$$
H(r,s)=D^5,
$$

and

$$
5\nmid N(r,s).
$$

Here `H` denotes `goldenFifthSndFactor`, while `N` denotes `goldenNorm`.

The important point is that this does not merely record that the current `base` satisfies one fifth-power equation. It stores **the complete set of hypotheses needed to construct the next descent stage again**.

The quadratic lift introduced in 0372--0375,

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr),
$$

returns the quartic factor to a golden-integer norm and conjugate-product problem. This structure turns that re-entry from a one-shot algebraic transformation into a recursive state that can be reproduced on smaller data.

## Role in the whole proof

The zero-sector elimination in the FLT5 development does not merely assume a fifth power and derive an immediate contradiction. Instead, it reconstructs another packet with the same invariant properties but with a strictly smaller measure.

The required pattern is

$$
P\longmapsto P',
$$

$$
P'\text{ satisfies the same invariant conditions as }P,
$$

$$
\mu(P')<\mu(P).
$$

`GoldenZeroSectorDescentPacket` fixes the phrase “the same invariant conditions” as a Lean type. Later, `GoldenZeroSectorStrictDescent` stores `next : GoldenZeroSectorDescentPacket` together with strict measure decrease.

Thus this structure is the **state space of the zero-sector infinite descent**.

## Meaning of each field

### `base : GoldenInt`

The current golden integer. Write

$$
base=(r,s).
$$

### `t : ℕ`, `t_pos : 0 < t`

A positive fifth-root parameter used to express the second coordinate as `±5 t^5`.

### `D : ℕ`, `D_pos : 0 < D`

The fifth root of the quartic factor `goldenFifthSndFactor r s`.

### `coprime_coords`

```lean
Nat.Coprime base.fst.natAbs base.snd.natAbs
```

The signed integer coordinates are sent to natural numbers by `natAbs`, preserving the primitive-coordinate condition.

Mathematically,

$$
\gcd(|r|,|s|)=1.
$$

### `snd_eq`

```lean
base.snd = 5 * (t : ℤ) ^ 5 ∨
  base.snd = -(5 * (t : ℤ) ^ 5)
```

The sign of the second coordinate is not fixed. Both the positive and negative signed fifth-power forms are retained in one packet. This is compatible with the odd exponent 5.

### `H_eq`

```lean
goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5
```

This preserves the fact that the quartic factor returned to a norm/conjugate-product form in 0374--0375 is itself a fifth power.

Because this field is retained, the next stage can again extract a fifth root and rebuild a packet of the same shape.

### `five_not_dvd_norm`

```lean
¬ (5 : ℤ) ∣ goldenNorm base
```

This stores the side condition that the exceptional prime 5 does not enter the norm. It acts as a clean condition when the golden-integer factorization and coprimality machinery extracts fifth-power roots.

## Direct dependencies

Because this declaration has no proof body, its direct dependencies are mainly types and definitions.

- `GoldenInt`: the type of `base`.
- `goldenFifthSndFactor`: the left-hand side of `H_eq`.
- `goldenNorm`: the target of `five_not_dvd_norm`.
- `Nat.Coprime`: the primitive-coordinate condition.
- `Int.natAbs`: sends signed coordinates to the natural-number gcd condition.
- Natural/integer powers, integer coercions, and integer divisibility.

0372 `goldenZeroSectorLift`, 0374 `goldenZeroSectorLift_norm`, and 0375 `goldenZeroSectorLift_mul_conj` are not definitional dependencies of the structure fields themselves. In the proof dependency graph, however, they are the immediately preceding algebraic re-entry machinery used to create and update packets of this type.

## Construction flow

Since this is a `structure`, the declaration itself contains no tactic proof. A value is built by supplying every field.

A typical construction has the form

```lean
{
  base := ...
  t := ...
  D := ...
  t_pos := ...
  D_pos := ...
  coprime_coords := ...
  snd_eq := ...
  H_eq := ...
  five_not_dvd_norm := ...
}
```

Later code rebuilds this record from candidate data or from a fifth root, then uses the whole record as the input to the strict descent.

## Lean-specific processing

### `structure ... where`

This turns several mathematical assumptions into one bundled object. Downstream theorems can receive a single `p : GoldenZeroSectorDescentPacket` instead of repeatedly accepting roughly eight related arguments.

### Coercions `(t : ℤ)` and `(D : ℤ)`

`t` and `D` are stored as natural numbers so that positivity and measure arguments remain natural-number statements. The second coordinate and `goldenFifthSndFactor` are integer-valued, so the equalities explicitly cast the roots to `ℤ`.

### `base.fst.natAbs`, `base.snd.natAbs`

`Nat.Coprime` is a predicate on natural numbers. Using `natAbs` expresses primitivity of integer coordinates while ignoring their signs.

### Explicit sign split with `∨`

`snd_eq` keeps the two sign branches instead of compressing them into an absolute-value identity such as `|s| = 5 t^5`. This design makes later sign-sensitive rewriting more direct.

## Redundancy and overlap

The structure contains intentional redundancy.

`t_pos` and `D_pos` might in some settings be derivable from `snd_eq`, `H_eq`, and suitable nonzero assumptions, but keeping positivity as explicit fields simplifies downstream proofs.

Likewise, `snd_eq` could be compressed using absolute values. That would require later lemmas to recover the sign branch, so it would not necessarily reduce proof complexity.

`coprime_coords` is initially derived from primitive candidate data, but re-proving and storing it at each descent stage makes the recursive invariant self-contained. It is therefore better viewed as a **proof cache needed for recursive closure** than as accidental duplication.

## Optimization candidates

1. Introduce a dedicated predicate such as `IsSignedFiveTimesFifthPower base.snd t` for `snd_eq` if the same signed equation recurs elsewhere.

2. Bundle `base.fst.natAbs` / `base.snd.natAbs` into a golden-integer primitivity predicate if coordinate coprimality appears repeatedly across modules.

3. Encode `t` and `D` as positive-natural subtypes. This is possible, but it may increase coercion overhead and friction with existing lemmas; the current plain `ℕ` plus positivity-field design may therefore be more practical in Lean.

4. `H_eq` and `five_not_dvd_norm` are core descent invariants. Splitting them into another packet would likely make strong-induction interfaces less transparent than the current unified record.

These are design alternatives, not evidence that the repository definition is incorrect or unnecessarily verbose.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

For this structure alone, the Mathlib-side requirements are roughly limited to

- `Nat.Coprime`,
- `Int.natAbs`,
- powers,
- integer divisibility,
- coercions between `Nat` and `Int`.

However, `GoldenInt`, `goldenFifthSndFactor`, and `goldenNorm` are project definitions, and the true minimal import set for the modular source depends on where those earlier definitions are imported from.

The standalone artifact by itself is insufficient to certify the exact minimal Mathlib import set. No Lean build was performed in this run, so import reduction has not been mechanically validated.

## Comparator challenge suitability

**Suitable, especially as a structure-reconstruction challenge.**

Simply asking the model to reproduce the declaration would be weak. A better challenge is to reconstruct an equivalent packet from its projections and constructor.

For example:

```lean
example (p : GoldenZeroSectorDescentPacket) :
    GoldenZeroSectorDescentPacket := by
  exact {
    base := p.base
    t := p.t
    D := p.D
    t_pos := p.t_pos
    D_pos := p.D_pos
    coprime_coords := p.coprime_coords
    snd_eq := p.snd_eq
    H_eq := p.H_eq
    five_not_dvd_norm := p.five_not_dvd_norm }
```

This can be extended into a challenge that packages candidate data into the descent invariant.

For Comparator, the interesting skill is not deep theorem proving but **accurate reconstruction of a bundled invariant with dependent fields**.

## Next declaration to read

The next declaration is

```lean
def goldenZeroSectorDescentMeasure (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

Where 0376 defines the state space of the descent, this next definition assigns the natural-number measure

$$
\mu(P)=|P.base.snd|.
$$

Later `GoldenZeroSectorStrictDescent` records that this measure strictly decreases on the next packet, and the final closure uses `Nat.strong_induction_on` to rule out the existence of a zero-sector packet altogether.

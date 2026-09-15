# 0377 `goldenZeroSectorDescentMeasure`

## Declaration kind

`def`

This is not a theorem. It is the definition that assigns a natural-valued descent measure to a `GoldenZeroSectorDescentPacket`.

## Lean code

```lean
/-- The positive natural measure decreased by every certified descent step. -/
def goldenZeroSectorDescentMeasure
    (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

## Lean type

```lean
goldenZeroSectorDescentMeasure :
  GoldenZeroSectorDescentPacket → ℕ
```

It takes one `GoldenZeroSectorDescentPacket` and returns the absolute value of the second coordinate `snd : ℤ` of its `base`, represented as a natural number.

Since `p.base.snd.natAbs` sends the absolute value of an integer to `ℕ`, mathematically

$$
\mu(p)=|p.base.snd|.
$$

## Mathematical meaning

Write `p.base=(r,s)`. Then

$$
\mu(p)=|s|.
$$

In 0376 `GoldenZeroSectorDescentPacket`, the second coordinate is constrained to have the form

$$
s=5t^5\quad\text{or}\quad s=-5t^5,
\qquad t>0.
$$

Hence, on a valid packet,

$$
\mu(p)=5t^5>0.
$$

That equation is not part of the body of this `def`, however. `goldenZeroSectorDescentMeasure` merely chooses `|s|` as the rank. Positivity must be obtained from later lemmas using the packet fields `t_pos` and `snd_eq`.

The important design choice is that the signed integer coordinate `s : ℤ` is not used directly as an order parameter. Instead, `natAbs` moves it into the well-founded order on natural numbers.

## Role in the whole proof

The zero-sector contradiction is closed by infinite descent: a packet satisfying the same invariant is mapped to a strictly smaller packet. What is needed is

$$
P\longmapsto P'
$$

along with

$$
\mu(P')<\mu(P)
$$

for a well-founded measure `μ`.

This definition fixes that measure.

The later structure

```lean
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

builds the present measure directly into the definition of a certified strict descent step.

Finally, `goldenZeroSectorDescentPacket_false` performs

```lean
induction n using Nat.strong_induction_on
```

with `goldenZeroSectorDescentMeasure q = n` as the induction index. The inequality `step.measure_lt` provides the smaller index needed to invoke the induction hypothesis.

Thus this `def` is the **rank function** that connects the algebraic fifth-power re-entry to Lean's well-founded natural-number induction.

## Direct dependencies

The direct dependencies are very small.

- `GoldenZeroSectorDescentPacket`
  - input type.
- `GoldenZeroSectorDescentPacket.base`
  - projection of the current `GoldenInt`.
- `GoldenInt.snd`
  - second integer coordinate.
- `Int.natAbs`
  - absolute value of an integer returned in `ℕ`.

The definition itself does not inspect proof fields such as `snd_eq`, `t_pos`, `H_eq`, or `five_not_dvd_norm`.

At the level of proof architecture, however, it is directly tied to the invariant packaged in 0376 and to the later `GoldenZeroSectorStrictDescent.measure_lt` and `goldenZeroSectorDescentPacket_false`.

## Definition flow

The computation is a single projection chain.

1. `p.base` obtains the current golden integer from the packet.
2. `.snd` obtains its second coordinate `s : ℤ`.
3. `.natAbs` removes the sign and returns `|s| : ℕ`.

In formulas,

$$
p\mapsto p.base\mapsto p.base.snd\mapsto |p.base.snd|.
$$

No proof tactic or auxiliary lemma is required.

## Lean-specific processing

### `Int.natAbs`

Since `p.base.snd : ℤ`, it cannot directly serve as the index for `Nat.strong_induction_on`. `Int.natAbs` produces

```lean
p.base.snd.natAbs : ℕ
```

and thereby connects the signed coordinate to standard strong induction on natural numbers.

### Chained structure projections

```lean
p.base.snd.natAbs
```

is a compact projection chain corresponding conceptually to

```lean
Int.natAbs (GoldenInt.snd p.base)
```

This keeps the definition of the measure visibly independent of the surrounding algebraic implementation.

### A reducible `def`

Because this is an ordinary `def`, it can be unfolded in simp/unfold contexts as

```lean
[goldenZeroSectorDescentMeasure]
```

when concrete coordinate calculations are required. In abstract strict-descent statements, however, keeping the named measure opaque at the surface level is useful.

## Why the second coordinate is used

The packet contains several plausible quantities from which one could define a rank, including `base`, `t`, and `D`. The repository instead chooses `|base.snd|`.

This matches the fact that the visible second coordinate satisfies

$$
s=\pm5t^5
$$

and is tracked directly through the quadratic lift and the repeated fifth-root construction.

Using `t` as the measure is conceptually possible, but the current strict descent is formulated by comparing the actual second coordinates of successive packets. Choosing `|s|` therefore avoids introducing extra casts or monotonicity lemmas for fifth powers.

`D` is crucial algebraic data as the fifth root of the quartic factor, but it is not chosen as the quantity controlling the final well-founded order.

## Redundancy and duplication

There is essentially no duplication in the definition itself.

However, the packet field `snd_eq` implies

$$
\mu(p)=5p.t^5,
$$

so if later proofs repeatedly unfold `natAbs` and split on the sign of `snd_eq`, there is room for a shared API lemma.

A possible theorem would be conceptually

```lean
theorem goldenZeroSectorDescentMeasure_eq
    (p : GoldenZeroSectorDescentPacket) :
    goldenZeroSectorDescentMeasure p = 5 * p.t ^ 5 := ...
```

The existence of this exact theorem in the repository was not confirmed in this pass; it is an optimization proposal, not a claim about the current source.

## Optimization candidates

1. **Add a named value formula for the measure.**

   Using `snd_eq` and `t_pos`, expose

   $$
   \mu(p)=5t^5.
   $$

   This would move some later measure arguments entirely into natural-number arithmetic.

2. **Add a positivity lemma.**

   Since `t>0` for every packet,

   $$
   0<\mu(p)
   $$

   follows and may deserve a `measure_pos` theorem if it occurs repeatedly.

3. **Be cautious with `@[simp]`.**

   Automatically unfolding `goldenZeroSectorDescentMeasure` into `natAbs` everywhere could destroy the useful abstraction boundary of strict-descent statements too early. Keeping the current named abstraction has value.

4. **Generalize to a `WellFounded` abstraction only if reused.**

   A future common descent framework could package a packet type and rank function generically. For FLT5 alone, however, `Nat.strong_induction_on` is simpler and such an abstraction may be unnecessary.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The central Mathlib feature directly used by this `def` is `Int.natAbs`, together with the basic `Nat` and `Int` types. The input type `GoldenZeroSectorDescentPacket` is a project-local definition, so the modular source must also import the module that provides that packet.

If downstream use is included, `Nat.strong_induction_on`, integer/natural casts, and order lemmas also become relevant, but those are not direct dependencies of this definition alone.

The exact minimal Mathlib import set has not been mechanically verified because no Lean build is performed in this task. Therefore any concrete reduction from `import Mathlib` remains a candidate rather than a confirmed minimal import list.

## Comparator challenge suitability

**Suitable, especially as a small definition/unfolding challenge.**

Reconstructing the definition itself is very easy, but one can test the boundary between the abstract measure and its concrete coordinate representation.

For example,

```lean
example (p : GoldenZeroSectorDescentPacket) :
    goldenZeroSectorDescentMeasure p = p.base.snd.natAbs := by
  rfl
```

is a minimal definitional-equality challenge.

A stronger version can use `p.snd_eq` to prove

$$
\mu(p)=5p.t^5,
$$

which exercises `rcases`, integer `natAbs`, casts, powers, and sign branches.

An even more meaningful Comparator task can start from `GoldenZeroSectorStrictDescent.measure_lt` and ask for the strong-induction step, checking that the model understands that this accessor is the well-founded rank rather than merely an arbitrary projection.

## Next declaration to read

The next declaration is inside namespace `GoldenZeroSectorDescentPacket`:

```lean
theorem snd_ne_zero (p : GoldenZeroSectorDescentPacket) :
    p.base.snd ≠ 0 := by
  have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
  rcases p.snd_eq with h | h
  · rw [h]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
  ...
```

It extracts from `snd_eq` and `t_pos` the fact that the second coordinate underlying the measure is genuinely nonzero.

Where 0377 **defines** the rank

$$
\mu(p)=|s|,
$$

the next theorem proves from the packet invariant that

$$
s\ne0,
$$

which then feeds the later positivity chain through

$$
s^2>0.
$$

This is the entry point for the positivity arguments used in the fifth-root re-entry.
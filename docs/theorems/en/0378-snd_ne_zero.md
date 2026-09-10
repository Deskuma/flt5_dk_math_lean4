# 0378 `snd_ne_zero`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma proves that the second coordinate of the packet is nonzero.

## Lean code

```lean
theorem snd_ne_zero (p : GoldenZeroSectorDescentPacket) :
    p.base.snd ≠ 0 := by
  have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
  rcases p.snd_eq with h | h
  · rw [h]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
  · rw [h]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5)))
```

## Lean type

After expanding the namespace qualification, its type is conceptually

```lean
GoldenZeroSectorDescentPacket.snd_ne_zero :
  (p : GoldenZeroSectorDescentPacket) → p.base.snd ≠ 0
```

Here `p.base.snd : ℤ` is the second coordinate of the current golden integer stored in the packet, and the theorem returns

$$
p.base.snd \ne 0.
$$

## Mathematical statement

0376 `GoldenZeroSectorDescentPacket` stores

$$
t>0
$$

and

$$
s=5t^5 \quad\text{or}\quad s=-5t^5,
$$

where `s = p.base.snd`.

Therefore

$$
5t^5>0,
$$

so in the positive-sign branch

$$
s>0 \Longrightarrow s\ne0,
$$

while in the negative-sign branch

$$
s=-5t^5 \Longrightarrow s\ne0.
$$

This theorem packages that elementary fact as part of the packet API.

## Role in the full proof

This lemma is the entry point to the positivity chain in the zero-sector infinite descent.

Later lemmas work with the absolute value, the square of `p.base.snd`, and the fifth-root re-entry. In particular, `fifthRoot_H_pos` and `fifthRoot_snd_pos` use the theorem in the form

```lean
have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
```

so the logical flow is

$$
p.t>0
\Longrightarrow p.base.snd\ne0
\Longrightarrow p.base.snd^2>0.
$$

That positivity is then propagated to the fifth-root second coordinate and to the quartic factor.

It also supplies the basic nondegeneracy fact behind the measure introduced in 0377,

$$
\mu(p)=|p.base.snd|,
$$

showing that the quantity being measured is genuinely nonzero for every descent packet.

## Direct dependencies

The declaration directly uses:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.t_pos`
- `GoldenZeroSectorDescentPacket.snd_eq`
- `exact_mod_cast`
- `pow_pos`
- `mul_pos`
- `ne_of_gt`
- `neg_ne_zero.mpr`
- `norm_num`

The mathematical core depends only on the two packet fields `t_pos` and `snd_eq`.

## Proof flow

1. Convert `p.t_pos : 0 < p.t` from `ℕ` to `ℤ`:

   ```lean
   have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
   ```

2. Split the disjunction `p.snd_eq`:

   ```lean
   rcases p.snd_eq with h | h
   ```

   yielding either

   $$
   s=5t^5
   $$

   or

   $$
   s=-5t^5.
   $$

3. In the positive branch, rewrite with `h`, prove $5t^5>0$ using `pow_pos` and `mul_pos`, then obtain nonzeroness with `ne_of_gt`.

4. In the negative branch, prove the same positive quantity nonzero and transport nonzeroness through the outer minus sign using `neg_ne_zero.mpr`.

## Lean-specific processing

### `exact_mod_cast`

The stored proof `p.t_pos` lives over natural numbers, while the equation for the second coordinate is over integers. The proof therefore begins by moving positivity across the cast:

```lean
have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
```

This gives the exact type required by the integer-order positivity lemmas.

### `rcases ... with h | h`

`p.snd_eq` is a disjunction. The proof handles the positive and negative signs separately, matching the packet design: the sign is not fixed, but the absolute fifth-power mass is.

### `rw [h]`

The abstract coordinate `p.base.snd` is replaced by the explicit expression $\pm5t^5$, reducing the remaining goal to elementary integer arithmetic.

### `ne_of_gt` and `neg_ne_zero.mpr`

The positive branch derives nonzeroness from strict positivity. The negative branch uses the equivalence between nonzeroness of `x` and nonzeroness of `-x`.

## Redundancy and overlap

The expression

```lean
ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
```

is essentially duplicated across the two sign branches.

One could first prove

```lean
have hpos : (0 : ℤ) < 5 * (p.t : ℤ) ^ 5 :=
  mul_pos (by norm_num) (pow_pos ht 5)
have hne : (5 : ℤ) * (p.t : ℤ) ^ 5 ≠ 0 := ne_of_gt hpos
```

and reuse `hne` in both branches.

The present proof is nevertheless short and keeps the two mathematical sign cases explicit, so the duplication is a reasonable readability tradeoff.

## Optimization candidates

1. If `snd_natAbs_eq` were available earlier in the dependency order, one could derive nonzeroness from the exact absolute-value identity $|s|=5t^5$ and `t_pos`. In the current source order, however, `snd_ne_zero` precedes that theorem, so the direct proof avoids an unnecessary dependency reversal.

2. The common positivity proof for $5t^5$ could be factored into a local lemma to eliminate branch duplication.

3. If a `measure_pos` API is later added, 0377 `goldenZeroSectorDescentMeasure` together with this theorem should make its proof short and reusable.

4. The packet could theoretically separate `snd_eq` into an absolute-value equation plus sign information, but later proofs also use the signed equation directly, so the current disjunctive representation has a clear purpose.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The theorem itself directly needs natural/integer casts, order lemmas, integer powers, `exact_mod_cast`, `norm_num`, and basic nonzero lemmas.

The input type `GoldenZeroSectorDescentPacket` also depends on earlier project definitions, so the modular source must import the project module that provides that packet.

The exact minimal Mathlib import set was not verified because no Lean build is performed in this task. Therefore any reduction from `import Mathlib` remains only a candidate optimization.

## Comparator challenge suitability

**Yes. It makes a small but useful cast/sign-split challenge.**

The core skills tested are:

- transporting positivity from `Nat` to `Int`;
- splitting a disjunction into the two sign cases;
- constructing nonzeroness from positivity.

The theorem can be used directly as a fill-the-proof challenge. A stronger version could forbid `exact_mod_cast` and require explicit cast lemmas, making the task a better test of Lean's coercion and arithmetic interfaces.

## Next declaration to read

The next declaration in the same namespace is

```lean
theorem snd_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    p.base.snd.natAbs = 5 * p.t ^ 5 := by
  rcases p.snd_eq with h | h <;> rw [h]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
```

The present theorem extracts the qualitative fact

$$
s\ne0,
$$

while the next theorem gives the exact quantitative identity

$$
|s|=5t^5.
$$

That identity connects directly to the measure from 0377 and makes the magnitude comparison in the zero-sector descent explicit.
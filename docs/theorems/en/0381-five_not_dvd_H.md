# 0381 `five_not_dvd_H`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma transfers the packet's nondivisibility-by-five information from the base norm to the quartic factor `goldenFifthSndFactor`, using the fact that `goldenFifthSndFactor - goldenNorm^2` is divisible by five.

## Lean code

```lean
theorem five_not_dvd_H (p : GoldenZeroSectorDescentPacket) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd := by
  intro hH
  apply p.five_not_dvd_norm
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq p.base
  have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

## Lean type

Expanding the namespace, the type is conceptually

```lean
GoldenZeroSectorDescentPacket.five_not_dvd_H :
  (p : GoldenZeroSectorDescentPacket) →
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

Since `p.base : GoldenInt`, both `p.base.fst` and `p.base.snd` are integers, and

```lean
goldenFifthSndFactor p.base.fst p.base.snd : ℤ
```

so the divisibility statement is in `ℤ`.

The packet itself stores the field

```lean
five_not_dvd_norm : ¬ (5 : ℤ) ∣ goldenNorm base
```

and this theorem transports that norm-side nondivisibility to the quartic factor.

## Mathematical statement

Write `base = (r,s)` and set

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
N(r,s)=\operatorname{goldenNorm}(r,s).
$$

The earlier lemma `five_dvd_goldenFifthSndFactor_sub_norm_sq` gives, for this base,

$$
5 \mid H(r,s)-N(r,s)^2.
$$

Meanwhile the descent packet stores the invariant

$$
5\nmid N(r,s).
$$

If, contrary to the target conclusion,

$$
5\mid H(r,s),
$$

then subtracting the divisible difference yields

$$
5\mid N(r,s)^2.
$$

Because 5 is prime,

$$
5\mid N(r,s)^2
\Longrightarrow
5\mid N(r,s),
$$

contradicting the packet invariant. Therefore

$$
5\nmid H(r,s).
$$

## Role in the full proof

0380 `H_pos` exposed the order-theoretic fact

$$
H(r,s)>0.
$$

The present `five_not_dvd_H` exposes the complementary 5-adic/divisibility fact

$$
5\nmid H(r,s).
$$

Thus the quartic side of the descent packet is now both

$$
\text{positive}
\quad+\quad
\text{prime to }5.
$$

The immediately following theorem `five_not_dvd_D` combines this result with the packet equation

$$
H(r,s)=D^5
$$

to deduce

$$
5\nmid D.
$$

That fact is then used downstream when `lift_relPrime_conj` builds coprimality between `D^5` and 5, a key ingredient in proving that the quadratic re-entry element and its conjugate have no nonunit common divisor.

Accordingly, this theorem is the bridge that converts the packet's norm-side 5-adic cleanliness into a form usable by the fifth-power root `D` and the re-entry factorization.

## Direct dependencies

The direct project declarations are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.five_not_dvd_norm`
- `goldenFifthSndFactor`
- `goldenNorm`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`

From its use in the proof, `five_dvd_goldenFifthSndFactor_sub_norm_sq p.base` is used in the form

```lean
(5 : ℤ) ∣
  goldenFifthSndFactor p.base.fst p.base.snd -
    goldenNorm p.base ^ 2
```

or an equivalent proposition reducible to that form.

The principal Lean/Mathlib facilities used directly are:

- `dvd_sub`
- `ring_nf`
- `Prime.dvd_of_dvd_pow`
- `norm_num`
- `intro`, `apply`, `have`, `exact`

The theorem does not directly depend on 0380 `H_pos` or 0379 `snd_natAbs_eq`; it closes entirely from `five_not_dvd_norm` and the quartic/norm congruence.

## Proof flow

1. Negate the target and assume that the quartic factor is divisible by five.

   ```lean
   intro hH
   ```

   Thus

   $$
   5\mid H(r,s).
   $$

2. Apply the packet's

   ```lean
   p.five_not_dvd_norm
   ```

   to reduce the contradiction goal to proving

   ```lean
   (5 : ℤ) ∣ goldenNorm p.base
   ```

3. Obtain the existing congruence lemma.

   ```lean
   have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq p.base
   ```

   Mathematically this gives

   $$
   5\mid H(r,s)-N(r,s)^2.
   $$

4. Subtract the two divisible quantities.

   ```lean
   have h := dvd_sub hH hdiff
   ```

   The resulting dividend is conceptually

   $$
   H-(H-N^2)=N^2.
   $$

5. Normalize the ring expression.

   ```lean
   ring_nf at h
   ```

   This produces

   ```lean
   (5 : ℤ) ∣ goldenNorm p.base ^ 2
   ```

6. Supply primality of the integer 5 with `norm_num` and descend divisibility from the square to its base.

   ```lean
   exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
   ```

   Hence

   $$
   5\mid N(r,s)^2
   \Longrightarrow
   5\mid N(r,s),
   $$

   contradicting `p.five_not_dvd_norm`.

## Lean-specific processing

### `apply p.five_not_dvd_norm`

The field `five_not_dvd_norm` is a negation:

```lean
¬ (5 : ℤ) ∣ goldenNorm p.base
```

Since the current goal is `False`, applying it makes the evidence it would reject,

```lean
(5 : ℤ) ∣ goldenNorm p.base
```

the new goal. This is a standard compact contradiction pattern in Lean.

### `dvd_sub hH hdiff`

`dvd_sub` expresses closure of divisibility under subtraction. Here it combines

```lean
hH    : 5 ∣ H
hdiff : 5 ∣ H - N^2
```

to obtain

```lean
5 ∣ H - (H - N^2).
```

### `ring_nf at h`

The expression generated by `dvd_sub` is not syntactically `N^2`. `ring_nf` performs ring normalization and reduces

$$
H-(H-N^2)=N^2
$$

to canonical form.

Its role here is purely algebraic normalization rather than number-theoretic reasoning.

### `Prime.dvd_of_dvd_pow`

Primality of the integer 5 is constructed as

```lean
(show Prime (5 : ℤ) by norm_num)
```

and

```lean
.dvd_of_dvd_pow hnormSq
```

descends divisibility from a power to its base.

Although the exponent here is 2, the proof uses the generic power API rather than a square-specific lemma.

## Redundancy and duplication

The proof is short and contains little mathematical redundancy.

The block

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
  have h := dvd_sub hH hdiff
  ring_nf at h
  exact h
```

might possibly be shortened with `simpa` or `convert`, for example conceptually

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
  simpa only [...] using dvd_sub hH hdiff
```

but the exact normalization lemma set was not verified. The current `ring_nf` version is therefore robust and readable.

Likewise, `Prime (5 : ℤ)` is likely to occur repeatedly throughout an FLT5 development. If the repetition is substantial, a named lemma for primality of 5 could be shared. Since `norm_num` closes it immediately, however, the abstraction cost may exceed the benefit.

## Optimization candidates

1. **Keep the current proof as the leading option.**

   The chain `hH → hnormSq → norm divisibility → contradiction` mirrors the mathematics directly and balances brevity with readability.

2. **Expose the mod-5 congruence explicitly.**

   `five_dvd_goldenFifthSndFactor_sub_norm_sq` is essentially the congruence

   $$
   H(r,s)\equiv N(r,s)^2\pmod 5.
   $$

   If downstream code repeatedly uses the same congruence, an `Int.ModEq 5 ...` theorem could provide a more semantic API alongside the difference-divisibility form.

3. **A `five_not_dvd_norm_sq` helper.**

   If many later proofs repeatedly derive `5 ∤ N^2` from `5 ∤ N`, a helper wrapping primality could be useful. This theorem uses the fact only once, so no such abstraction is needed locally.

4. **Keep `ring_nf` local.**

   The proof wisely avoids unfolding the quartic or norm definitions and applies `ring_nf` only to the small expression created by `dvd_sub`. Preserving that abstraction boundary is preferable to broad `simp` or `ring_nf` normalization.

## Required Mathlib imports and import optimization candidates

The standalone source uses `import Mathlib`.

For this theorem alone, the required Mathlib functionality is approximately:

- integer divisibility and `dvd_sub`
- prime elements and `Prime.dvd_of_dvd_pow`
- the `ring_nf` normalization tactic
- the `norm_num` tactic
- basic propositional tactic/term syntax

The actual project module must additionally import enough project code to provide:

- `GoldenZeroSectorDescentPacket`
- `goldenFifthSndFactor`
- `goldenNorm`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`

Because `ring_nf` and `norm_num` are used, their corresponding Mathlib tactic modules must be available. The exact minimal import set was not verified because no Lean build is performed in this task, so reductions from `import Mathlib` remain optimization candidates rather than confirmed replacements.

## Comparator challenge suitability

**Suitable. This is a good small challenge combining divisibility congruence with prime descent.**

Its essential stages are:

1. accept `5 ∣ H` as the contradiction hypothesis;
2. combine it with `5 ∣ H - N^2` to obtain `5 ∣ N^2`;
3. normalize the subtraction expression;
4. use `Prime.dvd_of_dvd_pow` to obtain `5 ∣ N` and contradict the packet invariant.

This is more informative than a pure `ring` exercise because it combines closure of divisibility, prime APIs, ring normalization, and goal transformation through a negated invariant.

Possible difficulty variants include:

- a standard version allowing `ring_nf`;
- a version forbidding `ring_nf` and requiring explicit equality manipulation;
- an exploration version in which the name `Prime.dvd_of_dvd_pow` is not supplied.

## Next declaration to read

The next declaration in the same namespace is

```lean
theorem five_not_dvd_D (p : GoldenZeroSectorDescentPacket) :
    ¬ 5 ∣ p.D := by
  intro hD
  apply p.five_not_dvd_H
  rw [p.H_eq]
  exact dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
```

It combines the present result

$$
5\nmid H(r,s)
$$

with the packet invariant

$$
H(r,s)=D^5
$$

to derive

$$
5\nmid D.
$$

Thus the 5-adic cleanliness propagates as

$$
N(r,s)
\longrightarrow
H(r,s)
\longrightarrow
D.
$$

After that, the proof proceeds through `coprime_s_H`, `coprime_D_s`, and `lift_relPrime_conj`, culminating in relative primality for the re-entry element.
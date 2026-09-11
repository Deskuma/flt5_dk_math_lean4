# 0382 `five_not_dvd_D`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this theorem proves that the fifth-power root `D` stored in the packet is not divisible by 5.

## Lean code

```lean
theorem five_not_dvd_D (p : GoldenZeroSectorDescentPacket) :
    ¬ 5 ∣ p.D := by
  intro hD
  apply p.five_not_dvd_H
  rw [p.H_eq]
  exact dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
```

## Lean type

With the namespace made explicit, the type is conceptually

```lean
GoldenZeroSectorDescentPacket.five_not_dvd_D :
  (p : GoldenZeroSectorDescentPacket) → ¬ 5 ∣ p.D
```

Since `p.D : ℕ`, the conclusion

```lean
¬ 5 ∣ p.D
```

is a non-divisibility statement in `ℕ`.

By contrast, the immediately preceding theorem used directly here,

```lean
p.five_not_dvd_H :
  ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

is a non-divisibility statement in `ℤ`. Therefore the proof uses

```lean
Int.natCast_dvd.mpr hD
```

to transport divisibility from naturals to integers.

## Mathematical statement

Write `base = (r,s)` and set

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s).
$$

The packet stores the identity

$$
H(r,s)=D^5
$$

through its field `H_eq`.

The preceding theorem 0381 `five_not_dvd_H` has already established

$$
5\nmid H(r,s).
$$

The present theorem combines these two facts to conclude

$$
5\nmid D.
$$

Indeed, if one assumes instead that

$$
5\mid D,
$$

then automatically

$$
5\mid D^5.
$$

Since $H(r,s)=D^5$, it follows that

$$
5\mid H(r,s),
$$

contradicting theorem 0381. Hence

$$
5\nmid D.
$$

## Role in the full proof

This theorem transports the 5-adic clean property of the zero-sector descent packet from the quartic factor down to its fifth root `D`.

The chain immediately preceding it is

$$
5\nmid N(r,s)
\Longrightarrow
5\nmid H(r,s)
\Longrightarrow
5\nmid D,
$$

where $N(r,s)=\operatorname{goldenNorm}(r,s)$.

The non-divisibility of `D` is used directly later in `lift_relPrime_conj`. In the canonical source, that proof constructs

```lean
have hD5 : Nat.Coprime (p.D ^ 5) 5 :=
  Nat.Coprime.pow_left 5
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      p.five_not_dvd_D).symm
```

which gives

$$
\gcd(D^5,5)=1.
$$

That fact is then combined with coprimality between $D^5$ and the remaining $|s|^4$ factor in order to show that the quadratic lift and its conjugate have no nonunit common divisor. This feeds the fifth-power re-entry argument and the elimination of nonzero unit sectors.

Thus `five_not_dvd_D` is a small but essential relay point in the coprimality chain after re-entry.

## Direct dependencies

The direct project-level dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.H_eq`
- `GoldenZeroSectorDescentPacket.five_not_dvd_H`
- `goldenFifthSndFactor`

The main Lean / Mathlib features used directly are:

- `Int.natCast_dvd`
- `dvd_pow`
- `decide`
- `rw`
- `intro`
- `apply`
- `exact`

The theorem does not directly depend on 0380 `H_pos` or 0379 `snd_natAbs_eq`. Mathematically it closes using only `H_eq` and `five_not_dvd_H`.

## Proof flow

1. Assume the negation of the goal, namely that the natural number `D` is divisible by 5.

   ```lean
   intro hD
   ```

   Thus

   $$
   5\mid D.
   $$

2. Use theorem 0381 as the contradiction target.

   ```lean
   apply p.five_not_dvd_H
   ```

   The new goal becomes

   ```lean
   (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
   ```

3. Rewrite the quartic factor using the packet identity.

   ```lean
   rw [p.H_eq]
   ```

   Conceptually the goal is now

   $$
   5\mid D^5,
   $$

   with `D` cast into `ℤ`.

4. Transport the hypothesis `hD : 5 ∣ p.D` from naturals to integers.

   ```lean
   Int.natCast_dvd.mpr hD
   ```

   This yields

   ```lean
   (5 : ℤ) ∣ (p.D : ℤ)
   ```

5. Lift divisibility to the fifth power using `dvd_pow`.

   ```lean
   dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
   ```

   Therefore

   $$
   5\mid (D:\mathbb Z)^5,
   $$

   contradicting `p.five_not_dvd_H`.

## Lean-specific details

### `apply p.five_not_dvd_H`

The type of `p.five_not_dvd_H` is the negated proposition

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

After `intro hD`, the current goal is `False`. Applying this negated proposition makes Lean ask for

```lean
(5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

as the new goal.

This is the same standard contradiction style used in theorem 0381.

### `rw [p.H_eq]`

`H_eq` is a field of the packet and stores

```lean
goldenFifthSndFactor p.base.fst p.base.snd = (p.D : ℤ) ^ 5
```

Therefore no unfolding of the quartic polynomial is needed. A single rewrite crosses the abstraction boundary from the quartic factor to fifth-power divisibility.

### `Int.natCast_dvd.mpr hD`

The hypothesis `hD` lives in `ℕ`, while the right-hand side of `p.H_eq` lives in `ℤ`.

`Int.natCast_dvd` bridges divisibility before and after casting naturals to integers. The `.mpr` direction transports the natural-number statement to the integer statement required by the rewritten goal.

### `dvd_pow`

`dvd_pow` expresses the closure property

$$
a\mid b \Longrightarrow a\mid b^n.
$$

Here `a = 5`, `b = (p.D : ℤ)`, and `n = 5`.

Its second argument

```lean
(by decide : 5 ≠ 0)
```

supplies a proof that the exponent is nonzero. Since this is a closed numeral proposition, `decide` proves it immediately.

## Redundancy and duplication

The proof is only five lines long and contains essentially no mathematical duplication.

If the larger FLT5 development repeatedly needs facts of the form “if 5 divides `x`, then 5 divides `x^5`” or conversely “if 5 does not divide `x^5`, then 5 does not divide `x`”, a dedicated helper theorem could centralize this pattern.

For this particular declaration, however, the combination of `rw [p.H_eq]`, `Int.natCast_dvd.mpr`, and `dvd_pow` is already direct enough that introducing a project-specific helper would probably add more dependency surface than value.

The `Nat`/`Int` conversion is also confined to one expression, which makes the type boundary easy to inspect.

## Optimization candidates

1. **Keep the current proof**

   The proof order closely follows the mathematics and is already very short.

2. **Generalize the clean-root principle**

   One could expose a packet-independent lemma for a prime `q` and positive exponent `n` expressing

   $$
   q\nmid x^n \Longrightarrow q\nmid x.
   $$

   If Mathlib's existing prime-divisibility API already covers downstream uses cleanly, adding a project-specific wrapper is unnecessary.

3. **Unify the `Nat`/`Int` boundary**

   Storing `D` as an integer would remove this cast, but `D : ℕ` is useful elsewhere for positivity, roots, and natural-number reasoning. A single cast here is not a sufficient reason to redesign the packet.

4. **Add a named coprimality corollary**

   If downstream code repeatedly constructs `Nat.Coprime p.D 5`, a theorem such as

   ```lean
   theorem coprime_D_five ... : Nat.Coprime p.D 5 := ...
   ```

   could make `five_not_dvd_D` the primitive divisibility-level API while exposing a coprimality-level API for later proofs.

## Required Mathlib imports and import optimization

The standalone canonical source uses `import Mathlib`.

For this theorem alone, the Mathlib-side requirements are approximately:

- natural and integer divisibility
- `Int.natCast_dvd`
- `dvd_pow`
- decidable proof of a closed numeral proposition via `decide`
- basic proof commands such as `rw`, `intro`, `apply`, and `exact`

This theorem itself does not invoke heavier tactics such as `ring`, `ring_nf`, `norm_num`, or `omega`.

Therefore a much smaller import set than the whole `Mathlib` umbrella is likely sufficient for this declaration in isolation. Project imports must additionally provide `GoldenZeroSectorDescentPacket`, `goldenFifthSndFactor`, and `five_not_dvd_H`.

Because no Lean build is performed in this task, the exact minimal Mathlib import set has not been verified. Specific module names are therefore left as optimization candidates rather than asserted as confirmed minima.

## Comparator challenge suitability

**Suitable. This is a compact challenge involving a Nat/Int cast and power divisibility.**

The essential steps are:

1. receive a `Nat` hypothesis `5 ∣ D`;
2. rewrite with `H = (D : ℤ)^5`;
3. transport divisibility across the cast and lift it to the fifth power;
4. contradict `5 ∤ H`.

For Comparator, this tests more than algebraic normalization. It exercises:

- namespace field projection
- contradiction through a negated divisibility proposition
- `Nat → Int` divisibility transport
- power divisibility

A minimal challenge version could omit the full packet and retain only assumptions such as

```lean
(hH : H = (D : ℤ) ^ 5)
(hnot : ¬ (5 : ℤ) ∣ H)
```

so that API selection rather than project-specific context becomes the main difficulty.

## Next declaration to read

The next declaration is 0383 `coprime_s_H`, also a `theorem`:

```lean
theorem coprime_s_H (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs :=
  coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.base.fst p.base.snd p.coprime_coords
```

It extracts from the primitive-coordinate condition

$$
\gcd(|r|,|s|)=1
$$

the stronger factor coprimality

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

After 0382 has transported the 5-adic clean property all the way to `D`, declaration 0383 begins the next stage: assembling the coprimality chain among `s`, `H`, and `D`.
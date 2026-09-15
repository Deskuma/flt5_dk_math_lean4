# 0384 `coprime_D_s`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma proves that the packet's fifth root `D` is coprime to the absolute value of the second coordinate `s` of its base.

## Lean code

```lean
theorem coprime_D_s (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.D p.base.snd.natAbs := by
  have hcop := p.coprime_s_H
  have hHAbs :
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
    rw [p.H_eq, Int.natAbs_pow]
    simp
  rw [hHAbs] at hcop
  exact ((Nat.coprime_pow_right_iff (by decide : 0 < 5)
    p.base.snd.natAbs p.D).mp hcop).symm
```

## Lean type

After expanding the namespace, its conceptual type is

```lean
GoldenZeroSectorDescentPacket.coprime_D_s :
  (p : GoldenZeroSectorDescentPacket) →
    Nat.Coprime p.D p.base.snd.natAbs
```

Here `p.D : ℕ` is the fifth root stored by the packet, while `p.base.snd : ℤ` is the second coordinate of the golden integer `base`. Since `Nat.Coprime` is a relation on natural numbers, the signed coordinate is transferred to `ℕ` by `Int.natAbs`.

## Mathematical statement

Write `p.base = (r,s)` and set

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s).
$$

The preceding theorem 0383 `coprime_s_H` gives

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

The packet field `H_eq` records

$$
H(r,s)=D^5.
$$

Since `D` is a natural number,

$$
|H(r,s)|=D^5,
$$

and therefore

$$
\gcd(|s|,D^5)=1.
$$

For the positive exponent 5,

$$
\gcd(a,b^5)=1
\Longleftrightarrow
\gcd(a,b)=1,
$$

so the theorem concludes

$$
\gcd(D,|s|)=1.
$$

## Role in the overall proof

This theorem is the bridge in the zero-sector descent coprimality chain that descends coprimality from the quartic factor to its fifth root.

The preceding step established

$$
\gcd(|r|,|s|)=1
\Longrightarrow
\gcd(|s|,|H(r,s)|)=1.
$$

The present theorem combines that result with

$$
H(r,s)=D^5
$$

to obtain

$$
\gcd(D,|s|)=1.
$$

This fact is used immediately by `lift_relPrime_conj`. There, if a golden integer `z` divides both the quadratic lift and its conjugate, its norm is shown to divide both `D^5` and `5|s|^4`. The present theorem, together with 0382 `five_not_dvd_D`, makes `D^5` coprime to `5|s|^4`. Hence the norm of the common divisor is forced to be 1, which makes `z` a unit.

Thus 0384 certifies that the fifth root `D` is arithmetically separated from the visible coordinate `s`, providing a principal input to relative primality of the golden lift and its conjugate.

## Direct dependencies

The directly used project declarations are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.coprime_s_H`
- `GoldenZeroSectorDescentPacket.H_eq`
- `goldenFifthSndFactor`

The main Mathlib APIs used directly are:

- `Int.natAbs_pow`
- `Nat.coprime_pow_right_iff`
- symmetry of `Nat.Coprime`
- simplification rules reducing the `natAbs` of an integer cast of a natural number

0382 `five_not_dvd_D` is not a direct dependency of this theorem itself. It is combined with `coprime_D_s` in the following `lift_relPrime_conj` theorem.

## Proof / construction flow

1. Retrieve the packet-level result from 0383:

   ```lean
   have hcop := p.coprime_s_H
   ```

   At this point,

   ```lean
   hcop : Nat.Coprime p.base.snd.natAbs
     (goldenFifthSndFactor p.base.fst p.base.snd).natAbs
   ```

2. Convert the absolute value of the quartic factor into a fifth power using `H_eq`:

   ```lean
   have hHAbs :
       (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
     rw [p.H_eq, Int.natAbs_pow]
     simp
   ```

   The rewrite by `p.H_eq` replaces `H(r,s)` with `(p.D : ℤ)^5`. `Int.natAbs_pow` moves the absolute value through the power, and the final `simp` reduces the `natAbs` of the natural-number cast back to `p.D`.

3. Rewrite the quartic factor inside `hcop`:

   ```lean
   rw [hHAbs] at hcop
   ```

   Hence

   ```lean
   hcop : Nat.Coprime p.base.snd.natAbs (p.D ^ 5)
   ```

4. Remove the fifth power from the right side by `Nat.coprime_pow_right_iff`:

   ```lean
   (Nat.coprime_pow_right_iff (by decide : 0 < 5)
     p.base.snd.natAbs p.D).mp hcop
   ```

   This produces

   ```lean
   Nat.Coprime p.base.snd.natAbs p.D
   ```

5. The public theorem uses the opposite argument order, so `.symm` yields

   ```lean
   Nat.Coprime p.D p.base.snd.natAbs
   ```

## Lean-specific processing

### `Int.natAbs_pow`

`H_eq` is an equality over integers,

```lean
p.H_eq :
  goldenFifthSndFactor p.base.fst p.base.snd = (p.D : ℤ) ^ 5
```

whereas `coprime_s_H` is stated over naturals after applying `natAbs`. `Int.natAbs_pow` bridges this type boundary.

### Cast simplification with `simp`

After rewriting with `Int.natAbs_pow`, the expression is conceptually

```lean
((p.D : ℤ).natAbs) ^ 5.
```

Because `p.D : ℕ`, `simp` reduces `(p.D : ℤ).natAbs` to `p.D`.

### `Nat.coprime_pow_right_iff`

This is the central API of the proof. The positive-exponent hypothesis is supplied by

```lean
(by decide : 0 < 5)
```

and the theorem converts `Coprime a (b^5)` into `Coprime a b`.

### `.symm`

The inherited orientation from 0383 is `Coprime |s| D`, whereas the packet API exported here is `Coprime D |s|`. They are mathematically equivalent, and symmetry adjusts the orientation to the form used by later code.

## Redundancy and duplication

There is little local redundancy. The proof performs exactly one descent from coprimality with a fifth power to coprimality with its base.

The local fact `hHAbs`, however, is a derived packet invariant that may be useful elsewhere. If the same `natAbs` conversion recurs, one could expose a packet-level helper such as

```lean
theorem H_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := ...
```

If this conversion is only needed here, keeping it as a local `have` avoids unnecessary API growth.

## Optimization candidates

1. **Promote `H_natAbs_eq` only if it is reused**

   Repeated occurrences would justify a named lemma; a one-off use favors the current local proof.

2. **Keep the current orientation**

   Although 0383 places `s` on the left, 0384 places `D` on the left. This is useful immediately afterward, where the code applies `Nat.Coprime.pow_left 5 p.coprime_D_s`.

3. **Keep `by decide : 0 < 5`**

   The exponent is a fixed numeral, so `decide` is lightweight and stable; a separate helper theorem would add little value.

4. **Avoid polynomial expansion**

   The proof correctly works through `H_eq` and the prior coprimality API. Re-expanding the quartic polynomial would duplicate arithmetic already abstracted elsewhere.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`.

At the surface level, this theorem uses mainly:

- `Nat.Coprime`
- `Nat.coprime_pow_right_iff`
- `Int.natAbs`
- `Int.natAbs_pow`
- simplification of natural-number casts into integers
- `decide`

A narrower Mathlib import set is likely possible. However, this task does not run a Lean build, so the exact minimal module set has not been verified and no specific minimal import list is asserted as fact.

On the project side, the imported module must expose `GoldenZeroSectorDescentPacket`, `coprime_s_H`, `H_eq`, and `goldenFifthSndFactor`.

## Comparator challenge suitability

**Yes. It is a slightly richer micro challenge than 0383.**

A reduced challenge could provide assumptions such as

```lean
hcop : Nat.Coprime sAbs HAbs
hH : HAbs = D ^ 5
```

with target

```lean
Nat.Coprime D sAbs.
```

This tests whether a model can:

- rewrite by a fifth-power identity,
- find `Nat.coprime_pow_right_iff`,
- supply the positive exponent condition,
- repair the final orientation with symmetry.

Using the actual source adds `Int.natAbs_pow` and cast simplification, so it also tests API selection across the `Int`/`Nat` boundary.

The mathematical difficulty is still modest; its value as a Comparator challenge lies mainly in correct theorem discovery and composition.

## Next declaration to read

The next declaration is 0385 `lift_relPrime_conj`, again a `theorem`.

```lean
theorem lift_relPrime_conj (p : GoldenZeroSectorDescentPacket) :
    GoldenRelPrime (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) := by
  intro z hzAlpha hzConj
  ...
```

It combines the present result

$$
\gcd(D,|s|)=1
$$

with 0382

$$
5\nmid D
$$

to show that every common divisor of the quadratic lift and its conjugate is a unit.

Thus 0384 completes the natural-number coprimality preparation, and 0385 begins the transfer of that information into `GoldenRelPrime` inside the golden integer ring.
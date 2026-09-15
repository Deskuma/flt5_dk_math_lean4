# 0390 `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`

## Declaration kind

`theorem`

This theorem lives in the `GoldenZeroSectorDescentPacket` namespace and proves that the second coordinate of the fifth root `gamma` is strictly positive.

## Lean code

```lean
theorem fifthRoot_snd_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hH := p.fifthRoot_H_pos gamma hroot
  nlinarith
```

## Lean type

Conceptually, the theorem has the following type.

```lean
GoldenZeroSectorDescentPacket.fifthRoot_snd_pos :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  0 < gamma.snd
```

The inputs are a descent packet `p`, a golden integer `gamma`, and a proof `hroot` that the quadratic lift is equal to `gamma^5`. The output is strict positivity of the integer second coordinate `gamma.snd : ℤ`.

## Mathematical statement

Write `gamma=(a,b)` and `p.base=(r,s)`.

By 0388 `fifthRoot_snd_factor_eq`,

$$
s^2 = 5bH(a,b),
$$

where

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

The packet invariant `snd_ne_zero` gives

$$
s\neq0,
$$

hence

$$
s^2>0.
$$

The immediately preceding theorem 0389 `fifthRoot_H_pos` gives

$$
H(a,b)>0.
$$

Therefore

$$
0<s^2=5bH(a,b).
$$

Since $5>0$ and $H(a,b)>0$, it follows that

$$
b>0.
$$

This is exactly the Lean conclusion `0 < gamma.snd`.

## Role in the overall proof

0387 `exists_lift_eq_fifthPower` converted the quadratic lift into a pure fifth power,

$$
T(r,s)=\gamma^5.
$$

0388 projected this identity to the second coordinate and obtained

$$
s^2=5bH(a,b).
$$

0389 then established the sign of the quartic factor,

$$
H(a,b)>0.
$$

0390 determines the sign of the remaining factor $b=\gamma_{\mathrm{snd}}$. This lets the second coordinate of the fifth root be treated not merely as an arbitrary integer, but as a positive quantity.

The subsequent descent needs coprimality of `gamma.fst.natAbs` and `gamma.snd.natAbs`, five-adic splitting of the second coordinate, reconstruction of a new descent packet, and finally a strict decrease of a natural-number measure. Once `gamma.snd>0` is known, one may remove the absolute value via

$$
|\gamma_{\mathrm{snd}}|=\gamma_{\mathrm{snd}},
$$

so this theorem is an important order-theoretic bridge from factorization in the golden integer ring back to the natural-number data used by well-founded descent.

## Direct dependencies

The main declarations used directly are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.snd_ne_zero`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `sq_pos_of_ne_zero`
- `nlinarith`

The two principal inputs are the identity returned by

```lean
p.fifthRoot_snd_factor_eq gamma hroot
```

namely

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

and the strict positivity returned by 0389,

```lean
0 < goldenFifthSndFactor gamma.fst gamma.snd.
```

## Proof flow

1. Obtain the second-coordinate product identity from 0388.

   ```lean
   have hEq := p.fifthRoot_snd_factor_eq gamma hroot
   ```

2. Use nonzeroness of the packet's second coordinate to obtain positivity of its square.

   ```lean
   have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
   ```

3. Obtain strict positivity of the quartic factor from 0389.

   ```lean
   have hH := p.fifthRoot_H_pos gamma hroot
   ```

4. Supply the three facts

   $$
   s^2=5bH,
   \qquad
   s^2>0,
   \qquad
   H>0
   $$

   to `nlinarith`.

5. If $b\le0$, then the right-hand side $5bH\le0$, contradicting positivity of the left-hand side. Therefore `0 < gamma.snd`.

   ```lean
   nlinarith
   ```

## Lean-specific processing

### `sq_pos_of_ne_zero`

`p.snd_ne_zero` gives `p.base.snd ≠ 0`. Lean extracts positivity of the square explicitly via

```lean
sq_pos_of_ne_zero p.snd_ne_zero
```

rather than relying on an implicit mathematical convention.

### `nlinarith`

The mathematical content is a sign argument, but the identity

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

contains products, so the proof uses the nonlinear arithmetic tactic `nlinarith` rather than `linarith`.

No expansion of the quartic polynomial is required here. `goldenFifthSndFactor gamma.fst gamma.snd` can be treated as a single integer expression; its positivity `hH`, together with `hEq` and `hsSq`, is enough.

### Reuse of packet APIs

The theorem does not reprove the origin of `s≠0` or nonnegativity/positivity of the quartic factor. It reuses the packet invariant `snd_ne_zero` and theorem 0389, keeping the dependency structure modular.

## Redundancy and duplication

The proof is only four lines long and contains almost no accidental redundancy.

The calls producing `hEq` and `hH` deliberately preserve the staging of the proof. Combining 0388, 0389, and 0390 into a single theorem could reduce line count, but it would lose separately reusable APIs for

- the second-coordinate product identity,
- positivity of the quartic factor,
- positivity of the fifth root's second coordinate.

Thus the current decomposition has clear design value.

The construction

```lean
have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
```

also appeared in 0389. If the same pattern appears repeatedly later, a packet helper such as `p.snd_sq_pos` could remove duplication. The repository evidence inspected here does not establish that there is enough repetition to justify that abstraction yet.

## Optimization candidates

### 1. Structural sign proof

`nlinarith` is concise and robust, but the sign structure could be made more explicit by first proving

$$
0<5H(a,b)
$$

and then extracting `b>0` from positivity of the product $b(5H)$.

A proof using lemmas such as `mul_pos_iff` or `mul_pos` could reduce dependence on nonlinear automation. The exact shortest Lean formulation is unverified because this run does not perform a Lean build.

### 2. Positivity packet for 0388–0390

If downstream code frequently requires both facts simultaneously, an auxiliary theorem returning

```lean
0 < gamma.snd ∧
0 < goldenFifthSndFactor gamma.fst gamma.snd
```

could be useful. It would be better as an additional API rather than a replacement for the current single-purpose lemmas.

### 3. A `natAbs` bridge

If `gamma.snd.natAbs` is repeatedly used as a natural-number descent measure, a helper derived from this theorem that rewrites the absolute value/cast of `gamma.snd` under positivity could centralize later sign-removal steps.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib functionality directly visible in this theorem consists mainly of integer order theory, positivity of squares via `sq_pos_of_ne_zero`, and the nonlinear arithmetic tactic `nlinarith`.

A reduced import set would therefore likely involve the relevant algebra/order modules plus `Mathlib.Tactic.Nlinarith` or a suitable `Mathlib.Tactic` import. However, `GoldenInt`, `GoldenZeroSectorDescentPacket`, and the preceding project theorems may transitively require additional Mathlib modules. Because no Lean build is performed in this run, the exact minimal import set has not been verified.

Thus **the confirmed working import is `Mathlib`; the minimal import remains undetermined**.

## Comparator challenge suitability

**Yes. It is particularly suitable as a small sign-reasoning challenge.**

After removing FLT5-specific definitions, the core can be presented as

```lean
(hEq : s ^ 2 = 5 * b * H)
(hs0 : s ≠ 0)
(hH : 0 < H)
⊢ 0 < b
```

The required ideas are:

1. derive `s^2>0` from `s≠0`,
2. recognize positivity of $5$ and `H`,
3. infer positivity of `b` from the product identity.

A version that permits `nlinarith` mainly tests tactic selection. A second version forbidding `nlinarith` and requiring explicit sign lemmas such as `mul_pos_iff` would test more structural reasoning. Both are useful Comparator variants.

## Next declaration to read

The next declaration is **0391 `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`**, also a `theorem`.

In the Lean source it begins as follows:

```lean
theorem fifthRoot_coprime_coords
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  ...
```

Up through 0390, the sign of the second coordinate of the fifth root has been fixed. 0391 then uses the additional equation `goldenNorm gamma = D` to establish primitive coprimality of the coordinates of

$$
\gamma=(a,b):
$$

$$
\gcd(|a|,|b|)=1.
$$

This is a central condition for reusing `gamma` as the next primitive descent datum.

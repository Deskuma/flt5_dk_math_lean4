# 0389 `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`

## Declaration kind

`theorem`

This theorem lives in the `GoldenZeroSectorDescentPacket` namespace and proves that the quartic factor attached to the fifth root `gamma` is strictly positive.

## Lean code

```lean
theorem fifthRoot_H_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < goldenFifthSndFactor gamma.fst gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hnonneg := goldenFifthSndFactor_nonneg gamma.fst gamma.snd
  have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hEq
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

## Lean type

Conceptually, the type is:

```lean
GoldenZeroSectorDescentPacket.fifthRoot_H_pos :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  0 < goldenFifthSndFactor gamma.fst gamma.snd
```

The inputs are a descent packet `p`, a golden integer `gamma`, and a proof `hroot` that the quadratic lift is `gamma^5`. The output is strict positivity in `ℤ` of the quartic factor associated with `gamma`.

## Mathematical statement

Write `gamma=(a,b)` and `p.base=(r,s)`.

The previous theorem 0388 `fifthRoot_snd_factor_eq` gives

$$
s^2 = 5bH(a,b),
$$

where

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

The packet theorem `snd_ne_zero` gives $s\neq0$, hence

$$
s^2>0.
$$

The general theorem `goldenFifthSndFactor_nonneg` gives

$$
H(a,b)\ge0.
$$

If $H(a,b)=0$, then the product identity becomes

$$
s^2=5b\cdot0=0,
$$

contradicting $s^2>0$. Therefore

$$
H(a,b)\neq0.
$$

Combining nonnegativity with nonzeroness yields

$$
H(a,b)>0.
$$

## Role in the full proof

In 0387 `exists_lift_eq_fifthPower`, the quadratic lift was shown to be an honest fifth power,

$$
T(r,s)=\gamma^5.
$$

Theorem 0388 projected this equality to the second coordinate and returned to integer arithmetic through

$$
s^2=5bH(a,b).
$$

The present theorem extracts the sign of the quartic factor from that identity. This is not merely auxiliary positivity: it is needed immediately by `fifthRoot_snd_pos` to prove $b>0$. Indeed, once

$$
s^2>0,
\qquad
H(a,b)>0,
\qquad
s^2=5bH(a,b)
$$

are known, positivity of $b$ follows.

Later in the descent, `gamma.snd.natAbs` is used as the new visible measure. Establishing the positive sign of the second coordinate removes sign ambiguity and supports the strict-measure comparison. Thus this theorem is an intermediate bridge from algebraic fifth-root existence to the order information required for well-founded descent.

## Direct dependencies

The main declarations used directly are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenFifthSndFactor`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.snd_ne_zero`
- `goldenFifthSndFactor_nonneg`
- `sq_pos_of_ne_zero`
- `lt_of_le_of_ne`
- `Ne.symm`

The central input from 0388 is

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

The general theorem `goldenFifthSndFactor_nonneg` ultimately comes from the diagonal identity

$$
16H(r,s)
 = X^4+10X^2s^2+5s^4,
\qquad X=2r+s,
$$

whose right-hand side is a sum of nonnegative even-power terms.

## Proof flow

1. Obtain the product identity from 0388.

   ```lean
   have hEq := p.fifthRoot_snd_factor_eq gamma hroot
   ```

2. Use nonzeroness of the packet's second coordinate to make its square strictly positive.

   ```lean
   have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
   ```

3. Obtain general nonnegativity of the quartic factor.

   ```lean
   have hnonneg := goldenFifthSndFactor_nonneg gamma.fst gamma.snd
   ```

4. Assume the quartic factor is zero.

   ```lean
   have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
     intro hzero
   ```

5. Rewrite the product identity with that zero value.

   ```lean
   rw [hzero, mul_zero] at hEq
   ```

   This reduces `hEq` essentially to `p.base.snd ^ 2 = 0`.

6. Contradict strict positivity of the square.

   ```lean
   omega
   ```

7. Combine `H ≥ 0` and `H ≠ 0` to conclude `H > 0`.

   ```lean
   exact lt_of_le_of_ne hnonneg (Ne.symm hne)
   ```

## Lean-specific processing

### `sq_pos_of_ne_zero`

Mathematically, $s\neq0\Rightarrow s^2>0$ is immediate. Lean extracts exactly this order fact through `sq_pos_of_ne_zero`.

The proof reuses the packet API `p.snd_ne_zero`, which has already derived nonzeroness from the invariant $s=\pm5t^5$ together with $t>0$.

### `rw [hzero, mul_zero] at hEq`

The proof substitutes `H=0` directly into the product identity and simplifies the right side to zero. No expansion of the quartic polynomial is needed.

### `omega`

Here `omega` is not solving nonlinear polynomial arithmetic. By this point the relevant facts are essentially

```lean
hsSq : 0 < p.base.snd ^ 2
hEq  : p.base.snd ^ 2 = 0
```

so the tactic closes a straightforward integer order contradiction.

### `lt_of_le_of_ne`

The orientation matters. `hnonneg` has type `0 ≤ H`, while `hne` has type `H ≠ 0`. The proof therefore supplies `Ne.symm hne : 0 ≠ H` to obtain `0 < H`.

## Redundancy and duplication

The theorem is short and contains little mathematical duplication. The fact `hsSq` is only used inside the proof of `hne`, so it could be localized there.

If the same pattern of deriving strict positivity from a nonnegative factor and a positive product appears repeatedly, a helper theorem could be introduced. At present, however, the abstraction cost would likely exceed the small amount of duplication.

After rewriting `hEq` by `hzero`, it may also be possible to avoid `omega` and derive the contradiction more directly from `hsSq.ne'`. Whether the resulting equality has exactly the required orientation and normal form has not been checked here because no Lean build is performed in this task.

## Optimization candidates

### 1. Shorter proof of nonzeroness

Conceptually, a shorter form may be possible:

```lean
have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
  intro hzero
  rw [hzero, mul_zero] at hEq
  exact (ne_of_gt hsSq) hEq
```

Depending on the orientation of the resulting equality, `hEq.symm` may be needed. This candidate is unverified.

### 2. Stronger quartic positivity API

The current API provides general nonnegativity of `H`, while the packet-specific theorem upgrades it to strict positivity by excluding zero. If a general classification of the zero locus of `H` were introduced, strict positivity might be derived more structurally. The present contradiction proof is already minimal for the immediate purpose.

### 3. Grouping the order facts

Theorems 0389 `fifthRoot_H_pos` and 0390 `fifthRoot_snd_pos` consecutively establish positivity of the two factors in the product identity. A future descent API could provide a combined theorem such as

```lean
0 < gamma.snd ∧
0 < goldenFifthSndFactor gamma.fst gamma.snd
```

although separate lemmas are more reusable.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

for the entire generated artifact.

This theorem itself mainly needs integer order/algebra facts, positivity of squares, rewriting, and the `omega` tactic. Therefore a substantially smaller import set is likely possible.

Likely ingredients include integer ordered-ring infrastructure together with `Mathlib.Tactic.Omega`, but project-local declarations such as `GoldenInt`, the descent packet, and quartic nonnegativity may transitively require additional Mathlib modules. Because this run does not perform a Lean build, the exact minimal import set has not been verified.

Thus **the confirmed import is `Mathlib`; the minimal import remains unverified**.

## Comparator challenge suitability

**Yes. It is particularly suitable as a small challenge.**

The core can be reduced to the following data:

```lean
hEq : s ^ 2 = 5 * b * H
hs0 : s ≠ 0
hnonneg : 0 ≤ H
⊢ 0 < H
```

The intended reasoning is:

1. obtain `s^2 > 0` from `s ≠ 0`;
2. assume `H = 0`;
3. use the product identity to get `s^2 = 0`;
4. derive a contradiction;
5. combine `H ≥ 0` with `H ≠ 0`.

Both an FLT5-specific challenge retaining the project definitions and a micro challenge over abstract integers are possible. The abstract version is especially appropriate for comparing proof-search behavior independently of domain-specific API discovery.

## Next declaration to read

The next declaration is **0390 `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`**, also a `theorem`.

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

It combines the product identity

$$
s^2=5bH(a,b)
$$

with the present result

$$
H(a,b)>0
$$

to conclude

$$
b>0.
$$

This removes the sign ambiguity from the fifth root's second coordinate and prepares the later strict measure decrease.

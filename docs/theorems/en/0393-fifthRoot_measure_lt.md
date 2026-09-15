# 0393 `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this is the strict-descent lemma showing that the absolute value of the second coordinate of the fifth root `gamma : GoldenInt`, constructed from 0387 onward, is strictly smaller than the absolute value of the second coordinate of the original descent packet.

## Lean code

```lean
theorem fifthRoot_measure_lt
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    gamma.snd.natAbs < p.base.snd.natAbs := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq gamma.fst gamma.snd
  have hbound :
      5 * gamma.snd ^ 4 ≤
        16 * goldenFifthSndFactor gamma.fst gamma.snd := by
    calc
      5 * gamma.snd ^ 4 ≤
          zeroSectorX gamma.fst gamma.snd ^ 4 +
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 +
            5 * gamma.snd ^ 4 := by
        have hx : 0 ≤ zeroSectorX gamma.fst gamma.snd ^ 4 := by positivity
        have hcross : 0 ≤
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 := by
          positivity
        linarith
      _ = 16 * goldenFifthSndFactor gamma.fst gamma.snd := hdiag.symm
  have hn4 : gamma.snd ≤ gamma.snd ^ 4 := by
    have hn0 : 0 ≤ gamma.snd := hn.le
    have hn1 : 0 ≤ gamma.snd - 1 := by omega
    have hquad : 0 ≤ gamma.snd ^ 2 + gamma.snd + 1 := by positivity
    have hnonneg : 0 ≤
        gamma.snd * (gamma.snd - 1) *
          (gamma.snd ^ 2 + gamma.snd + 1) :=
      mul_nonneg (mul_nonneg hn0 hn1) hquad
    nlinarith
  have hn_lt_fiveH :
      gamma.snd < 5 * goldenFifthSndFactor gamma.fst gamma.snd := by
    nlinarith
  apply Int.natAbs_lt_iff_sq_lt.mpr
  nlinarith
```

## Lean type

Conceptually, the theorem has the following type.

```lean
GoldenZeroSectorDescentPacket.fifthRoot_measure_lt :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  gamma.snd.natAbs < p.base.snd.natAbs
```

The inputs are a descent packet `p`, a golden integer `gamma`, and

```lean
hroot : goldenZeroSectorLift p.base = goldenPow gamma 5
```

stating that the quadratic lift is the fifth power of `gamma`. The output is the strict inequality in natural numbers

$$
|\gamma_{\mathrm{snd}}| < |p.base.snd|.
$$

Write

$$
a=\gamma_{\mathrm{fst}},\qquad
b=\gamma_{\mathrm{snd}},\qquad
s=p.base.snd,
$$

and

$$
H(a,b)=\operatorname{goldenFifthSndFactor}(a,b).
$$

## Mathematical statement

From 0388 `fifthRoot_snd_factor_eq` we have

$$
s^2=5bH(a,b).
$$

From 0389 and 0390 we also know

$$
H(a,b)>0,
\qquad
b>0.
$$

The proof then uses the existing diagonalization identity

$$
16H(a,b)
=
X(a,b)^4+10X(a,b)^2b^2+5b^4,
$$

where `X(a,b)` is `zeroSectorX a b`.

Since the first two terms on the right are nonnegative,

$$
5b^4\le16H(a,b).
$$

Because $b$ is a positive integer,

$$
b\le b^4.
$$

Combining these inequalities with $H(a,b)>0$ gives

$$
b<5H(a,b).
$$

Multiplying by $b>0$ yields

$$
b^2<5bH(a,b)=s^2.
$$

For integers,

$$
b^2<s^2
\quad\Longleftrightarrow\quad
|b|<|s|,
$$

so the final conclusion is

$$
|b|<|s|.
$$

## Role in the full proof

This theorem supplies the **well-founded strict decrease** at the core of the zero-sector descent.

In 0387 the development extracts a fifth root

$$
T(r,s)=\gamma^5.
$$

Then 0388–0392 recover the invariants needed for the next generation of descent data:

$$
s^2=5bH(a,b),
$$

$$
H(a,b)>0,
$$

$$
b>0,
$$

$$
\gcd(|a|,|b|)=1,
$$

$$
5\nmid H(a,b).
$$

Preserving invariants alone is not enough for infinite descent. One must also prove that the reconstructed next packet is **strictly smaller** than the current one.

0393 measures the size by

```lean
gamma.snd.natAbs
```

and proves

```lean
gamma.snd.natAbs < p.base.snd.natAbs
```

so that when the fifth root is reused as the base of the next packet, the natural-number-valued measure genuinely decreases.

This is the decisive theorem that justifies the later recursive packet construction and strong/well-founded descent.

## Direct dependencies

The main direct dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenFifthSndFactor`
- `zeroSectorX`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `sixteen_mul_goldenFifthSndFactor_eq`
- `Int.natAbs_lt_iff_sq_lt`
- `mul_nonneg`
- `positivity`
- `linarith`
- `nlinarith`
- `omega`

The main algebraic engine is the existing identity

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  ...
```

which gives an explicit positive lower bound for the quartic factor.

## Proof flow

1. Obtain from 0390

   ```lean
   hn : 0 < gamma.snd
   ```

2. Obtain from 0389

   ```lean
   hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd
   ```

3. Obtain the product identity from 0388:

   ```lean
   hEq : p.base.snd ^ 2 =
     5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
   ```

4. Retrieve the diagonalization identity `sixteen_mul_goldenFifthSndFactor_eq`.

5. Use `positivity` to prove

   $$
   X^4\ge0,
   \qquad
   10X^2b^2\ge0,
   $$

   then use `linarith` to deduce

   $$
   5b^4\le16H.
   $$

6. From $b>0$, use `omega` to get $b\ge1$, and build

   $$
   b(b-1)(b^2+b+1)\ge0.
   $$

   Since this product equals

   $$
   b^4-b,
   $$

   `nlinarith` proves

   $$
   b\le b^4.
   $$

7. From $5b^4\le16H$, $b\le b^4$, and $H>0$, use `nlinarith` to derive

   $$
   b<5H.
   $$

8. Convert the final goal

   ```lean
   gamma.snd.natAbs < p.base.snd.natAbs
   ```

   into a comparison of integer squares via

   ```lean
   Int.natAbs_lt_iff_sq_lt.mpr
   ```

9. Finally, use $b>0$, $b<5H$, and $s^2=5bH$ with `nlinarith` to prove

   $$
   b^2<s^2.
   $$

## Lean-specific processing

### Nonnegativity through `positivity`

When extracting the lower bound from the diagonal identity, the proof writes

```lean
have hx : 0 ≤ zeroSectorX ... ^ 4 := by positivity
have hcross : 0 ≤ 10 * zeroSectorX ... ^ 2 * gamma.snd ^ 2 := by
  positivity
```

Mathematically these facts are immediate from even powers. Lean makes the nonnegativity explicit with the tactic and then hands the inequalities to `linarith`.

### Constructing `b ≤ b^4` by factorization

For an integer $b>0$ one has $b\ge1$. However, nonlinear arithmetic does not necessarily exploit integrality from the strict inequality alone in the desired way, so the proof explicitly obtains

```lean
have hn1 : 0 ≤ gamma.snd - 1 := by omega
```

and then constructs the nonnegative expression

```lean
gamma.snd * (gamma.snd - 1) *
  (gamma.snd ^ 2 + gamma.snd + 1)
```

corresponding to

$$
b(b-1)(b^2+b+1)=b^4-b.
$$

This gives `nlinarith` exactly the polynomial inequality needed for $b\le b^4$.

### Division of labor between `linarith` and `nlinarith`

The first bound in `hbound` is a linear combination once nonnegativity of the extra terms has been supplied, so `linarith` is sufficient.

By contrast, `hn4` and the final square comparison involve products and powers, hence `nlinarith` is used.

### `Int.natAbs_lt_iff_sq_lt`

The final goal is a comparison of natural-number absolute values, while all important algebraic identities live in `ℤ`. The proof therefore uses

```lean
apply Int.natAbs_lt_iff_sq_lt.mpr
```

so that the `natAbs` comparison can be discharged by proving a square inequality over the integers.

This avoids repeated casts and lets the proof remain in the integer ring until the final step.

## Redundancy and duplication

The theorem is a substantive part of the strict descent and is longer than a simple API wrapper. Still, some local pieces could be factored out.

### 1. Positive-integer inequality `x ≤ x^4`

```lean
have hn4 : gamma.snd ≤ gamma.snd ^ 4 := by
  ...
```

is not specific to FLT5. If similar power comparisons occur elsewhere, it could be moved into a general helper lemma.

### 2. Quartic lower bound from diagonalization

The inequality

```lean
5 * b ^ 4 ≤ 16 * H(a,b)
```

is a direct corollary of `sixteen_mul_goldenFifthSndFactor_eq`. If it is used elsewhere in the zero-sector development, it is a natural candidate for a dedicated API theorem.

### 3. Local positivity facts

The explicit `hx` and `hcross` declarations could be compressed by using `positivity` directly inside the calculation. The current form, however, makes the mathematical reason for the lower bound clearer, so shorter code would not automatically be better code.

## Optimization candidates

### 1. Add a lower-bound helper

A general corollary

$$
5s^4\le16H(r,s)
$$

of the diagonalization theorem would hide the longest local block in 0393 and separate the algebraic identity from the descent argument more cleanly.

### 2. Reuse a positive-integer power monotonicity lemma

If Mathlib already contains a lemma matching this exact integer situation, the hand-built proof using

```lean
b * (b - 1) * (b^2 + b + 1) ≥ 0
```

could potentially be replaced.

No exact replacement lemma name is asserted here: this run does not perform a Lean build or a dedicated minimal-API search, so this remains an optimization candidate rather than a verified refactor.

### 3. Abstract the measure inequality

The mathematical inputs are essentially

$$
s^2=5bH,
\qquad
b>0,
\qquad
H>0,
\qquad
5b^4\le16H.
$$

One could therefore extract a golden-integer-independent inequality lemma and make 0393 an application of it. That would improve reuse and make the logical core of the descent especially clear.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib functionality used directly by 0393 is mainly:

- integer order and powers,
- `Int.natAbs_lt_iff_sq_lt`,
- `mul_nonneg`,
- `positivity`,
- `linarith`,
- `nlinarith`,
- `omega`.

`GoldenZeroSectorDescentPacket`, `goldenFifthSndFactor`, `zeroSectorX`, the diagonalization identity, and 0388–0390 are project-local preceding declarations.

In principle the import could likely be reduced from all of `Mathlib` to the required integer/order/power modules plus the tactic modules.

However, because no Lean build is run in this task, the **exact minimal import set is not verified**.

## Comparator challenge suitability

**Highly suitable.**

Unlike a short API wrapper, 0393 combines several previously established invariants with quartic diagonalization to produce the well-founded decrease. It is therefore a substantive proof challenge.

A challenge could provide

```lean
hroot
p.fifthRoot_snd_factor_eq gamma hroot
p.fifthRoot_H_pos gamma hroot
p.fifthRoot_snd_pos gamma hroot
sixteen_mul_goldenFifthSndFactor_eq gamma.fst gamma.snd
```

and ask for

```lean
gamma.snd.natAbs < p.base.snd.natAbs
```

Useful evaluation points are:

1. Can the solver extract $5b^4\le16H$ from the diagonal identity?
2. Can it safely obtain $b\le b^4$ from positivity and integrality?
3. Can it derive $b<5H$ and then $b^2<s^2$?
4. Can it correctly return to the absolute-value measure via `Int.natAbs_lt_iff_sq_lt`?
5. Can it assign appropriate roles to `linarith`, `nlinarith`, `omega`, and `positivity`?

Because the theorem connects preserved algebraic invariants to a genuinely decreasing well-founded measure, it is particularly good for testing understanding of the FLT5 descent rather than mere tactic imitation.

## Next declaration to read

The next declaration is **0394 `GoldenZeroSectorDescentPacket.fifthRoot_power_split`**, also a `theorem`.

In the source it immediately follows 0393 and begins as follows:

```lean
theorem fifthRoot_power_split
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ∃ u v : ℕ,
      0 < u ∧ 0 < v ∧
      ...
```

Where 0393 proves that the recursive datum **gets smaller**, 0394 splits the fifth-root-side product

$$
b\,H(a,b)
$$

using coprimality and the 5-adic conditions, recovering the power shape needed to build the next descent packet.

Thus 0393 supplies strict decrease, while 0394 restores the recursive algebraic shape; together they form the essential recursive step of the strict infinite descent.

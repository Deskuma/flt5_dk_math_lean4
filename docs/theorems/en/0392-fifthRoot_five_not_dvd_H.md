# 0392 `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this theorem recovers the fact that the quartic factor attached to the fifth root `gamma : GoldenInt`

```lean
goldenFifthSndFactor gamma.fst gamma.snd
```

is not divisible by 5.

## Lean code

```lean
theorem fifthRoot_five_not_dvd_H
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  have hnormFive : (5 : ℤ) ∣ goldenNorm gamma :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  rw [hnorm] at hnormFive
  exact p.five_not_dvd_D (by exact_mod_cast hnormFive)
```

## Lean type

Conceptually, the declaration has type

```lean
GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenNorm gamma = (p.D : ℤ) →
  ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

The inputs are a descent packet `p`, a golden integer `gamma`, and the norm identification

```lean
hnorm : goldenNorm gamma = (p.D : ℤ)
```

for the fifth root. The output is the integer divisibility statement

$$
5 \nmid H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

Here

$$
H(a,b)
= a^4+2a^3b+4a^2b^2+3ab^3+b^4
$$

is `goldenFifthSndFactor a b`.

## Mathematical statement

Write `gamma=(a,b)`. The earlier theorem

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
```

states

$$
5 \mid H(a,b)-N(a,b)^2.
$$

Assume, toward a contradiction, that

$$
5\mid H(a,b).
$$

Subtracting the two divisible quantities gives

$$
5\mid N(a,b)^2.
$$

Since 5 is prime,

$$
5\mid N(a,b).
$$

The hypothesis `hnorm` identifies

$$
N(a,b)=D,
$$

so

$$
5\mid D.
$$

This contradicts 0382 `GoldenZeroSectorDescentPacket.five_not_dvd_D`, which provides

$$
5\nmid D.
$$

Therefore

$$
5\nmid H(a,b).
$$

## Role in the full proof

0387 `exists_lift_eq_fifthPower` turned the original quadratic lift into a genuine fifth power,

$$
T(r,s)=\gamma^5,
\qquad
N(\gamma)=D.
$$

Then 0388–0391 successively recovered, for the fifth root `gamma=(a,b)`,

$$
s^2=5bH(a,b),
$$

$$
H(a,b)>0,
$$

$$
b>0,
$$

and

$$
\gcd(|a|,|b|)=1.
$$

0392 restores one more invariant that the source packet already possessed:

$$
5\nmid H.
$$

This is not merely a local cleanup fact. The later strict-descent argument needs the product structure involving the fifth root's second coordinate and quartic factor to split cleanly at the prime 5. In particular, the 5-adic mass must not migrate into `H(a,b)`.

Thus 0392 proves **closure of the 5-adic invariant under passage to the fifth root**, which is necessary if `gamma` is to serve as the next-generation descent datum.

## Direct dependencies

The main direct dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenNorm`
- `goldenFifthSndFactor`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `dvd_sub`
- `Prime.dvd_of_dvd_pow`
- `norm_num`
- `ring_nf`
- `exact_mod_cast`

The central preceding bridge is

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

which expresses the congruence

$$
H(a,b) \equiv N(a,b)^2 \pmod 5.
$$

0392 does not re-expand the quartic polynomial; it consumes this existing mod-5 bridge as an API theorem.

## Proof flow

1. Negate the desired nondivisibility:

   ```lean
   intro hH
   ```

   so that

   $$
   5\mid H(a,b).
   $$

2. Obtain the mod-5 bridge:

   ```lean
   have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
   ```

   giving

   $$
   5\mid H(a,b)-N(a,b)^2.
   $$

3. Combine the two divisibility facts with `dvd_sub hH hdiff`, and normalize the resulting ring expression with `ring_nf`, yielding

   $$
   5\mid N(a,b)^2.
   $$

4. Use primality of 5:

   ```lean
   (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
   ```

   to obtain

   $$
   5\mid N(a,b).
   $$

5. Rewrite with `hnorm`, turning this into

   $$
   5\mid D.
   $$

6. Move the divisibility statement from integers to naturals with `exact_mod_cast` and contradict 0382:

   ```lean
   p.five_not_dvd_D
   ```

## Lean-specific processing

### `dvd_sub hH hdiff`

Mathematically one simply writes

$$
5\mid H,
\qquad
5\mid H-N^2
\Longrightarrow
5\mid N^2.
$$

Lean explicitly composes the divisibility proofs using `dvd_sub`. The result is not syntactically in exactly the desired normal form, so

```lean
ring_nf at h
```

is used to normalize the expression.

### `Prime (5 : ℤ)`

The primality fact used here is a `Prime` statement in the integer ring, not `Nat.Prime`:

```lean
show Prime (5 : ℤ) by norm_num
```

The method

```lean
.dvd_of_dvd_pow
```

then implements

$$
5\mid N^2 \Longrightarrow 5\mid N.
$$

### `rw [hnorm] at hnormFive`

`goldenNorm gamma` is an integer whereas `p.D` is a natural number, so the norm hypothesis already contains a cast:

```lean
goldenNorm gamma = (p.D : ℤ)
```

After rewriting, `hnormFive` has integer form

```lean
(5 : ℤ) ∣ (p.D : ℤ).
```

### `exact_mod_cast`

0382 `five_not_dvd_D` is stated over naturals:

```lean
¬ 5 ∣ p.D
```

Therefore the final step uses

```lean
by exact_mod_cast hnormFive
```

to transport integer divisibility back to natural-number divisibility.

The main Lean difficulty in this theorem is therefore not the underlying mathematics but the boundary between `ℤ` and `ℕ`.

## Redundancy and duplication

The proof is short and contains almost no local logical redundancy. There is, however, a closely related proof pattern elsewhere in the codebase.

`SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor` also starts from

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
```

then derives divisibility of the norm square, descends through primality to the norm itself, and reaches a contradiction.

0392 is the descent-packet version of the same algebraic core. The difference is only the contradiction endpoint:

- the ramifier-stripped theorem uses `zeroSector_five_not_dvd_gamma_norm`;
- 0392 uses `five_not_dvd_D` together with `hnorm`.

So the algebraic transfer step is duplicated at the project level.

## Optimization candidates

### 1. Extract a mod-5 transfer helper

A reusable theorem such as

```lean
theorem five_dvd_norm_of_five_dvd_sndFactor
    (gamma : GoldenInt)
    (hH : (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

would allow 0392 to shrink to roughly

```lean
intro hH
have hNorm := five_dvd_norm_of_five_dvd_sndFactor gamma hH
rw [hnorm] at hNorm
exact p.five_not_dvd_D (by exact_mod_cast hNorm)
```

and could also be reused by the earlier zero-sector theorem.

### 2. Localize the cast bridge

If conversions from

```lean
(5 : ℤ) ∣ (D : ℤ)
```

to

```lean
5 ∣ D
```

occur repeatedly, a small dedicated helper could isolate the `exact_mod_cast` boundary. The current one-line use is already readable, however, so this is optional.

### 3. Reduce reliance on `ring_nf`

It may be possible to combine the divisibility facts in a syntactically more direct way and avoid `ring_nf`. Whether that is actually clearer is uncertain; the current proof makes the arithmetic normalization explicit and robust.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

0392 directly relies on Mathlib support for:

- integer divisibility;
- `Prime.dvd_of_dvd_pow`;
- `norm_num`;
- `ring_nf`;
- `exact_mod_cast`.

`GoldenInt`, `goldenNorm`, `goldenFifthSndFactor`, the packet definitions, 0382, and the mod-5 bridge are project-local preceding declarations.

In principle, the import could be narrowed from all of `Mathlib` to the modules providing integer divisibility, primality, ring normalization, `norm_num`, and norm-cast machinery.

However, no Lean build is performed in this task, so the **exact minimal import set is not verified**. Import reduction therefore remains only a candidate optimization.

## Comparator challenge suitability

**Yes.** As a standalone 0392 challenge the difficulty is low to medium because the proof is short once the correct APIs are known.

A useful challenge setup would expose

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
p.five_not_dvd_D
hnorm
```

and ask the model to reconstruct

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

The challenge tests whether the solver can:

1. exploit the congruence `H ≡ N² (mod 5)` through divisibility APIs;
2. descend from `5 ∣ N²` to `5 ∣ N` using primality;
3. transport the result through `hnorm` to `D`;
4. handle the `ℤ`/`ℕ` cast boundary correctly.

A more substantive Comparator challenge would hide `five_dvd_goldenFifthSndFactor_sub_norm_sq` as well, forcing reconstruction of the polynomial identity

$$
H(a,b)-N(a,b)^2
$$

as a multiple of 5 before completing the divisibility argument.

## Next declaration to read

The next declaration is

```lean
theorem fifthRoot_measure_lt
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    ...
```

Its declaration kind is `theorem`.

It proves that the visible second coordinate of the fifth root is strictly smaller than the source packet's `|s|`, providing the central strict inequality for the well-founded descent.

By the end of 0392, the fifth-root side has recovered

$$
H(a,b)>0,
\qquad
b>0,
\qquad
\gcd(|a|,|b|)=1,
\qquad
5\nmid H(a,b),
$$

which are precisely the local invariants needed before showing that **the data type is preserved while the descent measure strictly decreases**.

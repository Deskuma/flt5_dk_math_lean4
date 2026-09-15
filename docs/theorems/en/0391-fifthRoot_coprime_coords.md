# 0391 `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`

## Declaration kind

`theorem`

This theorem lives in the `GoldenZeroSectorDescentPacket` namespace. It recovers the primitive-coordinate property for the fifth root `gamma : GoldenInt` obtained in the preceding descent construction.

## Lean code

```lean
theorem fifthRoot_coprime_coords
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqF, hqSnd⟩
  have hqFZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqF
  have hqSndZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqSnd
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqFZ (by decide : 2 ≠ 0))
      (dvd_mul_of_dvd_left hqFZ gamma.snd))
      (dvd_pow hqSndZ (by decide : 2 ≠ 0))
  have hqD : q ∣ p.D := by
    rw [hnorm] at hqNormZ
    exact_mod_cast hqNormZ
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hqBaseSqZ : (q : ℤ) ∣ p.base.snd ^ 2 := by
    rw [hEq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqSndZ 5) _
  have hqBaseSq : q ∣ p.base.snd.natAbs ^ 2 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqBaseSqZ
  have hqBase : q ∣ p.base.snd.natAbs :=
    hqPrime.dvd_of_dvd_pow hqBaseSq
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqD hqBase)
    p.coprime_D_s
```

## Lean type

Conceptually, the theorem has the following type.

```lean
GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  goldenNorm gamma = (p.D : ℤ) →
  Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

The inputs are a descent packet `p`, a golden integer `gamma`, a proof `hroot` that the lift is the fifth power `gamma^5`, and a norm identification

```lean
goldenNorm gamma = (p.D : ℤ).
```

The conclusion is primitive coprimality of the two integer coordinates of `gamma`, expressed over naturals via `natAbs`:

$$
\gcd(|\gamma_{\mathrm{fst}}|,|\gamma_{\mathrm{snd}}|)=1.
$$

## Mathematical statement

Write `gamma=(a,b)` and `p.base=(r,s)`.

The goal is

$$
\gcd(|a|,|b|)=1.
$$

Assume instead that the coordinates are not coprime. Then there exists a common prime divisor $q$ such that

$$
q\mid |a|,
\qquad
q\mid |b|.
$$

Over the integers this becomes

$$
q\mid a,
\qquad
q\mid b.
$$

The golden norm is

$$
N(a,b)=a^2+ab-b^2.
$$

Hence $q$ divides every term and therefore

$$
q\mid N(a,b).
$$

Using `hnorm`,

$$
N(a,b)=D,
$$

so

$$
q\mid D.
$$

On the other hand, theorem 0388 `fifthRoot_snd_factor_eq` gives

$$
s^2=5bH(a,b),
$$

where

$$
H(a,b)=a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

Since $q\mid b$,

$$
q\mid s^2.
$$

Because $q$ is prime,

$$
q\mid |s|.
$$

Thus the same prime satisfies

$$
q\mid D,
\qquad
q\mid |s|.
$$

But theorem 0384 `coprime_D_s` already provides

$$
\gcd(D,|s|)=1,
$$

which is a contradiction. Therefore

$$
\gcd(|a|,|b|)=1.
$$

## Role in the overall proof

Theorem 0387 `exists_lift_eq_fifthPower` converts the original quadratic lift into a pure fifth power and also identifies its norm:

$$
T(r,s)=\gamma^5,
\qquad
N(\gamma)=D.
$$

Theorems 0388–0390 then project the second coordinate, prove positivity of the quartic factor, and fix the sign of `gamma.snd`.

The present theorem recovers the **primitive-coordinate invariant** needed to use `gamma` as new descent data.

Existence of a fifth root alone is not enough for an infinite-descent argument. To reconstruct another packet in the same primitive class, the new coordinates must again satisfy

$$
\gcd(|a|,|b|)=1.
$$

The proof transports a hypothetical common prime divisor of `gamma` in two directions:

1. through the norm to obtain $q\mid D$;
2. through the second-coordinate fifth-power identity to obtain $q\mid |s|$;
3. then collides those two facts with the already established invariant `coprime_D_s`.

Thus 0391 is a bridge from the fifth root in the golden integer ring back to the natural-number primitive invariant of the source packet.

## Direct dependencies

The principal directly used declarations are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenNorm`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.coprime_D_s`
- `Nat.Prime.not_coprime_iff_dvd`
- `Int.natCast_dvd.mpr`
- `Int.natCast_dvd.mp`
- `dvd_pow`
- `dvd_mul_of_dvd_left`
- `dvd_mul_of_dvd_right`
- `dvd_add`
- `dvd_sub`
- `Int.natAbs_pow`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `exact_mod_cast`

The hypothesis `hroot` is not used in the norm branch directly; it is used through

```lean
p.fifthRoot_snd_factor_eq gamma hroot.
```

The hypothesis `hnorm` serves the separate role of converting divisibility of `goldenNorm gamma` into divisibility of `p.D`. These two hypotheses therefore control two distinct transport paths in the contradiction.

## Proof flow

1. Negate the target coprimality.

   ```lean
   by_contra hcop
   ```

2. Use `Nat.Prime.not_coprime_iff_dvd` to extract a common prime divisor $q$.

   ```lean
   rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
     ⟨q, hqPrime, hqF, hqSnd⟩
   ```

3. Move divisibility of the natural absolute values to divisibility of the integer coordinates.

   ```lean
   have hqFZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqF
   have hqSndZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqSnd
   ```

4. Expand the norm

   $$
   N(a,b)=a^2+ab-b^2
   $$

   and prove that $q$ divides it.

5. Rewrite with `hnorm` and cast back to naturals to obtain

   $$
   q\mid D.
   $$

6. Obtain the second-coordinate factorization from theorem 0388:

   $$
   s^2=5bH(a,b).
   $$

7. Since $q\mid b$, prove $q\mid s^2$.

8. Use `Int.natAbs_pow` and `Int.natCast_dvd.mp` to obtain

   $$
   q\mid |s|^2
   $$

   in the natural numbers.

9. Use primality of $q$ to descend from the square:

   $$
   q\mid |s|.
   $$

10. Combine $q\mid D$ and $q\mid |s|` to contradict `p.coprime_D_s`.

## Lean-specific processing

### `Nat.Prime.not_coprime_iff_dvd`

The informal step “if the two coordinates are not coprime, choose a common prime divisor” is materialized by

```lean
Nat.Prime.not_coprime_iff_dvd.mp hcop.
```

This produces the prime witness `q` and the two divisibility proofs that drive the rest of the argument.

### `Int.natCast_dvd`

The theorem repeatedly crosses the boundary between natural absolute values and integer algebra.

```lean
Int.natCast_dvd.mpr hqF
Int.natCast_dvd.mpr hqSnd
```

turn divisibility of `natAbs` values into integer divisibility of the coordinates themselves. In the opposite direction,

```lean
Int.natCast_dvd.mp hqBaseSqZ
```

moves divisibility of the integer square back to naturals.

### Explicit norm divisibility construction

The proof expands `goldenNorm` and manually assembles divisibility of

$$
a^2+ab-b^2
$$

using `dvd_pow`, `dvd_mul_of_dvd_left`, `dvd_add`, and `dvd_sub`.

This keeps the arithmetic structure explicit rather than delegating it to a stronger automation tactic.

### `exact_mod_cast`

After rewriting `goldenNorm gamma` as `(p.D : ℤ)`, the proof has integer divisibility and needs the natural-number statement `q ∣ p.D`. `exact_mod_cast` performs this cast transfer.

### `Int.natAbs_pow`

The source coordinate is an integer, while `coprime_D_s` is formulated using `natAbs`. The line

```lean
simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqBaseSqZ
```

normalizes the square across that boundary.

### Prime divisor descent through a power

```lean
hqPrime.dvd_of_dvd_pow hqBaseSq
```

implements the prime fact

$$
q\mid |s|^2 \Longrightarrow q\mid |s|.
$$

Primality is essential here.

## Redundancy and duplication

The theorem has little accidental redundancy, but several patterns could potentially be abstracted.

### 1. Common coordinate divisor implies norm divisor

The construction of `hqNormZ` is a general fact about golden integers. A helper of the form

```lean
theorem goldenNorm_dvd_of_common_coord_dvd
    {q : ℤ} {z : GoldenInt}
    (hfst : q ∣ z.fst) (hsnd : q ∣ z.snd) :
    q ∣ goldenNorm z
```

would hide the explicit expansion of the norm.

The repository evidence inspected in this run does not establish whether an equivalent helper already exists, so this remains an optimization candidate rather than a confirmed omission.

### 2. Repeated `natAbs` / cast transport

The proof starts with a natural-number prime witness, moves to integer coordinates, and later returns to natural absolute values. This is not merely cosmetic duplication: it reflects the fact that coprimality is expressed over `Nat`, whereas the golden-order arithmetic lives over `ℤ`.

Still, if the same bridge appears repeatedly, a dedicated project API could shorten several proofs.

### 3. Indirect use of `hroot`

`hroot` is used only through `fifthRoot_snd_factor_eq`. This is a clean dependency boundary, not a defect. If many later lemmas require only the factored second-coordinate identity, a lower-level lemma taking that identity directly could complement the present higher-level API.

## Optimization candidates

### 1. Extract a norm-divisibility helper

This is the clearest local simplification. It would leave the theorem body centered on its true mathematical skeleton:

- extract a common prime;
- send it to `D` through the norm;
- send it to `|s|` through the second coordinate;
- contradict `coprime_D_s`.

### 2. Extract second-coordinate prime transport

The step

```lean
q ∣ gamma.snd.natAbs → q ∣ p.base.snd.natAbs
```

under primality and `hroot` could be packaged as an auxiliary lemma if it reappears in the later five-adic descent.

### 3. Localize cast management

A helper connecting divisibility of `goldenNorm gamma` with divisibility of `p.D` under `hnorm` could remove `exact_mod_cast` from the main proof and make the proof more declarative.

### 4. Final contradiction

The final line

```lean
exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqD hqBase)
  p.coprime_D_s
```

is already concise and structurally clear. Expanding it further would not improve the proof.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The Mathlib functionality directly visible in this theorem includes:

- `Nat.Coprime` and `Nat.Prime`;
- divisibility combinators such as `dvd_add`, `dvd_sub`, and `dvd_pow`;
- `Int.natCast_dvd`;
- `Int.natAbs_pow`;
- `exact_mod_cast`;
- basic `simp` rewriting.

A reduced import set would therefore likely involve natural-number prime/coprimality modules, integer divisibility and cast modules, powers, and the relevant cast tactic support. However, `GoldenInt`, `GoldenZeroSectorDescentPacket`, `goldenNorm`, and the preceding project theorems may bring additional transitive requirements.

Because this run does not perform a Lean build, the exact minimal import set is unverified. Thus **the confirmed working import is `Mathlib`; the minimal import remains undetermined**.

## Comparator challenge suitability

**Yes. This is a good medium-sized divisibility/cast/coprimality challenge.**

After abstracting away the FLT5-specific names, the core has the form

```lean
(hnorm : N a b = D)
(hEq : s ^ 2 = 5 * b * H)
(hDS : Nat.Coprime D s.natAbs)
⊢ Nat.Coprime a.natAbs b.natAbs
```

with the additional structural definition

$$
N(a,b)=a^2+ab-b^2.
$$

The main reasoning steps are:

1. extract a common prime witness from non-coprimality;
2. prove that the common divisor of `a` and `b` divides the norm;
3. transport that to a divisor of `D`;
4. use the second-coordinate identity to transport the same prime to `s`;
5. contradict coprimality of `D` and `|s|`.

A version retaining the `Nat`/`Int` boundary is especially useful for evaluating practical Lean engineering. A simplified single-domain version would instead focus on the pure number-theoretic structure.

## Next declaration to read

The next declaration is **0392 `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`**, also a `theorem`.

In the Lean source it begins:

```lean
theorem fifthRoot_five_not_dvd_H
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  ...
```

After 0391 establishes primitive coordinates for the fifth root itself, 0392 restores the next five-adic cleanliness invariant by proving that

$$
5\nmid H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

This mirrors the role previously played by 0381 `five_not_dvd_H` for the source packet. The descent is therefore reconstructing, one invariant at a time, the conditions needed to turn the fifth root into a new packet.
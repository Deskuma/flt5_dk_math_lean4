# 0330 — `GoldenZeroSectorInversionPacket.coprime_Q_d`

## Declaration kind

This declaration is a **`theorem`**.

It is a public theorem in `GoldenZeroSectorInversionPacket`. It proves that the fifth-power mass appearing in the zero-sector inversion,

$$
Q=5^5c^8,
$$

is coprime to the tenth-power base `d` on the quartic side.

## Lean type

```lean
/-- The full fifth-power mass is coprime to the quartic tenth-power base. -/
theorem GoldenZeroSectorInversionPacket.coprime_Q_d
    (p : GoldenZeroSectorInversionPacket) :
    Nat.Coprime (zeroSectorQ p.source.c) p.source.d := by
  have h5d : Nat.Coprime 5 p.source.d :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
  unfold zeroSectorQ
  exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

## Mathematical statement

`zeroSectorQ` is defined by

$$
Q=5^5c^8.
$$

The theorem combines the packet facts

$$
5\nmid d
$$

and

$$
\gcd(c,d)=1
$$

into

$$
\gcd(5^5c^8,d)=1.
$$

Hence the conclusion is

$$
\gcd(Q,d)=1.
$$

Mathematically, this is a very short composition rule: `d` is independent of both prime-factor sources from which `Q` is built, namely `5` and `c`, and these two exclusions are packaged into one `Nat.Coprime` statement.

## Role in the full proof

After zero-sector inversion, the factorization phase decomposes `A0` and `B0` into powers of two and fifth-power parts. The downstream packets need more than coprimality between the left and right factors themselves: the extracted fifth-power bases `e` and `f` must also remain coprime to `d`.

This theorem establishes the required mass-level coprimality first.

Since

$$
Q=5^5c^8,
$$

once a later branch proves ownership equations such as

$$
ef=Q
$$

or

$$
2ef=Q,
$$

coprimality of `e*f` with `d` can be descended from the present result.

Thus, unlike 0328 `no_common_odd_prime` and 0329 `odd_factor_halves`, which analyze the two positive inversion factors locally, this theorem supplies the **global prime-factor separation between the zero-sector mass `Q` and the quartic base `d`**.

## Direct dependencies

### `zeroSectorQ`

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

The proof expands this definition directly with `unfold zeroSectorQ`.

### `GoldenZeroSectorInversionPacket.five_not_dvd_d`

The packet stores

```lean
five_not_dvd_d : ¬ 5 ∣ source.d
```

which comes from the upstream theorem `GoldenZeroSectorCandidate.five_not_dvd_d`.

### `GoldenZeroSectorInversionPacket.coprime_c_d`

The packet also stores

```lean
coprime_c_d : Nat.Coprime source.c source.d
```

and this is the second coprimality input.

### Main Mathlib tools

- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.mul_left`
- `norm_num`
- `unfold`

## Proof flow

### 1. Build coprimality of `5` and `d`

The packet already provides

```lean
p.five_not_dvd_d : ¬ 5 ∣ p.source.d
```

and `5` is prime. Therefore

```lean
(by norm_num : Nat.Prime 5).coprime_iff_not_dvd
```

turns the nondivisibility statement into

$$
\gcd(5,d)=1.
$$

This is stored as `h5d`.

### 2. Raise the left factor to `5^5`

From `h5d.pow_left 5` we obtain

$$
\gcd(5^5,d)=1.
$$

`Nat.Coprime.pow_left` states that if the base on the left is coprime to the right-hand argument, then every natural power of that base remains coprime to the right-hand argument.

### 3. Raise `c` to `c^8`

From

```lean
p.coprime_c_d : Nat.Coprime p.source.c p.source.d
```

we obtain

```lean
p.coprime_c_d.pow_left 8
```

and hence

$$
\gcd(c^8,d)=1.
$$

### 4. Combine the two left factors

`Nat.Coprime.mul_left` combines

$$
\gcd(5^5,d)=1
$$

and

$$
\gcd(c^8,d)=1
$$

into

$$
\gcd(5^5c^8,d)=1.
$$

Because `zeroSectorQ` has already been unfolded, this is exactly the target.

## Lean-specific processing

### `Nat.Prime.coprime_iff_not_dvd`

On paper one normally uses “a prime `p` not dividing `n` implies `gcd(p,n)=1`” without comment. Lean makes this conversion explicit through the `Nat.Prime` API:

```lean
(by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
```

This line converts an exclusion of divisibility into a reusable `Nat.Coprime` object.

### `.pow_left`

`Nat.Coprime` is stable under powers. Here

```lean
h5d.pow_left 5
p.coprime_c_d.pow_left 8
```

raise the two independent left factors to the exact exponents occurring in `Q`.

### `.mul_left`

```lean
(h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

combines two coprimality statements with the same right-hand argument `d` into a statement about their product.

The chained method syntax makes the Lean proof almost as short as the mathematical derivation.

## Redundancy and duplication

There is essentially no substantive redundancy inside this theorem. The proof consists only of

1. converting `5 ∤ d` into `Coprime 5 d`,
2. lifting the two coprimality facts through powers,
3. combining them through multiplication.

One could inline `h5d` into the final `exact`, but keeping the local name makes the semantic conversion from `5 ∤ d` to `Coprime 5 d` explicit and improves readability.

## Optimization candidates

### 1. Keeping the present form is likely best

The current proof is already close to minimal:

```lean
have h5d : Nat.Coprime 5 p.source.d := ...
unfold zeroSectorQ
exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

Its structure mirrors the mathematics clearly, so further compression would bring little benefit.

### 2. A general coprimality lemma for `zeroSectorQ`

If later code repeatedly reconstructs

```lean
Nat.Coprime (zeroSectorQ c) n
```

it could be useful to extract a general lemma of the form

```lean
Nat.Coprime 5 n → Nat.Coprime c n → Nat.Coprime (zeroSectorQ c) n
```

For a single use, however, that abstraction would probably be unnecessary.

### 3. Storing `Coprime 5 d` directly

If the upstream packet stored `Nat.Coprime 5 d` instead of `¬ 5 ∣ d`, the first conversion in this theorem would disappear.

On the other hand, `¬ 5 ∣ d` is often the more convenient form for arithmetic exclusion arguments elsewhere, so the present packet design is reasonable.

## Required Mathlib imports and import optimization

The standalone canonical source uses

```lean
import Mathlib
```

for the entire generated artifact.

The theorem itself mainly needs

- natural-number primality and divisibility,
- `Nat.Coprime`,
- `Nat.Coprime.pow_left`,
- `Nat.Coprime.mul_left`,
- the `norm_num` tactic.

A substantially smaller import set than all of `Mathlib` is therefore likely possible. However, no Lean build is performed in this task, so the **minimal import set has not been verified**.

In particular, a minimal configuration would have to include both the location of the relevant `Nat.Coprime` / `Nat.Prime` lemmas and the tactic import required by `norm_num`.

## Comparator challenge suitability

**Suitable.**

The mathematical content is very clean, and the same proposition admits several possible Lean formulations, making it useful for comparing proof styles.

A challenge could impose constraints such as:

- unfold `zeroSectorQ`,
- use only `five_not_dvd_d` and `coprime_c_d` from the packet,
- forbid `omega`, `linarith`, and `nlinarith`,
- aim for a short proof using `Nat.Coprime.pow_left` and `mul_left`.

The expected core is

```lean
have h5d : Nat.Coprime 5 p.source.d :=
  (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
unfold zeroSectorQ
exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

This makes a good small Comparator challenge for testing whether the prover can select the appropriate Mathlib coprimality API without relying on arithmetic automation.

## Next declaration to read

The next declaration is

```lean
theorem fifth_mod_eleven_cases (n : ℕ) :
    n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
  rw [Nat.pow_mod]
  generalize hr : n % 11 = r
  have hlt : r < 11 := by rw [← hr]; omega
  interval_cases r <;> norm_num
```

Therefore the next sequence entry is **0331 `fifth_mod_eleven_cases`**.

It classifies fifth-power residues modulo eleven into

$$
0,1,-1\pmod{11},
$$

and is the finite residue computation used by the following theorem `eleven_dvd_d_of_fifth_add_four_fifth` in the mod-11 channel.
# 0336 — `GoldenZeroSectorFactorData.odd_eleven_channel`

## Declaration kind

This declaration is a **`theorem`**.

From the exact factor certificate in the odd branch, it extracts the fact that the prime $11$ is forced onto the `d` side, while being excluded from `c` and from the fifth-power factors `e`, `f`, and `e*f` owned by the `c` side.

```lean
/-- The odd branch exposes the forced eleven channel and excludes eleven from
every factor owned by `c`. -/
theorem GoldenZeroSectorFactorData.odd_eleven_channel
    {p : GoldenZeroSectorInversionPacket}
    (data : GoldenZeroSectorFactorData p)
    (hbranch : data.branch = .odd) :
    ∃ e f : ℕ,
      11 ∣ p.source.d ∧
      ¬ 11 ∣ p.source.c ∧
      ¬ 11 ∣ e ∧
      ¬ 11 ∣ f ∧
      ¬ 11 ∣ e * f := by
  cases data with
  | odd e f _ _ _ hefD _ _ _ _ _ hdiff =>
      have h11d : 11 ∣ p.source.d :=
        eleven_dvd_d_of_fifth_add_four_fifth hdiff
      have h11c : ¬ 11 ∣ p.source.c := by
        intro h11c
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11c h11d)
          p.coprime_c_d
      have h11ef : ¬ 11 ∣ e * f := by
        intro h11ef
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11ef h11d) hefD
      have h11e : ¬ 11 ∣ e := by
        intro h11e
        exact h11ef (dvd_mul_of_dvd_left h11e f)
      have h11f : ¬ 11 ∣ f := by
        intro h11f
        exact h11ef (dvd_mul_of_dvd_right h11f e)
      exact ⟨e, f, h11d, h11c, h11e, h11f, h11ef⟩
  | evenLeftLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
  | evenRightLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
```

## Lean type

The declaration has type

```lean
GoldenZeroSectorFactorData.odd_eleven_channel :
  {p : GoldenZeroSectorInversionPacket} →
  (data : GoldenZeroSectorFactorData p) →
  data.branch = .odd →
  ∃ e f : ℕ,
    11 ∣ p.source.d ∧
    ¬ 11 ∣ p.source.c ∧
    ¬ 11 ∣ e ∧
    ¬ 11 ∣ f ∧
    ¬ 11 ∣ e * f
```

It takes a fixed inversion packet `p`, an exact factor datum `data` depending on that packet, and the additional condition

```lean
hbranch : data.branch = .odd
```

asserting that the datum lies in the odd branch.

The conclusion existentially returns `e,f : ℕ` together with five pieces of $11$-adic information:

$$
11 \mid d,
\qquad
11 \nmid c,
\qquad
11 \nmid e,
\qquad
11 \nmid f,
\qquad
11 \nmid ef.
$$

The witnesses `e,f` are not arbitrary naturals: they are exactly the fifth-power factors stored in the `GoldenZeroSectorFactorData.odd` constructor.

## Mathematical statement

In the odd branch, declaration 0334 provides positive coprime factors $e,f$ satisfying in particular

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5,
$$

and the branch equation

$$
e^5 + 4d^5 = f^5.
$$

The certificate also carries

$$
\gcd(ef,d)=1.
$$

Applying 0332 `eleven_dvd_d_of_fifth_add_four_fifth` to the branch equation yields

$$
11 \mid d.
$$

The inversion packet itself carries

$$
\gcd(c,d)=1,
$$

so $11\mid c$ cannot occur together with $11\mid d$. Hence

$$
11 \nmid c.
$$

Likewise, from

$$
\gcd(ef,d)=1
$$

and $11\mid d$, one obtains

$$
11 \nmid ef.
$$

Finally, $11\mid e$ would imply $11\mid ef$, and similarly for $f$, so

$$
11 \nmid e,
\qquad
11 \nmid f.
$$

Thus the odd-branch difference equation **forces** the prime $11$ onto the `d` side, while coprimality excludes it from every factor controlled by `c`. In this sense, `eleven_channel` is a channel assigning the prime $11$ to one side of the factorization.

## Role in the full proof

This theorem is the API that connects the local mod-$11$ arithmetic prepared in 0331–0332 to the exact factorization certificate introduced in 0334.

0331 classified fifth-power residues modulo $11$ as

$$
0,\pm1 \pmod{11}.
$$

0332 used that classification to derive

$$
11\mid d
$$

from

$$
e^5+4d^5=f^5.
$$

But 0332 by itself knows nothing about the ownership of `c`, `e`, or `f`. The present theorem combines that local conclusion with

```lean
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

stored in `GoldenZeroSectorFactorData.odd`, together with the inversion packet's

```lean
p.coprime_c_d
```

to lift the mod-$11$ obstruction to a structural statement about the whole factor packet.

After this theorem, downstream arguments can use, in one step, the allocation

$$
11\mid d,
\qquad
11\nmid c e f.
$$

The displayed product form is only shorthand; the Lean conclusion records the non-divisibility of `c`, `e`, `f`, and `e*f` separately.

## Direct dependencies

### `GoldenZeroSectorFactorData`

Declaration 0334, a dependent inductive type.

From the odd constructor, this theorem mainly uses

```lean
hefD : Nat.Coprime (e * f) p.source.d
hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5
```

The positivity fields, `Nat.Coprime e f`, parity fields, `A_eq`, `B_eq`, and `ownership` are not directly used here.

### `GoldenZeroSectorFactorData.branch`

The `def` from 0335.

It forms the hypothesis

```lean
hbranch : data.branch = .odd
```

and allows the two even constructors to be eliminated as impossible.

### `eleven_dvd_d_of_fifth_add_four_fifth`

The theorem from 0332.

It is the direct arithmetic engine converting

```lean
hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5
```

into

```lean
h11d : 11 ∣ p.source.d
```

### `p.coprime_c_d`

Coprimality available from the source of the inversion packet:

$$
\gcd(c,d)=1.
$$

This excludes $11$ from `c` once $11\mid d$ is known.

### `Nat.not_coprime_of_dvd_of_dvd`

A Mathlib lemma expressing that two numbers cannot be coprime if a common divisor greater than one divides both.

It is used twice here with $q=11$.

### `dvd_mul_of_dvd_left` / `dvd_mul_of_dvd_right`

These lift divisibility of either `e` or `f` to divisibility of the product `e*f`.

## Proof flow

### 1. Split the factor datum by constructor

```lean
cases data with
```

examines all three constructors of `GoldenZeroSectorFactorData`.

In the odd branch, only the fields actually needed are named:

```lean
hefD
hdiff
```

along with the factor witnesses `e,f`.

### 2. Force $11\mid d$

```lean
have h11d : 11 ∣ p.source.d :=
  eleven_dvd_d_of_fifth_add_four_fifth hdiff
```

This is a direct application of 0332.

### 3. Exclude $11$ from `c`

Assume $11\mid c`. Together with `h11d`, this would make `c` and `d` non-coprime:

```lean
exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11c h11d)
  p.coprime_c_d
```

The `(by norm_num)` subproof discharges the numerical fact $1<11$.

### 4. Exclude $11$ from `e*f`

The same argument is applied to

```lean
hefD : Nat.Coprime (e * f) p.source.d.
```

If $11\mid ef$ and $11\mid d$, then `e*f` and `d` cannot be coprime.

### 5. Exclude $11$ from `e` and from `f`

Assuming $11\mid e`,

```lean
dvd_mul_of_dvd_left h11e f
```

gives $11\mid ef$, contradicting `h11ef`.

The argument for `f` is symmetric, using `dvd_mul_of_dvd_right`.

### 6. Build the existential result

```lean
exact ⟨e, f, h11d, h11c, h11e, h11f, h11ef⟩
```

returns the original odd-branch factor witnesses together with all five properties.

### 7. Eliminate the two even branches

```lean
| evenLeftLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
| evenRightLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
```

After unfolding 0335, the hypothesis becomes respectively an impossible equality

```lean
.evenLeftLow = .odd
.evenRightLow = .odd
```

between distinct constructors. `simp` closes both branches.

## Lean-specific processing

### `cases` on a dependent inductive

`data : GoldenZeroSectorFactorData p` is an inductive value indexed by `p`. Splitting it with `cases data` exposes constructor-specific proof fields in the local context.

Only the odd branch can construct the requested result; the two even branches disappear by constructor disjointness through `hbranch`.

### Discarding unused constructor fields with `_`

The odd constructor carries many arguments, but the pattern

```lean
| odd e f _ _ _ hefD _ _ _ _ _ hdiff =>
```

names only `e`, `f`, `hefD`, and `hdiff`.

This makes the theorem's true dependency footprint visible even though the certificate itself is much richer.

### Negation as a function to `False`

In Lean,

```lean
¬ 11 ∣ p.source.c
```

means

```lean
11 ∣ p.source.c → False.
```

Hence each non-divisibility result is built by introducing a divisibility hypothesis and deriving a contradiction.

### Letting `simp` use constructor disjointness

Once `GoldenZeroSectorFactorData.branch` is unfolded, inequalities between distinct enum constructors need no manual discrimination proof. `simp` handles them automatically.

## Redundancy and duplication

The proofs of `h11c` and `h11ef` have nearly identical structure:

1. assume $11$ divides the left object,
2. combine it with `h11d : 11 ∣ d`,
3. use `Nat.not_coprime_of_dvd_of_dvd` to contradict a known `Nat.Coprime` fact.

Likewise, the proofs of `h11e` and `h11f` are left-right symmetric.

The theorem is short enough, however, that abstracting these repetitions could reduce readability rather than improve it.

The constructor pattern contains many `_` placeholders, which makes it somewhat sensitive to changes in the positional field order of `GoldenZeroSectorFactorData`. That is a natural cost of using an inductive constructor with positional arguments.

## Optimization candidates

### Small helper for prime exclusion from coprimality

A local helper of the shape

```lean
Nat.Coprime a d → 11 ∣ d → ¬ 11 ∣ a
```

would make `h11c` and `h11ef` one-liners.

For this theorem alone, however, the abstraction benefit is small.

### More direct `Nat.Coprime` API

If Mathlib provides a suitably direct lemma connecting prime divisibility and coprimality, the uses of `Nat.not_coprime_of_dvd_of_dvd` might be shortened. The repository evidence inspected here does not establish a verified replacement, so this remains only a candidate.

### Branch-specific accessor theorem

Instead of accepting

```lean
hbranch : data.branch = .odd
```

and then splitting `data`, one could expose an accessor dedicated to the odd constructor.

The current API, however, has the advantage that callers can specify the branch through the public label without exposing the internal constructor of the proof certificate. This matches the design introduced by 0335.

### Packaging the conclusion in a structure

If the same five properties are reused repeatedly downstream, the nested existential/conjunction result could be promoted to a dedicated structure.

At the current scale, the existential form is lighter and adequate.

## Required Mathlib imports and import optimization

The standalone canonical source uses

```lean
import Mathlib
```

for the generated file as a whole.

This theorem directly relies at least on

- `Nat.Coprime`,
- `Nat.not_coprime_of_dvd_of_dvd`,
- `dvd_mul_of_dvd_left`,
- `dvd_mul_of_dvd_right`,
- `norm_num`,
- `simp`.

It also depends on earlier DkMath declarations such as `GoldenZeroSectorFactorData`, `GoldenZeroSectorInversionPacket`, and theorem 0332.

The surrounding source module `SignedGoldenZeroSectorFactorization.lean` uses a much wider range of facilities, including `omega`, `ring`, parity APIs, fifth-power splitting, and natural/integer coercions. Therefore the minimal import set for the whole module cannot be determined from this declaration alone.

In principle the umbrella `Mathlib` import could perhaps be reduced to individual modules providing coprimality, divisibility, and numeric tactics. No Lean build is performed in this task, so no minimal import set is claimed or verified.

## Comparator challenge suitability

**Suitable; medium difficulty.**

This makes a useful challenge because the proof combines several different Lean skills in a compact form:

- elimination of a dependent inductive,
- extraction of branch-specific certificate fields,
- reuse of `eleven_dvd_d_of_fifth_add_four_fifth`,
- prime exclusion from `Nat.Coprime`,
- lifting divisibility from a factor to a product.

A good challenge setup would provide declarations 0332–0335 and ask the solver to fill only the body of `odd_eleven_channel`.

Evaluation can check more than merely proving `11 ∣ d`: the solution must also derive non-divisibility for `c`, `e`, `f`, and `e*f`, and correctly eliminate the two even branches using `hbranch`.

## Next declaration to read

The next declaration is

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

This is not a theorem but a **`structure`**.

It packages together

- an inversion certificate, and
- exact factor data dependent on that particular inversion packet.

The field

```lean
factors : GoldenZeroSectorFactorData inversion
```

is a dependent field referring to the preceding field `inversion`. This structure becomes the proof-carrying container that passes the zero-sector inversion together with its certified fifth-power factorization branch into the later descent machinery.
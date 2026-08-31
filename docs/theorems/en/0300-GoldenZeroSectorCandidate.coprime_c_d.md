# 0300 — `GoldenZeroSectorCandidate.coprime_c_d`

## Declaration kind

This is a **`theorem`**.

From the coprimality of the primitive zero-sector coordinates stored in the candidate, together with the two tenth-power magnitude representations, it extracts that the split bases `c` and `d` themselves are coprime:

$$
\gcd(c,d)=1.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The two split tenth-power bases inherit coprimality. -/
theorem coprime_c_d (p : GoldenZeroSectorCandidate) :
    Nat.Coprime p.c p.d := by
  have hcop := coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.r p.s p.coprime_coords
  have hc : p.c ∣ p.s.natAbs := by
    rw [p.s_natAbs_eq]
    exact dvd_mul_of_dvd_right (dvd_pow_self p.c (by decide : 10 ≠ 0)) _
  have hd : p.d ∣ (goldenFifthSndFactor p.r p.s).natAbs := by
    rw [p.H_natAbs_eq]
    exact dvd_pow_self p.d (by decide : 10 ≠ 0)
  exact (hcop.of_dvd_left hc).of_dvd_right hd
```

The conclusion is the natural-number coprimality proposition

```lean
Nat.Coprime p.c p.d
```

## Mathematical meaning

Primitive coordinates already give

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

The candidate also stores

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Therefore

$$
c\mid |s|
$$

and

$$
d\mid |H(r,s)|.
$$

If two natural numbers are coprime, then any divisor chosen from the first and any divisor chosen from the second are also coprime. Hence

$$
\gcd(c,d)=1.
$$

The important point is that one does not need to "take tenth roots" of a coprimality statement. It is enough to observe that `c` divides the left magnitude and `d` divides the right magnitude. Coprimality descends along divisibility.

## Role in the full proof

The preceding theorem 0299 `a_eq_c_mul_d` established

$$
a=cd.
$$

The present theorem adds

$$
\gcd(c,d)=1.
$$

Together, these say that the original tenth-power base `a` is split into two factors with no common prime divisor. In other words, the prime support of `a` is distributed between `c` and `d` without overlap.

This is important for the later exclusion of the prime five, parity arguments, valuation separation, and factor-packet analysis. The equation

$$
a=cd
$$

alone would still allow a prime to occur simultaneously in both `c` and `d`; this theorem rules that out.

Thus 0299 and 0300 together upgrade the magnitude split into a **coprime base-level factorization**.

## Direct dependencies

### `coprime_natAbs_goldenFifthSndFactor_of_coprime`

This is the main upstream theorem used here:

```lean
theorem coprime_natAbs_goldenFifthSndFactor_of_coprime
    (r s : ℤ) (hrs : Nat.Coprime r.natAbs s.natAbs) :
    Nat.Coprime s.natAbs (goldenFifthSndFactor r s).natAbs
```

It turns primitive-coordinate coprimality

```lean
Nat.Coprime r.natAbs s.natAbs
```

into coprimality of the natural absolute values of the visible coordinate `s` and the quartic factor `H(r,s)`.

### `GoldenZeroSectorCandidate.coprime_coords`

A field of the 0290 structure:

```lean
p.coprime_coords : Nat.Coprime p.r.natAbs p.s.natAbs
```

This is the preserved provenance passed to the upstream coprimality theorem.

### `GoldenZeroSectorCandidate.s_natAbs_eq`

Another structure field:

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

It is used to prove `p.c ∣ p.s.natAbs`.

### `GoldenZeroSectorCandidate.H_natAbs_eq`

Likewise:

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

It is used to prove `p.d ∣ |H|`.

### `dvd_pow_self`

This supplies the fact that a base divides a nonzero positive power of itself:

```lean
dvd_pow_self p.c (by decide : 10 ≠ 0)
```

and

```lean
dvd_pow_self p.d (by decide : 10 ≠ 0)
```

construct divisibility into the tenth powers.

### `dvd_mul_of_dvd_right`

This lifts `c ∣ c^10` to

$$
c\mid 5^6c^{10}.
$$

### `Nat.Coprime.of_dvd_left` / `Nat.Coprime.of_dvd_right`

These are the core APIs that descend the known coprimality

$$
\gcd(|s|,|H|)=1
$$

to the selected divisors `c` and `d`.

## Proof flow

1. Pass `p.coprime_coords` to `coprime_natAbs_goldenFifthSndFactor_of_coprime`, obtaining
   $$
   \gcd(|s|,|H|)=1
   $$
   as `hcop`.
2. Rewrite with `p.s_natAbs_eq`, so that $|s|=5^6c^{10}$.
3. Use `dvd_pow_self` to obtain $c\mid c^{10}$ and `dvd_mul_of_dvd_right` to obtain
   $$
   c\mid |s|,
   $$
   stored as `hc`.
4. Rewrite with `p.H_natAbs_eq`, so that $|H|=d^{10}$.
5. Use `dvd_pow_self` to obtain
   $$
   d\mid |H|,
   $$
   stored as `hd`.
6. Apply `hcop.of_dvd_left hc` to shrink the left side from `|s|` to `c`.
7. Apply `.of_dvd_right hd` to shrink the right side from `|H|` to `d`, yielding `Nat.Coprime p.c p.d`.

## Lean-specific processing

On paper, the facts "`c` divides $5^6c^{10}$" and "`d` divides $d^{10}$" are nearly implicit. Lean's general power-divisibility API distinguishes the zero exponent case, so the proof explicitly supplies

```lean
(by decide : 10 ≠ 0)
```

for the exponent.

`decide` works because `10 ≠ 0` is a closed decidable proposition.

The final expression

```lean
(hcop.of_dvd_left hc).of_dvd_right hd
```

encodes coprimality inheritance along divisors in two steps. No gcd computation and no prime-factor enumeration are needed; the theorem closes entirely through the abstract `Nat.Coprime` API.

## Redundancy and overlap

Since `p.s_natAbs_eq` and `p.H_natAbs_eq` express the tenth-power split, one could imagine rewriting the coprimality statement into

$$
\gcd(5^6c^{10},d^{10})=1
$$

and then recovering `Coprime c d` from coprimality of powers.

The current implementation is cleaner: it does not need stronger rewriting or specialized power-coprimality lemmas. It only establishes

$$
c\mid |s|,
\qquad
d\mid |H|
$$

and descends the existing coprimality.

Also, 0299 `a_eq_c_mul_d` is not used here. This is best viewed as deliberate layer separation. The equation `a=cd` comes from the product-magnitude identity, whereas the present theorem comes from primitive-coordinate coprimality. The two information sources remain independent until later stages.

## Optimization candidates

1. The proof of `hc` may admit a shorter `simp`-style formulation using `p.s_natAbs_eq` and power divisibility, but the current version makes the provenance of the divisibility explicit.
2. `by decide : 10 ≠ 0` could likely be replaced by `by norm_num`; the current `decide` is smaller and direct.
3. An alternative proof could rewrite all of `hcop` and use coprimality lemmas for powers, but that would probably depend on more Mathlib API than the current divisor-descent proof.
4. If `c ∣ |s|` and `d ∣ |H|` are reused later, helper lemmas could be extracted. No such reuse has been confirmed from the inspected declaration sequence, so this is a **speculative optimization**.

Because no Lean build is performed in this task, these shortening ideas are **unverified**.

## Required Mathlib imports and import optimization

The standalone canonical artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the manifest places this declaration in the source region corresponding to

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The main Mathlib facilities used directly by this theorem are

- `Nat.Coprime`
- `Nat.Coprime.of_dvd_left`
- `Nat.Coprime.of_dvd_right`
- `dvd_pow_self`
- `dvd_mul_of_dvd_right`
- `rw`
- `decide`
- natural-number divisibility and power APIs

The theorem itself does not use `ring`, `omega`, `linarith`, `nlinarith`, `norm_num`, or `exact_mod_cast`.

The exact minimal import set is **unverified** because Lean builds are explicitly excluded. It is likely possible to replace `import Mathlib` with narrower divisibility/coprimality modules, but this would have to account for the imports required by all upstream definitions and lemmas as well.

## Comparator challenge suitability

**Suitable.** The difficulty is roughly beginner-intermediate to intermediate.

For example, provide only

```lean
hcop : Nat.Coprime p.s.natAbs
  (goldenFifthSndFactor p.r p.s).natAbs
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

and ask for

```lean
Nat.Coprime p.c p.d
```

Useful evaluation points are whether the solver can

- extract divisibility instead of manipulating the full tenth-power equations,
- find `dvd_pow_self`,
- use `Nat.Coprime.of_dvd_left/right` for downward inheritance,
- avoid unnecessary factorization or explicit gcd calculations.

The proof is short, but it is a good test of whether `Coprime` is understood structurally rather than merely as a computational statement `gcd = 1`.

## Relation to the PDFs

The target branch repository tree contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

and the Japanese PDF blob SHA is confirmed as `88796012a87abfb348e7c9e529332063288319a3`.

However, the GitHub connector's binary retrieval path returned no PDF body content in this run, so the exact page, section, or prose location corresponding to this theorem **could not be verified**. No speculative page mapping is made.

For the technical content, the current branch version of `Flt5DkMath/FLT5StandAlone.lean` is therefore treated as the primary canonical source.

## Next declaration to read

The next declaration is **0301 `GoldenZeroSectorCandidate.five_not_dvd_H`**, also a `theorem`.

In the Lean source it immediately follows 0300:

```lean
/-- The quartic factor retains the packet's exclusion of the prime five. -/
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s := by
  ...
```

After 0300 establishes coprimality of the split bases, 0301 excludes the prime `5` from the quartic factor `H` itself. This is the next step toward descending the exclusion to `d` and separating five-adic prime ownership.
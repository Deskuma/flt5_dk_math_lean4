# 0299 — `GoldenZeroSectorCandidate.a_eq_c_mul_d`

## Declaration kind

This declaration is a **`theorem`**.

It compares the three tenth-power magnitude relations stored in a zero-sector candidate and extracts the exact factorization of the original tenth-power base:

$$
a=cd.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The original tenth-power base is exactly the product of the split bases. -/
theorem a_eq_c_mul_d (p : GoldenZeroSectorCandidate) : p.a = p.c * p.d := by
  have hprod := p.natAbs_product_eq
  rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod
  have hpows : (p.c * p.d) ^ 10 = p.a ^ 10 := by
    apply Nat.mul_left_cancel (by positivity : 0 < 5 ^ 6)
    calc
      5 ^ 6 * (p.c * p.d) ^ 10 =
          (5 ^ 6 * p.c ^ 10) * p.d ^ 10 := by ring
      _ = 5 ^ 6 * p.a ^ 10 := hprod
  exact (Nat.pow_left_injective (by norm_num : 10 ≠ 0) hpows).symm
```

The conclusion is an equality in `ℕ`:

$$
p.a=p.c\,p.d.
$$

## Mathematical meaning

0298 `natAbs_product_eq` gives

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

The `GoldenZeroSectorCandidate` structure itself stores

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Substituting these two equations into the product identity yields

$$
(5^6c^{10})d^{10}=5^6a^{10}.
$$

Using the power-of-a-product identity,

$$
5^6(cd)^{10}=5^6a^{10}.
$$

Since $5^6>0$, the common factor can be cancelled, giving

$$
(cd)^{10}=a^{10}.
$$

For natural numbers, the tenth-power map is injective, so

$$
a=cd.
$$

Thus this theorem proves that the chosen tenth-power split is not merely a pair of independent magnitude representations: the split bases `c` and `d` exactly factor the original base `a`.

## Role in the full proof

The zero-sector inversion layer has separated the magnitudes of `s` and the quartic factor `H` into tenth powers. This theorem shows that the two resulting bases `c` and `d` together account for the entire original arithmetic base `a`.

That fact is important for the later coprimality, prime-exclusion, parity, and factor-packet arguments. In particular, the next theorem 0300 `GoldenZeroSectorCandidate.coprime_c_d` derives coprimality of `c` and `d` from coprimality of the coordinate and quartic factor. Combined with

$$
a=cd,
$$

one can track how the prime factors of the original base are distributed between the two split bases.

Accordingly, this theorem is the **bridge from the tenth-power magnitude split to a base-level factorization**.

## Direct dependencies

### `GoldenZeroSectorCandidate.natAbs_product_eq`

The theorem 0298 and the direct starting point:

```lean
p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
  5 ^ 6 * p.a ^ 10
```

### `GoldenZeroSectorCandidate.s_natAbs_eq`

A field of the structure introduced in 0290:

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

### `GoldenZeroSectorCandidate.H_natAbs_eq`

Another structure field:

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

### `Nat.mul_left_cancel`

Used to cancel the common factor `5 ^ 6`. In Lean the proof does this through the cancellative multiplicative structure of `ℕ`, rather than by division.

### `Nat.pow_left_injective`

Used to turn

```lean
(p.c * p.d) ^ 10 = p.a ^ 10
```

into equality of the bases. The fact that exponent `10` is nonzero is discharged by `norm_num`. The result has the reverse orientation from the goal, so `.symm` is applied.

## Proof flow

1. Obtain 0298 as `hprod`.
2. Rewrite `hprod` using `p.s_natAbs_eq` and `p.H_natAbs_eq`.
3. Introduce the intermediate equality
   $$
   (cd)^{10}=a^{10}
   $$
   as `hpows`.
4. Use `Nat.mul_left_cancel` so that it suffices to prove the equality after multiplication by the common factor $5^6$.
5. Use `ring` to normalize
   $$
   5^6(cd)^{10}=(5^6c^{10})d^{10}.
   $$
6. Close that calculation with `hprod`.
7. Apply `Nat.pow_left_injective` and reverse the resulting equality with `.symm`.

## Lean-specific processing

On paper one simply says “cancel $5^6$”. Because `ℕ` is not a field, the Lean proof does not divide by $5^6`; instead it explicitly uses multiplicative cancellation:

```lean
apply Nat.mul_left_cancel (by positivity : 0 < 5 ^ 6)
```

The `ring` tactic handles the rearrangement of products and powers, including the algebra behind

$$
(cd)^{10}=c^{10}d^{10}.
$$

Finally, `Nat.pow_left_injective` is an algebraic injectivity result on natural numbers; the proof does not need to pass through real-number monotonicity.

## Redundancy and overlap

It would likely be possible to combine the signed equations from 0296 `s_eq_neg_five_pow_mul_tenth` and 0297 `H_eq_tenth` and recover a similar base relation. The present theorem instead uses only the magnitude theorem 0298 and the magnitude fields in the structure, so it has no dependency on the sign-removal layer.

This is better viewed as a deliberate separation between the **sign layer** and the **magnitude-factorization layer** than as accidental duplication.

The construction of `hpows` does look slightly indirect because it temporarily reintroduces the common factor $5^6$ in order to use `Nat.mul_left_cancel`. That choice, however, keeps the argument purely in natural-number multiplicative algebra.

## Optimization candidates

1. `ring` might be replaceable by more local rewrites such as power-of-product and associativity lemmas, reducing tactic dependence.
2. A different natural-number cancellation lemma, together with a direct proof that `5 ^ 6 ≠ 0`, might shorten the construction of `hpows`.
3. The orientation passed to `Nat.pow_left_injective` might be rearranged to avoid the final `.symm`, though the current form is readable.
4. One could inline 0298 and prove `a = c*d` directly, but retaining the magnitude bridge as a named theorem gives a cleaner and more reusable API.

These possibilities are **unverified**, because no Lean build is performed in this task.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The main Mathlib facilities used directly by this theorem are:

- `Nat.mul_left_cancel`
- `Nat.pow_left_injective`
- `positivity`
- `ring`
- `norm_num`
- `rw`
- natural-number multiplication and power APIs

This theorem itself does not use `omega`, `linarith`, `nlinarith`, or `exact_mod_cast`.

On the generated-source side, this declaration belongs to the zero-sector inversion layer, corresponding in the established manifest mapping to `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`. The exact minimal import set is **not verified**, because the requested workflow forbids a Lean build.

## Comparator challenge suitability

**Suitable.** The difficulty is moderate.

A challenge could expose only the goal together with

```lean
p.natAbs_product_eq
p.s_natAbs_eq
p.H_natAbs_eq
```

and ask for the proof.

Useful evaluation points include whether the solver can:

- rewrite the magnitude fields into the product equation;
- identify $(cd)^{10}=a^{10}$ as the right intermediate statement;
- understand that natural-number cancellation, rather than division, is the appropriate operation;
- discover and use `Nat.pow_left_injective`;
- keep `ring` localized to the purely algebraic normalization step.

This tests more than tactic search: it tests recognition of the algebraic structure behind typed natural-number arithmetic.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The repository confirms the blobs exist. In this run, however, the PDF binary bodies were not available through the normal text retrieval path, and direct raw-PDF retrieval was unavailable. Therefore the exact page, section, and prose location corresponding to this theorem are **not verified**. No page-level correspondence is inferred.

For the technical content, the current branch version of `Flt5DkMath/FLT5StandAlone.lean` is treated as the primary source of truth.

## Next declaration to read

The next declaration is **0300 `GoldenZeroSectorCandidate.coprime_c_d`**, also a `theorem`.

In the current Lean source it immediately follows 0299:

```lean
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

After 0299 establishes the base-level factorization $a=cd$, 0300 establishes that the two split bases are themselves coprime. This prepares the later prime-ownership and valuation-separation arguments.
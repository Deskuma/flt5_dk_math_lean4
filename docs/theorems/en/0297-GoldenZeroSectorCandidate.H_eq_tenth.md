# 0297 — `GoldenZeroSectorCandidate.H_eq_tenth`

## Declaration kind

This declaration is a **`theorem`**.

It restores the positive sign to the absolute-value tenth-power split of the quartic factor stored by the zero-sector candidate, using the strict positivity established in 0292 `GoldenZeroSectorCandidate.H_pos`, and thereby recovers an exact signed equation.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sign removal for the positive quartic factor. -/
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  have habs : ((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
      (p.d : ℤ) ^ 10 := by
    exact_mod_cast p.H_natAbs_eq
  rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs
  exact habs
```

The conclusion is

$$
goldenFifthSndFactor(p.r,p.s)=p.d^{10}.
$$

## Mathematical meaning

0290 `GoldenZeroSectorCandidate` stores, for the quartic factor

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4,
$$

the field

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

corresponding to

$$
|H(p.r,p.s)|=p.d^{10}.
$$

On the other hand, 0292 `p.H_pos` has already established

$$
0<H(p.r,p.s).
$$

Hence $H\ge0$, so

$$
|H|=H,
$$

and therefore

$$
H(p.r,p.s)=p.d^{10}.
$$

This theorem is the positive-sign counterpart of 0296 `s_eq_neg_five_pow_mul_tenth`. There, the visible coordinate is negative and the proof uses $|s|=-s$; here the quartic factor is positive and the proof uses $|H|=H$.

## Role in the full proof

When the zero-sector arithmetic receiver enters the inversion layer, the chosen tenth-power split is retained in absolute-value form:

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Together, 0296 and this theorem convert those data into the exact signed equations

$$
s=-5^6c^{10},
\qquad
H(r,s)=d^{10}.
$$

These equations are important downstream. The next theorem, 0298 `natAbs_product_eq`, and then 0299 `a_eq_c_mul_d`, connect the original product equation with the two tenth-power splits and recover the original base as `a = c * d`. `H_eq_tenth` is also reused later by `five_not_dvd_d`, `d_odd`, `discriminant_eq`, and by the construction of the descent packet's `H_eq` field.

Thus this theorem is the boundary where a quartic tenth power received only through an absolute value becomes exact positive algebra usable by inversion and descent.

## Direct dependencies

### `GoldenZeroSectorCandidate.H_natAbs_eq`

A field of the 0290 structure:

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

This is the direct source of the magnitude information.

### `GoldenZeroSectorCandidate.H_pos`

The theorem from 0292:

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

The present proof weakens it with `.le` to

```lean
p.H_pos.le : 0 ≤ goldenFifthSndFactor p.r p.s
```

for absolute-value removal.

### `Int.ofNat_natAbs_of_nonneg`

For a nonnegative integer `z`, this Mathlib lemma gives

```lean
(z.natAbs : ℤ) = z
```

and is applied here with $z=H(p.r,p.s)$.

### `exact_mod_cast`

`p.H_natAbs_eq` is an equality in `ℕ`, whereas the target theorem is an equality in `ℤ`. The proof therefore lifts it to

```lean
((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
  (p.d : ℤ) ^ 10
```

before removing the absolute value.

## Proof flow

1. Lift `p.H_natAbs_eq` from `ℕ` to `ℤ` with `exact_mod_cast`, producing `habs`.
2. Obtain nonnegativity from `p.H_pos.le`.
3. Rewrite `((H).natAbs : ℤ)` to `H` using `Int.ofNat_natAbs_of_nonneg`.
4. After the rewrite, `habs` is exactly the goal, so close with `exact habs`.

Unlike 0296, no final `linarith` call is required: in the nonnegative case, the casted `natAbs` rewrites directly to the quartic factor itself.

## Lean-specific processing

Mathematically, $H>0$ and $|H|=d^{10}$ immediately imply $H=d^{10}$. In Lean, however, `Int.natAbs` has codomain `ℕ`, so the natural-number equality must first be moved into the integer domain.

`exact_mod_cast` handles that type boundary, after which `Int.ofNat_natAbs_of_nonneg p.H_pos.le` removes the absolute value.

Also, `H_pos` provides strict positivity, while the absolute-value lemma only needs nonnegativity, so `.le` explicitly projects the stronger fact to the weaker one required by the API.

## Redundancy and overlap

The theorem is structurally symmetric with 0296 `s_eq_neg_five_pow_mul_tenth`:

- 0296: from `s < 0`, use `Int.ofNat_natAbs_of_nonpos`;
- 0297: from `H > 0`, use `Int.ofNat_natAbs_of_nonneg`.

The present theorem is one step simpler because the rewrite leaves `habs` exactly equal to the target, so no arithmetic tactic is needed afterward.

It may be possible to remove the named intermediate `habs` and compress the cast and rewrite into a single `simpa`-style proof. The current form, however, cleanly separates type conversion from sign removal and is pedagogically useful in a theorem museum.

## Optimization candidates

1. A shorter proof may be possible by avoiding the named `habs` and closing directly with `simpa` after `exact_mod_cast`.
2. The `rw ... at habs` step might be merged with the cast step using a `simpa` expression involving `Int.ofNat_natAbs_of_nonneg p.H_pos.le`.
3. One could abstract 0296 and 0297 into a helper lemma turning a `natAbs` power equality plus sign information into a signed equality. Because the positive and negative cases use different APIs and both proofs are already short, the gain from abstraction appears limited.

These shorter alternatives are **unverified**, because no Lean build was run as requested.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the manifest/generated-source boundary places this declaration in

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The main facilities directly used by this theorem are

- `exact_mod_cast`;
- `Int.ofNat_natAbs_of_nonneg`;
- the order projection `.le`;
- `rw`;
- the existing theorem `GoldenZeroSectorCandidate.H_pos`.

The theorem itself does not use `linarith`, `nlinarith`, `ring`, `positivity`, `omega`, or `norm_num`.

Because no Lean build was run, the exact minimal replacement for `import Mathlib` is **not verified**. In particular, the minimal imports for this theorem alone should be distinguished from the minimal imports for the whole module containing the preceding candidate API.

## Comparator challenge suitability

**Suitable.** The difficulty is low to medium.

A natural challenge is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  ...
```

with `p.H_natAbs_eq` and `p.H_pos` available for discovery and use.

The comparison can test whether a solver recognizes that `H_natAbs_eq` is an equality in `ℕ`, transports it to `ℤ` with `exact_mod_cast`, weakens strict positivity to nonnegativity with `.le`, and finds `Int.ofNat_natAbs_of_nonneg` to remove the absolute value.

This is therefore a good challenge for Lean integer absolute-value APIs and cast discipline rather than for difficult algebra.

## Relation to the PDFs

The repository tree on the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`;
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, through the ordinary text retrieval path available in the GitHub connector during this run, the binary PDF contents could not be obtained as analyzable text. Therefore the exact PDF page number, section number, and a matching passage for this theorem are **not confirmed**. The current Lean source `Flt5DkMath/FLT5StandAlone.lean` is treated as the primary source, and no specific PDF content is inferred.

## Next declaration to read

The next declaration is **0298 `GoldenZeroSectorCandidate.natAbs_product_eq`**, also a `theorem`:

```lean
/-- Natural absolute-value form of the signed product equation. -/
theorem natAbs_product_eq (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, pow_succ] using h
```

Where 0296–0297 finish sign removal for the individual factors, 0298 applies `Int.natAbs` to the original signed product equation and extracts a natural-number multiplicative identity. That identity is the direct input to the following theorem `a_eq_c_mul_d`, which recovers

$$
a=c d.
$$

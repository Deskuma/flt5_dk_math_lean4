# 0290 — `GoldenZeroSectorCandidate`

## Declaration kind

This declaration is a **`structure`**.

It packages the sign, coprimality, norm, and tenth-power splitting data obtained in the zero-sector arithmetic layer into a single record that the later inversion proofs can consume as one input.

## Lean type

```lean
/--
All raw hypotheses supplied by the zero-sector arithmetic receiver, including the
chosen tenth-power split.  No norm or coprimality provenance is discarded.
-/
structure GoldenZeroSectorCandidate where
  r : ℤ
  s : ℤ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  five_not_dvd_b : ¬ 5 ∣ b
  norm_eq_or_eq_neg :
    goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)
  product_eq :
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10
  coprime_coords : Nat.Coprime r.natAbs s.natAbs
  s_natAbs_eq : s.natAbs = 5 ^ 6 * c ^ 10
  H_natAbs_eq : (goldenFifthSndFactor r s).natAbs = d ^ 10
```

This declaration does not prove a proposition. It defines a record type containing both data and proofs that will be projected by subsequent theorems.

## Mathematical meaning

An element $p$ of `GoldenZeroSectorCandidate` contains integer coordinates

$$
(r,s)\in\mathbb Z^2
$$

and natural-number parameters

$$
a,b,c,d\in\mathbb N.
$$

It records

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1,\qquad 5\nmid b.
$$

For the golden norm it keeps the signed alternative

$$
N(r,s)=b
\quad\text{or}\quad
N(r,s)=-b,
$$

represented in Lean by

```lean
norm_eq_or_eq_neg :
  goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
  goldenNorm ⟨r, s⟩ = -(b : ℤ)
```

The central signed zero-sector equation is stored exactly as

$$
s\,H(r,s)=-5^6a^{10},
$$

where

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s).
$$

Primitive coordinates are retained through

$$
\gcd(|r|,|s|)=1.
$$

Finally, the chosen tenth-power split from the arithmetic receiver is stored as

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Thus the structure is more than a tuple of coordinates: it is a **proof certificate carrying zero-sector arithmetic provenance into the inversion layer**.

## Role in the full proof

Declarations 0282–0289 prepared the inversion quantities

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W,
\qquad
Q=5^5c^8,
$$

as well as the quartic diagonalization and nonnegativity result.

0290 is the boundary where those constructions can be applied to an actual zero-sector candidate. It acts as a **state packet** for the inversion argument.

Subsequent theorems take

```lean
p : GoldenZeroSectorCandidate
```

and obtain their hypotheses through projections such as `p.a_pos`, `p.product_eq`, and `p.s_natAbs_eq`. This avoids repeating a long list of hypotheses in every theorem.

The immediately following 0291 `GoldenZeroSectorCandidate.product_neg` already uses the structure in exactly this way:

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

The source then proceeds through `H_pos`, `s_neg`, `c_pos`, `d_pos`, `H_eq_tenth`, `a_eq_c_mul_d`, `coprime_c_d`, `factor_product`, and further inversion lemmas. Hence 0290 is an important API boundary between zero-sector arithmetic and inversion/factorization.

## Direct dependencies

### `goldenNorm`

The norm of a golden-integer coordinate. The structure stores that this norm equals either $b$ or $-b$.

### `goldenFifthSndFactor`

The quartic factor occurring in the second coordinate of a fifth power in the golden-integer model:

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

It appears in both `product_eq` and `H_natAbs_eq`.

### `Nat.Coprime`

Used by `coprime_a_b` and `coprime_coords`. In the latter, integer coordinates are transferred to natural numbers using `Int.natAbs`.

### `Int.natAbs`

Used to express absolute values of the signed integer quantities $r$, $s$, and $H(r,s)$ as natural numbers.

## Construction flow

Because this is a structure declaration, there is no theorem-style `by` proof. Lean generates a record constructor and projections for all fields.

Conceptually, the zero-sector arithmetic receiver fills the record as follows.

1. Store the basic coordinates `r`, `s` and the decomposition parameters `a`, `b`, `c`, `d`.
2. Preserve the primitive packet information through `a_pos`, `b_pos`, `coprime_a_b`, and `five_not_dvd_b`.
3. Preserve norm provenance in `norm_eq_or_eq_neg`.
4. Preserve the signed tenth-power product equation in `product_eq`.
5. Preserve primitive coordinate coprimality in `coprime_coords`.
6. Preserve the chosen tenth-power split in `s_natAbs_eq` and `H_natAbs_eq`.

The key design point is that the record does not keep only $c$ and $d$ while discarding earlier information. It retains $a,b$, the norm alternative, the signed product, and coprimality. This is exactly what the source docstring means by “No norm or coprimality provenance is discarded.”

## Lean-specific processing

`structure ... where` causes Lean to generate

- a constructor,
- projections such as `p.r`, `p.s`, `p.a`,
- proof projections such as `p.a_pos`, `p.product_eq`, and so on.

The coordinate fields `r,s` live in `ℤ`, while `a,b,c,d` live in `ℕ`. Later proofs therefore require bridges such as `exact_mod_cast` and natural/integer cast lemmas. The next theorem `product_neg`, for example, converts

```lean
p.a_pos : 0 < p.a
```

into the integer inequality

$$
0<(p.a:\mathbb Z)
$$

using `exact_mod_cast`.

Likewise, `coprime_coords` records primitive signed coordinates through the natural values `r.natAbs` and `s.natAbs`, which makes the information compatible with Mathlib's natural-number divisibility and coprimality API.

## Redundancy and overlap

At first sight, `product_eq` and the pair `s_natAbs_eq` / `H_natAbs_eq` may look redundant, but they carry different information.

`product_eq` preserves the **signed full-product equation**

$$
sH=-5^6a^{10},
$$

which is needed for later sign arguments such as `product_neg` and `s_neg`.

The two absolute-value equations preserve the **factor-by-factor exact split**

$$
|s|=5^6c^{10},\qquad |H|=d^{10},
$$

which is used by `c_pos`, `d_pos`, `H_eq_tenth`, `a_eq_c_mul_d`, and related results.

Similarly, `coprime_a_b` and `coprime_coords` refer to different stages of the arithmetic reduction and cannot simply be identified.

Therefore there is no obvious field that can be removed as mere duplication.

## Optimization candidates

### 1. Split into substructures

One possible redesign would separate

- original packet data,
- signed zero-sector product data,
- chosen tenth-power split data,

into smaller structures, with `GoldenZeroSectorCandidate` composing them.

The present flat design, however, gives shallow projections such as `p.product_eq`, which is convenient for both proofs and exposition.

### 2. Remove derivable fields

If a future refactor establishes that some fields can always be reconstructed by short and stable lemmas, the record could in principle be minimized. However, the source explicitly states that provenance is intentionally retained, so removing logically derivable fields merely to reduce size could conflict with the intended design.

### 3. Make it a proposition?

The structure has no explicit `: Prop`; it is an ordinary data-bearing structure. That is appropriate because later proofs compute with and project the parameters `r,s,a,b,c,d`. Compressing the record into a pure existence proposition would make the projection-oriented API substantially less convenient.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The principal facilities directly used by this structure are

- `ℤ`, `ℕ`,
- `Nat.Coprime`,
- `Int.natAbs`,
- powers and divisibility notation,
- the existing definitions `goldenNorm` and `goldenFifthSndFactor`.

The structure itself uses no tactics, so tactics such as `ring`, `nlinarith`, or `positivity` are not required by declaration 0290 alone.

No Lean build is run in this task, so the exact minimal import set for the original `SignedGoldenZeroSectorInversion.lean` module is **not verified**. A concrete replacement for `import Mathlib` is therefore not asserted here.

## Comparator challenge suitability

**Not well suited as a direct theorem-proving challenge, but suitable as an API-design challenge.**

There is no proof hole to fill; the central problem is deciding which invariants must be stored as fields.

A Comparator-style exercise could instead ask for the smallest practical field set supporting later results such as

- `product_neg`,
- `H_pos`,
- `s_neg`,
- `a_eq_c_mul_d`,
- `coprime_c_d`.

For the standard “complete this Lean theorem” format, the verdict is **not suitable**. For structure/API design comparison, it is **suitable**.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The Japanese PDF repository file and blob SHA can be identified, but the GitHub connector's normal UTF-8 retrieval path does not expose the binary body in analyzable text form. The English PDF likewise fails UTF-8 decoding.

Therefore the exact page, section, and wording corresponding to this structure are **not verified**, and no such location is guessed here. The technical account above is grounded primarily in the Lean source on the target branch.

## Next declaration to read

The next declaration is 0291 `GoldenZeroSectorCandidate.product_neg`, a **`theorem`**:

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

It is the first theorem to consume the record created in 0290, immediately turning the stored `product_eq` and `a_pos` fields into the sign statement

$$
p.s\,H(p.r,p.s)<0.
$$

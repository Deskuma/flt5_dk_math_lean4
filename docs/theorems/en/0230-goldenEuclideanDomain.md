# 0230 — `goldenEuclideanDomain`

## Lean type

```lean
/-- Euclidean division for the absolute norm, with well-founded measure
`natAbs (goldenNorm x)`. -/
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
  r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
  r_wellFounded := (measure goldenEuclideanSize).wf
  remainder_lt := golden_remainder_size_lt
  mul_left_not_lt := by
    intro a b hb
    apply not_lt_of_ge
    rw [← golden_mul_eq, goldenEuclideanSize_mul]
    have hbSize : 1 ≤ goldenEuclideanSize b :=
      goldenEuclideanSize_pos_of_ne_zero hb
    exact Nat.le_mul_of_pos_right _ hbSize
```

This declaration is not a theorem but a `noncomputable instance`. It registers the previously constructed golden-integer ring `GoldenInt` as a standard Mathlib `EuclideanDomain`.

## Mathematical statement and meaning of the declaration

Mathematically, this instance states that the golden integer ring

$$
\mathbb Z[\varphi],\qquad \varphi^2=\varphi+1
$$

is Euclidean with respect to the absolute norm measure

$$
\operatorname{size}(x)=|N(x)|.
$$

Thus for arbitrary $x,y\in\mathbb Z[\varphi]$ with $y\neq0$, one can choose a quotient $q$ and remainder $r$ such that

$$
x=yq+r
$$

and

$$
|N(r)|<|N(y)|.
$$

In this development, the quotient is constructed by expressing $x/y$ in rational golden-basis coordinates and rounding each coordinate to the nearest integer. The resulting rounding error lies in a fundamental square cell on which the golden norm form

$$
Q(u,v)=u^2+uv-v^2
$$

satisfies

$$
|Q(u,v)|\le\frac5{16}<1.
$$

That contraction produces the strict decrease required for Euclidean division.

## Role in the full proof

Declaration 0230 is the integration point for the entire `GoldenEuclidean.lean` module.

Declarations 0209–0229 construct the following ingredients in order:

- rational coordinates `GoldenRat`;
- the rational norm form `goldenRatNorm`;
- nearest-integer rounding;
- the sharp `5/16` bound on the fundamental cell;
- nonvanishing of the norm on nonzero golden integers;
- the rationalized numerator `x * conjugate(y)`;
- rational quotient coordinates;
- the nearest-lattice quotient `goldenQuotient`;
- the remainder `goldenRemainder`;
- the quotient/remainder reconstruction identity;
- the Euclidean size `natAbs (goldenNorm x)`;
- positivity and multiplicativity of that size;
- the remainder norm identity;
- strict remainder decrease;
- an explicit quotient/remainder witness package.

The present instance connects all of these pieces to Mathlib's `EuclideanDomain` interface at once.

After this registration, generic gcd, Euclidean-algorithm, coprimality, and divisibility APIs become available for `GoldenInt`. The standalone source module header explicitly notes that the later `GoldenCoprimeFactor` layer uses the resulting gcd theory to split coprime factors of a fifth power.

Thus 0230 is a major boundary: the explicit coordinate arithmetic developed so far becomes a fully integrated member of Mathlib's abstract algebra hierarchy.

## Direct dependencies

The instance fields directly refer to:

- 0220 `goldenQuotient`;
- 0222 `goldenQuotient_zero`;
- 0221 `goldenRemainder`;
- 0223 `golden_quotient_mul_add_remainder`;
- 0224 `goldenEuclideanSize`;
- 0228 `golden_remainder_size_lt`;
- 0159 `golden_mul_eq`;
- 0226 `goldenEuclideanSize_mul`;
- 0225 `goldenEuclideanSize_pos_of_ne_zero`;
- Mathlib `measure`;
- Mathlib `Nat.le_mul_of_pos_right`.

The earlier algebraic construction has already supplied the ring and domain structure required for `EuclideanDomain GoldenInt`.

Conceptually,

$$
\text{explicit quotient/remainder}
+
\text{well-founded size}
+
\text{strict remainder decrease}
\Longrightarrow
\texttt{EuclideanDomain GoldenInt}.
$$

## Construction flow

### 1. Quotient and the zero-divisor branch

```lean
quotient := goldenQuotient
quotient_zero := goldenQuotient_zero
```

The nearest-lattice quotient from 0220 becomes the standard Euclidean quotient, and 0222 supplies the total-function specification when the divisor is zero.

### 2. Remainder and reconstruction

```lean
remainder := goldenRemainder
quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
```

The remainder defined in 0221 by

$$
r=x-qy
$$

is registered directly, while 0223 supplies the reconstruction law

$$
yq+r=x.
$$

### 3. Euclidean relation

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
r_wellFounded := (measure goldenEuclideanSize).wf
```

The Euclidean relation is simply strict inequality of the natural-valued size:

$$
a\;r\;b
\iff
|N(a)|<|N(b)|.
$$

Using `measure goldenEuclideanSize`, well-foundedness is inherited from the standard well-founded order on natural numbers rather than proved from scratch.

### 4. Strict remainder decrease

```lean
remainder_lt := golden_remainder_size_lt
```

Declaration 0228 already proves

$$
|N(r)|<|N(y)|,
$$

so it can be installed directly as the Euclidean remainder-decrease condition.

### 5. Multiplication does not decrease the relation on the left

The final field proves that multiplying by a nonzero factor cannot make the size smaller in the forbidden direction:

```lean
mul_left_not_lt := by
  intro a b hb
  apply not_lt_of_ge
  rw [← golden_mul_eq, goldenEuclideanSize_mul]
  have hbSize : 1 ≤ goldenEuclideanSize b :=
    goldenEuclideanSize_pos_of_ne_zero hb
  exact Nat.le_mul_of_pos_right _ hbSize
```

By 0226,

$$
\operatorname{size}(ab)
=
\operatorname{size}(a)\operatorname{size}(b),
$$

and by 0225, $b\neq0$ implies

$$
1\le\operatorname{size}(b).
$$

Hence

$$
\operatorname{size}(a)
\le
\operatorname{size}(a)\operatorname{size}(b).
$$

## Lean-specific processing

The declaration is marked `noncomputable instance`.

Although the quotient itself is explicitly defined using `round`, the `EuclideanDomain` structure and the surrounding hierarchy are registered in a noncomputable context. This is a Lean computability-management issue, not a mathematical failure to construct a quotient.

The line

```lean
r_wellFounded := (measure goldenEuclideanSize).wf
```

is a particularly Lean-specific compression: instead of proving a custom well-founded recursion principle, the implementation transports the standard well-foundedness of `<` on `ℕ` through the measure map.

The proof of `mul_left_not_lt` also exposes the boundary between the raw and standard multiplication APIs:

```lean
rw [← golden_mul_eq, goldenEuclideanSize_mul]
```

Standard multiplication is first rewritten back to `goldenMul` so that the bespoke size-multiplicativity theorem 0226 can be applied. The same raw/standard boundary appeared earlier in the conjugation and norm power proofs.

## Redundancy and duplication

The instance itself contains little unnecessary duplication; its main purpose is to aggregate the results of 0209–0229.

Some API-level duplication remains visible, however.

1. **`goldenMul` versus standard `*`**
   - `mul_left_not_lt` crosses this boundary explicitly through `golden_mul_eq`.

2. **0229 `exists_golden_quotient_remainder`**
   - 0229 already packages Euclidean division existentially, but the `EuclideanDomain` structure expects explicit quotient/remainder functions and their laws as separate fields, so 0229 cannot simply be inserted as one field.

3. **The `goldenEuclideanSize` wrapper**
   - it is definitionally just `Int.natAbs (goldenNorm x)`, but naming the measure greatly improves readability in the relation and downstream lemmas.

Therefore several logically thin wrappers are still useful at the API level.

## Optimization candidates

1. **Add a standard-multiplication version of size multiplicativity**

A theorem of the form

```lean
goldenEuclideanSize (x * y) =
  goldenEuclideanSize x * goldenEuclideanSize y
```

would eliminate the `← golden_mul_eq` rewrite in `mul_left_not_lt`.

2. **Bundle the Euclidean division certificate internally**

Quotient, remainder, reconstruction, and strict decrease could be packaged in an internal structure. This may reduce duplication between 0229 and the final instance assembly.

3. **Abstract the quadratic-order pattern**

The nearest-lattice rounding plus norm-contraction construction could potentially be generalized to a wider class of quadratic orders. The sharp `5/16` bound is specific to the golden norm, however, so excessive abstraction may make the mathematics less transparent.

4. **Compare with existing Mathlib quadratic-integer infrastructure**

If `AdjoinRoot`, quadratic algebra, or an existing Euclidean-domain instance can represent the same ring, the amount of code, definitional transparency, and simp behavior should be compared.

The present implementation is longer, but it keeps the quotient selection and strict-decrease argument completely explicit and therefore highly auditable.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct Mathlib surface used by this instance includes primarily:

- `EuclideanDomain`;
- `measure`;
- well-foundedness APIs;
- `Nat.le_mul_of_pos_right`;
- order lemmas such as `not_lt_of_ge`.

The full `GoldenEuclidean.lean` module also uses:

- rational rounding;
- `abs_sub_round`;
- `nlinarith`;
- `linarith`;
- `field_simp`;
- `exact_mod_cast`;
- integer `natAbs`;
- ring normalization.

Therefore the minimal import surface of the whole module is substantially broader than that of 0230 alone.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

This declaration is especially well suited for a Comparator challenge because it sits exactly at the architecture boundary.

Possible implementations include:

- A: the current explicit-coordinate + nearest-lattice rounding + `5/16` bound construction;
- B: reuse an existing Mathlib quadratic-integer / Euclidean-domain infrastructure;
- C: construct the ring abstractly from `AdjoinRoot (X^2-X-1)`;
- D: choose a quotient by directly minimizing the norm over lattice points;
- E: package quotient/remainder laws in an internal certificate and make the final instance thinner.

Useful comparison metrics are:

- theorem count;
- proof-line count;
- strength of `rfl` / `simp` normalization;
- concreteness of the quotient;
- transparency of the strict-decrease argument;
- depth of Mathlib dependencies;
- simplicity of downstream gcd / coprimality proofs;
- generalizability.

The comparison between A and B is particularly valuable because it measures the trade-off between explicit coordinate auditability and reuse of the abstract algebra hierarchy.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

Its module header explicitly describes rounding the rational quotient in both coordinates, proving

$$
|u^2+uv-v^2|\le\frac5{16}<1,
$$

using this to make the remainder absolute norm strictly smaller than the divisor's, and finally making `GoldenInt` a `EuclideanDomain`.

Japanese and English PDFs exist on the target branch, but the exact page or section corresponding to this instance was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

`goldenEuclideanDomain` closes the `GoldenEuclidean.lean` generated section.

The next declaration in dependency/source order is the first declaration of `SignedGoldenRamifierStripped.lean`, **0231 `SignedGoldenRamifierStrippedPacket`**:

```lean
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  exceptional : SignedSquareGoldenExceptionalPacket u v w
  alpha : GoldenInt
  beta : GoldenInt
  k : ℤ
  alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
  linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
  alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
  beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
  beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
  beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
  five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
  five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
  tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

By 0230, the Euclidean-domain infrastructure of the golden order is complete. Declaration 0231 returns to the exceptional FLT5 branch and packages the element `beta` obtained after stripping the unique visible ramified factor `tau` from the exceptional packet.
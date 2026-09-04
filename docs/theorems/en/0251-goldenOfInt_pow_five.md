# 0251 — `goldenOfInt_pow_five`

## Lean type

```lean
/-- Integer embedding respects fifth powers in the explicit golden API. -/
theorem goldenOfInt_pow_five (b : ℤ) :
    goldenOfInt (b ^ 5) = goldenPow (goldenOfInt b) 5 := by
  apply GoldenInt.ext
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
    ring
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

This is a `theorem` stating that the integer embedding `goldenOfInt : ℤ → GoldenInt` preserves fifth powers when expressed through the raw golden-order power API `goldenPow`.

## Mathematical statement

`goldenOfInt b` embeds an integer into the golden order by

$$
b \longmapsto b+0\varphi.
$$

Thus ordinary ring arithmetic gives

$$
(b^5)+0\varphi=(b+0\varphi)^5.
$$

The theorem exposes exactly this fact in the explicit coordinate model:

$$
\operatorname{goldenOfInt}(b^5)
=
\operatorname{goldenPow}(\operatorname{goldenOfInt}(b),5).
$$

The left-hand side has coordinates $(b^5,0)$. Repeated `goldenMul` on the right keeps the second coordinate equal to zero, while the first coordinate reduces to the ordinary integer fifth power.

## Role in the full proof

Declarations 0241–0250 construct the relative-primality certificate for `beta` and its conjugate and then expose the corresponding contradiction routing interfaces. Declaration 0251 begins `SignedGoldenFifthPower.lean`, where that relative primality is connected to fifth-power factor extraction.

A stripped packet already carries

$$
N(\beta)=b^5.
$$

Together with the general identity

$$
\beta\overline{\beta}=N(\beta),
$$

this yields an internal golden-order equality

$$
\beta\overline{\beta}=\operatorname{goldenOfInt}(b^5).
$$

The present theorem rewrites the right-hand side as

$$
\operatorname{goldenOfInt}(b)^5.
$$

Therefore the next theorem can state the standard factorization pattern

$$
\beta\overline{\beta}=z^5,
$$

with the two factors already known to be relatively prime. This is precisely the form needed by the generic coprime-factor theorem.

Thus 0251 is a representation bridge from an integer fifth power on the norm side to a genuine fifth power inside the golden order.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt`
- `GoldenInt.ext`
- 0162 `goldenOfInt`
- raw power `goldenPow`
- raw multiplication `goldenMul`
- `goldenOne`
- `simp`
- `ring`

The proof does not use an abstract cast theorem or `map_pow`; instead it unfolds the explicit coordinate definitions directly.

Conceptually,

$$
\text{integer embedding}
+
\text{explicit golden multiplication}
\Longrightarrow
\text{fifth-power preservation}.
$$

## Proof flow

The proof first applies extensionality for `GoldenInt`:

```lean
apply GoldenInt.ext
```

This reduces equality of golden integers to equality of their two integer coordinates.

### First coordinate

```lean
· simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
  ring
```

After unfolding the raw power and multiplication, all mixed terms involving the second coordinate vanish because the embedded integer has second coordinate zero. `simp` performs the definitional normalization, and `ring` closes the remaining integer polynomial identity.

### Second coordinate

```lean
· simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

The second coordinate of an embedded integer is zero and remains zero under all repeated multiplications, so `simp` alone closes this branch.

## Lean-specific processing

`goldenPow` is a raw recursive power function rather than the standard `Pow.pow`, although 0160 `golden_pow_eq` already connects it definitionally to standard exponentiation.

Likewise, `goldenOfInt` is a raw coordinate embedding, while the `AddGroupWithOne GoldenInt` instance already gives integer casts by the same coordinate rule $(b,0)$.

The current proof deliberately avoids those standard-API bridges and unfolds `goldenOfInt`, `goldenPow`, and `goldenMul` directly. This keeps the dependency surface local and auditable, but it also exposes some duplication between the raw API and Mathlib's standard ring API.

`GoldenInt.ext` is the key structural step: it reduces the structure equality to two ordinary integer equalities, and only the first coordinate requires `ring`.

## Redundancy and duplication

Mathematically, the theorem overlaps with the generic fact that ring casts preserve powers.

If a bridge theorem of the form

```lean
goldenOfInt b = (b : GoldenInt)
```

were available, then the standard statement

$$
((b^5 : \mathbb Z) : GoldenInt)=((b : GoldenInt))^5
$$

could likely be discharged almost entirely by the generic cast and power API.

Similarly, 0160 `golden_pow_eq` can rewrite `goldenPow x 5` to `x ^ 5`, so directly unfolding `goldenPow` here is comparatively low-level.

On the other hand, for a standalone auditable development the current coordinate proof has value: it visibly confirms that golden multiplication restricts to ordinary integer multiplication on the embedded integer axis.

## Optimization candidates

1. Add a bridge such as `goldenOfInt_eq_intCast` and prove the theorem through the standard cast API.
2. Reuse 0160 `golden_pow_eq` to avoid directly unfolding `goldenPow`.
3. Prove the more general statement

```lean
goldenOfInt (b ^ n) = goldenPow (goldenOfInt b) n
```

for arbitrary `n : ℕ`, then specialize to `n=5`.
4. Bundle `goldenOfInt` as a `RingHom ℤ GoldenInt` and derive the result with `map_pow`.

Because FLT5 only consumes exponent five downstream, the current specialized theorem is also a pragmatic way to keep dependencies small.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface used by this theorem is mainly:

- structure extensionality
- `simp`
- `ring`
- basic integer ring operations

No advanced number-theory API is required by the theorem itself. A much smaller import set than all of `Mathlib` is likely sufficient in isolation, but the true minimal import should be measured at the `SignedGoldenFifthPower.lean` module level because that module depends on the surrounding golden-order infrastructure.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The alternatives are particularly clear:

- A: current explicit-coordinate `ext + simp + ring` proof
- B: proof using `golden_pow_eq` and the standard cast API
- C: bundle `goldenOfInt` as a `RingHom` and use `map_pow`
- D: prove an arbitrary-exponent theorem and specialize to `5`

Useful comparison axes are proof size, dependency depth, visibility of the raw API, reuse of standard Mathlib abstractions, generalizability, and standalone auditability.

The contrast between A and C is especially useful: A proves the concrete FLT5 fact directly in coordinates, while C tests the benefits of exposing the integer embedding as a genuine ring homomorphism.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenFifthPower.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms that after the 0250 conjugate-coprime routing theorem, the generated source enters `SignedGoldenFifthPower.lean`, and this theorem is its first declaration.

The branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small API theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`**:

```lean
theorem SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenMul p.beta (goldenConj p.beta) =
      goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5 := by
  rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

Now that 0251 establishes compatibility between integer embedding and fifth powers, 0252 upgrades

$$
\beta\overline{\beta}=N(\beta)=b^5
$$

to the genuine fifth-power factorization inside the golden order

$$
\beta\overline{\beta}=(\operatorname{goldenOfInt} b)^5.
$$

This becomes the direct input to the generic coprime-factor extraction theorem.
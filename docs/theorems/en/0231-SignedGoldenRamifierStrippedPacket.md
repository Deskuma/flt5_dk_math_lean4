# 0231 — `SignedGoldenRamifierStrippedPacket`

## Lean type

```lean
/-- The exceptional packet after removing the unique visible ramifier `tau`. -/
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

This is a `structure`, not a theorem. It packages the complete state obtained after removing the visible ramified factor `tau = 2 + φ` exactly once from the signed FLT5 exceptional branch.

## Mathematical statement and meaning of the declaration

The central situation represented by the structure starts with the golden integer

$$
\alpha=M+N\varphi
$$

coming from the exceptional packet. A linear divisibility condition is recorded as

$$
2M+N=5k.
$$

Using the distinguished norm-five element

$$
\tau=2+\varphi,
$$

the packet stores a factorization

$$
\alpha=\tau\beta.
$$

The stripped element is explicitly

$$
\beta=(M-k)+(2k-M)\varphi,
$$

and its norm is already reduced to a pure fifth power:

$$
N(\beta)=b^5.
$$

Its second coordinate is also exposed explicitly:

$$
\beta_2=-5^7a^{10}.
$$

The packet additionally carries

$$
5\nmid b,
$$

$$
5\nmid N(\beta),
$$

and

$$
\tau\nmid\beta.
$$

Thus this is not merely a factorization record. It represents a **normalized state in which the visible ramified factor has been removed and certified not to remain inside `beta`**.

## Role in the full proof

By 0230 the development has completed the Euclidean-domain infrastructure for `GoldenInt`. Declaration 0231 returns to the exceptional FLT5 branch and packages the algebraic state that will be fed into fifth-power factor extraction.

The module header states that the preceding square/norm packet gives an element `alpha` with

$$
N(\alpha)=5b^5.
$$

Divisibility of the diagonal linear coordinate extracts the explicit ramifier `tau`, yielding

$$
\alpha=\tau\beta,
$$

and the stripped element then satisfies

$$
N(\beta)=b^5.
$$

Immediately downstream, `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` constructs an inhabitant of this structure. Choice-based APIs then transport the packet from an exceptional packet, from a five-adic power split, and directly from a signed normal form.

The next module, `SignedGoldenConjugateCoprime.lean`, uses `beta_norm`, `beta_snd`, and the five-free information to prove that every common divisor of `beta` and its conjugate is a unit, giving

$$
GoldenRelPrime(\beta,\overline\beta).
$$

That certificate is later used by fifth-power factor extraction to reach a representation of the form

$$
\beta=\varepsilon\gamma^5.
$$

Therefore 0231 is the main packet boundary between ramifier stripping and conjugate-coprime fifth-power extraction.

## Meaning of the fields

### `exceptional`

```lean
exceptional : SignedSquareGoldenExceptionalPacket u v w
```

Retains the complete upstream signed square-golden exceptional data. The coordinates `M`, `N`, the five-adic split, and the bases `a`, `b` remain accessible through this field.

### `alpha`

```lean
alpha : GoldenInt
```

The golden integer lifting the exceptional coordinates `(M,N)`.

### `beta`

```lean
beta : GoldenInt
```

The element remaining after the visible `tau` factor has been removed. This becomes the main object in the subsequent conjugate-coprime and fifth-power arguments.

### `k`

```lean
k : ℤ
```

The quotient witness for the linear divisibility relation

$$
2M+N=5k.
$$

### `alpha_eq`

```lean
alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
```

Fixes the correspondence between the abstract field `alpha` and the original integer coordinates.

### `linear_eq`

```lean
linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
```

Stores the integer linear relation used to extract a `goldenTau` factor.

### `alpha_eq_tau_mul`

```lean
alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
```

The central factorization certificate

$$
\alpha=\tau\beta.
$$

### `beta_eq`

```lean
beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
```

Provides explicit coordinates for the stripped element, allowing later arguments to reduce projections of `beta` to integer arithmetic.

### `beta_norm`

```lean
beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
```

Records the removal of the visible norm-five factor from the upstream identity `N(alpha)=5*b^5`.

### `beta_snd`

```lean
beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
```

This explicit second coordinate drives the later computation of the conjugate-difference norm

$$
N(\beta-\overline\beta)=-5^{15}a^{20}.
$$

### `five_not_dvd_b`

```lean
five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
```

Certifies that the residual fifth-power base `b` contains no factor of five.

### `five_not_dvd_beta_norm`

```lean
five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
```

Combines `beta_norm = b^5` with `5 ∤ b` to record that no factor of five remains in the norm of the stripped element.

### `tau_not_dvd_beta`

```lean
tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

Directly certifies that `beta` cannot be divided by `tau` again. If `beta = tau * gamma`, norm multiplicativity and `N(tau)=5` would imply `5 ∣ N(beta)`, contradicting the preceding field.

## Direct dependencies

The structure statement directly references:

- `SignedSquareGoldenExceptionalPacket`
- `GoldenInt`
- `goldenTau`
- `goldenMul`
- `goldenNorm`
- the power-split coordinates `a` and `b`
- divisibility on `ℕ` and `ℤ`

Because this is a structure declaration, it has no proof script of its own. The immediately following construction theorem fills its fields using, among other facts:

- `exists_goldenTau_factor_of_five_dvd`
- `goldenNorm_mul`
- `goldenNorm_tau`
- primality of `5` and `dvd_of_dvd_pow`
- upstream `golden_eq`, `tenth_boundary`, and five-adic residual facts

## Construction flow

Declaration 0231 specifies the certificate interface rather than proving one proposition. The following private existence theorem constructs the packet roughly as follows.

1. Set $A=2M+N$ and derive $5\mid A^2$ from the upstream discriminant identity.
2. Use primality of `5` to conclude $5\mid A$.
3. Apply `exists_goldenTau_factor_of_five_dvd` to construct `k`, `beta`, and
   $$
   \alpha=\tau\beta.
   $$
4. Use norm multiplicativity and `N(tau)=5` to obtain
   $$
   N(\beta)=b^5.
   $$
5. Combine the explicit `beta` coordinates with the upstream tenth-boundary relation to compute `beta_snd`.
6. Derive $5\nmid b$ from the five-adic residual condition.
7. Use `beta_norm` to deduce $5\nmid N(\beta)$.
8. Show that another `tau` factor would force $5\mid N(\beta)$, proving `tau_not_dvd_beta`.

The fields therefore form a sequence of cached certificates for one coherent ramifier-stripping argument rather than unrelated pieces of metadata.

## Lean-specific processing

Because the declaration is

```lean
structure ... : Type where
```

it defines a data type, not a proposition. Equalities and non-divisibility facts are stored as fields, so downstream theorems can access them directly as projections such as `p.beta_norm`, `p.beta_snd`, and `p.tau_not_dvd_beta`.

The first field is itself a dependent packet:

```lean
exceptional : SignedSquareGoldenExceptionalPacket u v w
```

and later field types refer to `exceptional.M` and `exceptional.powerSplit.b`. This dependent structure design guarantees that all cached certificates refer to exactly the same upstream exceptional packet.

The final field writes divisibility explicitly through raw multiplication:

```lean
¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

rather than using standard `¬ goldenTau ∣ beta`. Since `EuclideanDomain GoldenInt` has just been installed in 0230, a standard divisibility formulation is now also available as a possible API simplification.

## Redundancy and duplication

Several fields are logically derivable from others.

- `five_not_dvd_beta_norm` follows from `beta_norm` and `five_not_dvd_b`.
- `tau_not_dvd_beta` follows from `five_not_dvd_beta_norm`, `goldenNorm_mul`, and `goldenNorm_tau`.
- `alpha` could in principle be replaced everywhere by `⟨exceptional.M, exceptional.N⟩` because `alpha_eq` fixes that identity.
- `beta` could likewise be reconstructed from the coordinates stored in `beta_eq`.

A logically minimal packet could therefore contain fewer fields.

The current design, however, treats these as cached semantic milestones. This makes downstream proof code shorter and significantly improves auditability: important facts such as the exact norm, the exact second coordinate, and complete ramifier stripping can be accessed by one projection rather than rederived repeatedly.

## Optimization candidates

1. **Separate primitive and derived fields**
   - move `five_not_dvd_beta_norm` and `tau_not_dvd_beta` to theorems outside the structure and compare downstream proof cost.

2. **Reduce explicit `alpha` / `beta` fields**
   - define them from coordinates instead of storing coherence equalities; this reduces fields but lengthens projections.

3. **Use standard divisibility**
   - formulate the final certificate as `¬ goldenTau ∣ beta`, taking advantage of the Euclidean-domain instance established in 0230.

4. **Split the packet into stages**
   - one structure for factorization `alpha = tau * beta`, another for strippedness `5 ∤ N(beta)` and `tau ∤ beta`.

5. **Bundle exact fifth-power norm data**
   - replace the bare equality `beta_norm` with a dedicated predicate or structure expressing that the norm is an exact fifth power.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The structure declaration itself needs mostly project-local types and definitions plus basic divisibility propositions.

The surrounding `SignedGoldenRamifierStripped.lean` module, however, immediately uses prime divisibility, `norm_num`, `nlinarith`, `omega`, `ring`, integer casts, and norm multiplicativity when constructing the packet. Therefore the true minimal import set must be measured at module scope rather than from this structure alone.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Packet design gives a useful structural comparison.

Possible implementations include:

- A: the current proof-rich structure with derived certificates cached as fields;
- B: a minimal data structure plus derived theorem API;
- C: a normalized structure in which `alpha` and `beta` are computed from coordinates;
- D: a version using standard `Dvd.dvd`, `IsUnit`, and Euclidean-domain APIs throughout;
- E: separate staged packets for ramifier factorization and strippedness.

Useful metrics are field count, constructor proof size, downstream theorem size, coherence obligations, reusability, alignment with Mathlib's standard API, and audit readability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

Its module header explicitly describes the transition from an element `alpha` with norm `5*b^5` to a stripped element `beta` satisfying `N(beta)=b^5`, an explicit second coordinate, five-free norm, and the absence of another `tau` factor.

The branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this structure was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0232 `five_not_dvd_powerSplit_b`**:

```lean
private theorem five_not_dvd_powerSplit_b
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    ¬ 5 ∣ p.powerSplit.b := by
  ...
```

This private theorem extracts `5 ∤ b` from the known modulo-25 property of the five-adic residual. It is the first auxiliary certificate used to construct the `five_not_dvd_b` field of the packet introduced in 0231.

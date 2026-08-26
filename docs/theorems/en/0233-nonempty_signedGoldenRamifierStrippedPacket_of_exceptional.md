# 0233 — `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`

## Lean type

```lean
private theorem nonempty_signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    Nonempty (SignedGoldenRamifierStrippedPacket u v w) := by
  ...
```

This is a `private theorem`. It proves that a `SignedSquareGoldenExceptionalPacket u v w` gives rise to an inhabitant of the structure introduced in 0231, `SignedGoldenRamifierStrippedPacket u v w`.

It is an internal construction theorem rather than part of the public API. The immediately following declaration `signedGoldenRamifierStrippedPacket_of_exceptional` uses `Classical.choice` on this existence proof to select an actual packet for downstream use.

## Mathematical statement

The input packet `p` contains the exceptional-branch integer coordinates `M,N` together with an exact five-adic power split. Declaration 0233 constructs the golden integer

$$
\alpha=M+N\varphi
$$

and removes one visible copy of the ramifier

$$
\tau=2+\varphi
$$

by constructing a factorization

$$
\alpha=\tau\beta.
$$

The resulting `β` is then proved to satisfy every major certificate required by the structure from 0231:

$$
N(\beta)=b^5,
$$

$$
\beta_{\mathrm{snd}}=-5^7a^{10},
$$

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

Thus the theorem completes the normalization step saying that the visible ramified factor has been stripped exactly once and that the remaining factor is primitive with respect to five.

## Role in the full proof

Declaration 0231 defines the target packet structure, and 0232 establishes one of its crucial fields,

$$
5\nmid b,
$$

from the modulo-25 information in the five-adic residual.

Declaration 0233 is the central constructor theorem that integrates these ingredients. Conceptually, the proof follows the chain

$$
\text{exceptional packet}
\longrightarrow 5\mid(2M+N)
\longrightarrow \alpha=\tau\beta
\longrightarrow N(\beta)=b^5
\longrightarrow 5\nmid N(\beta)
\longrightarrow \tau\nmid\beta.
$$

Once this packet is available, the next module `SignedGoldenConjugateCoprime.lean` studies common divisors of `β` and its conjugate and eventually proves their relative primality. From there the Euclidean-domain and gcd infrastructure can be used to split fifth-power factors.

In other words, 0233 is the boundary theorem that converts five-adic exceptional data into a **ramifier-stripped primitive factor in the golden integer ring**.

## Direct dependencies

The main direct dependencies are:

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0232 `five_not_dvd_powerSplit_b`
- `SignedSquareGoldenExceptionalPacket`
- 0186 `exists_goldenTau_factor_of_five_dvd`
- 0174 `goldenNorm_mul`
- 0184 `goldenNorm_tau`
- 0172 `goldenNorm_eq_GoldenNorm`
- `goldenNorm`
- `goldenTau`
- `GoldenInt`
- `Prime.dvd_of_dvd_pow`
- `exact_mod_cast`
- `mul_left_cancel₀`
- `nlinarith`, `omega`, `ring`, and `norm_num`

On the input-packet side, the proof uses certificates including `p.discriminant_five_eq`, `p.golden_eq`, `p.tenth_boundary`, `p.powerSplit.b`, and `p.powerSplit.a`.

## Proof / construction flow

### 1. Introduce the linear quantity `A = 2M+N`

The proof starts with

```lean
let A : ℤ := 2 * p.M + p.N
```

and derives from the packet's discriminant relation

```lean
have hAeq : A ^ 2 = 5 * (p.N ^ 2 + 4 * (p.powerSplit.b : ℤ) ^ 5) := by
  dsimp [A]
  nlinarith [p.discriminant_five_eq]
```

Hence

$$
5\mid A^2.
$$

Since `5` is prime, the proof obtains

$$
5\mid A.
$$

Lean records this through

```lean
have h5sq : (5 : ℤ) ∣ A ^ 2 := ⟨_, hAeq⟩
have h5A : (5 : ℤ) ∣ A :=
  (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5sq
```

### 2. Extract a concrete `τ` factor

Using 0186, the divisibility condition `5 ∣ 2*M+N` is converted into witnesses:

```lean
rcases exists_goldenTau_factor_of_five_dvd h5A with
  ⟨k, beta, hk, hbeta, halpha⟩
```

This gives

$$
2M+N=5k,
$$

$$
\beta=\langle M-k,\,2k-M\rangle,
$$

and

$$
\langle M,N\rangle=\tau\beta.
$$

The proof then fixes

```lean
let alpha : GoldenInt := ⟨p.M, p.N⟩
```

as the golden integer represented by the exceptional packet.

### 3. Read the norm of `α` from the input packet

The packet certificate `p.golden_eq` is transported through the bridge theorem from 0172:

```lean
have hnormAlpha : goldenNorm alpha = 5 * (p.powerSplit.b : ℤ) ^ 5 := by
  simpa [alpha, goldenNorm_eq_GoldenNorm] using p.golden_eq
```

Thus

$$
N(\alpha)=5b^5.
$$

### 4. Prove `N(β)=b^5`

From `α=τβ` and norm multiplicativity,

$$
N(\alpha)=N(\tau)N(\beta)=5N(\beta).
$$

On the other hand,

$$
N(\alpha)=5b^5.
$$

Cancelling the integer factor `5` yields

$$
N(\beta)=b^5.
$$

The Lean proof uses `goldenNorm_mul goldenTau beta`, rewrites with 0184 `goldenNorm_tau`, and lets `omega` handle the final integer cancellation.

### 5. Derive the exact second coordinate of `β`

From the coordinate formula `hbeta`, the proof first establishes

$$
5\,\beta_{\mathrm{snd}}=-(M-2N).
$$

The packet certificate `p.tenth_boundary` rewrites

$$
M-2N=5^8a^{10}.
$$

Using the fact that `5 ≠ 0`, Lean cancels one factor of five and obtains

$$
\beta_{\mathrm{snd}}=-5^7a^{10}.
$$

The source uses

```lean
apply (mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0))
```

so that the proof can establish an equality after multiplying both sides by `5` and then cancel.

### 6. Reuse 0232 to obtain `5 ∤ b`

The preceding private theorem is imported directly into the construction:

```lean
have h5b : ¬ 5 ∣ p.powerSplit.b := five_not_dvd_powerSplit_b p
```

### 7. Prove `5 ∤ N(β)`

Assume for contradiction that

$$
5\mid N(\beta).
$$

After rewriting with `hnormBeta`, this gives

$$
5\mid b^5.
$$

Primality of `5` then implies

$$
5\mid b,
$$

contradicting `h5b`.

Lean first obtains divisibility in `ℤ` via `Prime.dvd_of_dvd_pow` and then uses

```lean
exact_mod_cast
```

to transport `(5 : ℤ) ∣ (b : ℤ)` back to the natural-number statement `5 ∣ b`.

### 8. Exclude a second `τ` factor

Finally suppose

$$
\beta=\tau\gamma.
$$

Norm multiplicativity and `N(τ)=5` give

$$
N(\beta)=5N(\gamma),
$$

and hence

$$
5\mid N(\beta),
$$

contradicting `h5norm`.

The corresponding Lean fragment is very short:

```lean
have htau : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma := by
  rintro ⟨gamma, hgamma⟩
  apply h5norm
  use goldenNorm gamma
  rw [hgamma, goldenNorm_mul, goldenNorm_tau]
```

### 9. Assemble the structure

All witnesses and certificates are finally inserted into the 0231 structure and wrapped as a `Nonempty` witness:

```lean
exact ⟨{
  exceptional := p
  alpha := alpha
  beta := beta
  k := k
  alpha_eq := rfl
  linear_eq := hk
  alpha_eq_tau_mul := halpha
  beta_eq := hbeta
  beta_norm := hnormBeta
  beta_snd := hsnd
  five_not_dvd_b := h5b
  five_not_dvd_beta_norm := h5norm
  tau_not_dvd_beta := htau }⟩
```

## Lean-specific processing

This theorem crosses several domain boundaries, so its Lean-specific surface is substantial.

1. `let A : ℤ := ...` together with `dsimp [A]` introduces a local integer expression and exposes it to `nlinarith`.
2. `Prime.dvd_of_dvd_pow` pulls prime divisibility back from a square or fifth power.
3. `rcases` simultaneously expands the multiple existential witnesses returned by 0186.
4. `simpa [alpha, goldenNorm_eq_GoldenNorm] using p.golden_eq` bridges the older two-variable norm API and the `GoldenInt` norm API.
5. `mul_left_cancel₀` performs explicit cancellation using the nonzeroness of the integer `5`.
6. `exact_mod_cast` transports divisibility between `ℤ` and `ℕ`.
7. The final `Nonempty` value is constructed by wrapping an explicit structure literal with `⟨...⟩`.

Mathematically the theorem is one ramifier-stripping argument, but Lean makes the interfaces among natural numbers, integers, golden integers, and existential packet data explicit.

## Redundancy and duplication

### 1. Two-stage `Nonempty` plus `Classical.choice`

The next declaration is

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional ... :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

so the implementation separates an existence theorem from the selected object. This is a standard proof/data separation, although much of the witness construction inside 0233 is explicit. It is worth checking whether a more directly functional factor-extraction API could reduce the later reliance on choice.

### 2. Both `5 ∤ b` and `5 ∤ N(β)` are cached

Since `N(β)=b^5` is already stored, the second fact is derivable from the first. Keeping both fields is logically redundant but convenient for downstream proofs that operate directly on norms.

### 3. `τ ∤ β` is also derivable from the norm certificate

Because `N(τ)=5`, `tau_not_dvd_beta` follows from `five_not_dvd_beta_norm` and norm multiplicativity. Again this is cached redundancy that makes the packet more consumer-friendly.

## Optimization candidates

1. **Generalize ramifier stripping**
   - a generic lemma deriving `τ ∤ β` from `α=τβ`, `N(τ)=p`, and `p∤N(β)` could remove local repetition.

2. **Factor out the norm-primitivity chain**
   - the step `N(β)=b^5` plus `5∤b` implies `5∤N(β)` could be a standalone helper.

3. **Minimize packet fields**
   - `five_not_dvd_beta_norm` and `tau_not_dvd_beta` could be external theorems rather than stored fields, leaving only primitive data in the structure.

4. **Reduce choice through an explicit constructor API**
   - if the factor extraction performed by 0186 were exposed as a function rather than only an existential theorem, the later `Classical.choice` layer might be reducible.

5. **Compare with valuation-based proofs**
   - the modulo-25 and prime-divisibility chain could potentially be expressed with valuation APIs. The current approach, however, has shallow dependencies and strong auditability.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The main Mathlib surface directly used by this theorem includes:

- `Prime.dvd_of_dvd_pow`
- `mul_left_cancel₀`
- `exact_mod_cast`
- `nlinarith`
- `omega`
- `ring`
- `norm_num`
- `Nonempty`
- existential and conjunction elimination

Golden-order-specific results such as `goldenNorm_mul`, `goldenNorm_tau`, and the factor extraction theorem 0186 are upstream DkMath declarations.

The theorem in isolation should require less than all of `Mathlib`, but the complete `SignedGoldenRamifierStripped.lean` module crosses five-adic packets, integer divisibility, and golden-order arithmetic. Exact import minimization therefore requires a Lean build. No build is run in this museum pass, so this remains an optimization candidate only.

## Comparator challenge suitability

Yes. Declaration 0233 offers several substantially different proof architectures.

Possible contestants are:

- A: current explicit divisibility, norm, and coordinate construction
- B: a valuation-centered ramifier-stripping proof
- C: a Euclidean-domain proof using `Associated`, prime-element, or gcd APIs
- D: a minimal packet structure with derived certificates moved to external theorems
- E: an explicit factor-extraction function designed to reduce `Classical.choice`

Useful metrics include proof size, dependency depth, computability, visibility of mathematical provenance, downstream API ergonomics, elaboration stability, and auditability of the five-adic argument.

The contrast between A and C is particularly interesting because 0230 has just established `EuclideanDomain GoldenInt`; 0233 tests whether that newly available abstract infrastructure should already replace some of the explicit arithmetic.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

This run confirmed directly from the source that the private theorem appears immediately after 0232 and is followed by

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional ... :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

Japanese and English PDFs are known to exist on the target branch from prior museum passes. GitHub code search returned a transient 502 during this run and the exact PDF page/section was not re-identified, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is **0234 `signedGoldenRamifierStrippedPacket_of_exceptional`**:

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

Declaration 0233 proves that the packet exists. Declaration 0234 moves from that `Nonempty` proof to an object-level API by selecting a canonical representative for downstream definitions and theorems through `Classical.choice`.

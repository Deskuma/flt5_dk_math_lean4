# 0243 — `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`

## Lean type

```lean
/-- The packet coordinate makes the conjugate-difference norm explicit. -/
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

This is a `theorem`. It specializes the generic conjugate-difference norm formula from 0242 using the explicit second-coordinate certificate stored in 0231 `SignedGoldenRamifierStrippedPacket`.

## Mathematical statement

Declaration 0242 proves for every golden integer $x=a+b\varphi$ that

$$
N(x-\overline{x})=-5b^2.
$$

A ramifier-stripped packet stores

$$
p.\beta_{\mathrm{snd}}=-5^7a^{10},
$$

where $a$ denotes `p.exceptional.powerSplit.a` after coercion to `ℤ`.

Substituting this coordinate gives

$$
N(\beta-\overline{\beta})
=-5\left(-5^7a^{10}\right)^2
=-5^{15}a^{20}.
$$

The theorem exposes this exact integer mass identity as a named API fact.

## Role in the full proof

The purpose of `SignedGoldenConjugateCoprime.lean` is to prove that the stripped element `beta` and its conjugate are relatively prime in the golden order.

If a common divisor `d` divides both `beta` and `goldenConj beta`, then 0191 `goldenDivides_sub` gives

$$
d\mid(\beta-\overline{\beta}).
$$

Using 0192 `goldenNorm_dvd_of_goldenDivides`, one obtains integer divisibility

$$
N(d)\mid N(\beta)
$$

and

$$
N(d)\mid N(\beta-\overline{\beta}).
$$

The packet already stores

$$
N(\beta)=b^5.
$$

The present theorem supplies the second mass as

$$
N(\beta-\overline{\beta})=-5^{15}a^{20}.
$$

In the immediately following theorem 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`, the source uses the coprimality of $b^5$ and $5^{15}a^{20}$ to force the natural absolute value of the common-divisor norm to be `1`, and then concludes that the divisor is a `GoldenUnit`.

Thus 0243 is the **second integer-mass certificate** needed to transport the common-divisor problem from the golden order to ordinary integer coprimality.

## Direct dependencies

The Lean proof directly uses only:

- 0242 `goldenNorm_sub_conj`
- 0231 `SignedGoldenRamifierStrippedPacket.beta_snd`
- `ring`

The statement also depends on:

- `SignedGoldenRamifierStrippedPacket`
- `GoldenInt`
- `goldenNorm`
- `goldenConj`
- `p.beta`
- `p.exceptional.powerSplit.a`

Conceptually, the theorem is simply the composition of

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2
$$

with

$$
\beta_{\mathrm{snd}}=-5^7a^{10}.
$$

## Proof flow

The entire proof is:

```lean
rw [goldenNorm_sub_conj, p.beta_snd]
ring
```

1. `goldenNorm_sub_conj` rewrites the left-hand side to

$$
-5\cdot p.\beta_{\mathrm{snd}}^2.
$$

2. `p.beta_snd` replaces the second coordinate by

$$
-5^7a^{10}.
$$

3. `ring` normalizes the remaining integer power expression to

$$
-5^{15}a^{20}.
$$

Mathematically this is exactly

$$
-5(-5^7a^{10})^2
=-5\cdot5^{14}a^{20}
=-5^{15}a^{20}.
$$

## Lean-specific processing

The theorem is namespace-qualified as

```lean
SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
```

so for a packet `p` downstream code can use the method-style form

```lean
p.norm_sub_conj_eq.
```

In

```lean
rw [goldenNorm_sub_conj, p.beta_snd]
```

the first rewrite specializes the generic theorem to `x := p.beta`, while the second rewrite consumes the packet-specific coordinate certificate.

The final `ring` works entirely in `ℤ`, normalizing signs, multiplication, and natural-number powers. No divisibility, valuation, or gcd reasoning is needed here because 0242 and the packet field have already isolated all nontrivial mathematical information.

## Redundancy and duplication

Logically, 0243 is a direct specialization of 0242 and adds no new general law. Downstream code could repeat

```lean
rw [goldenNorm_sub_conj, p.beta_snd]
ring
```

instead of naming the result.

Keeping the theorem is nevertheless useful API redundancy:

- downstream relative-primality proofs do not need to reopen packet coordinate algebra;
- the exact five-adic mass attached to the conjugate difference is directly searchable by theorem name;
- the three-layer API becomes clear: 0241 generic factorization, 0242 generic norm identity, 0243 packet specialization;
- consumers remain insulated if the internal representation of `beta_snd` later changes.

One design cost is that both `p.beta_snd` and this theorem explicitly expose large powers of the same parameter `a`. A more abstract packet based on valuation or prime-support certificates could reduce representation coupling.

## Optimization candidates

1. **Keep the current specialization theorem**

   The proof is only two lines and clearly separates generic algebra from packet-specific arithmetic.

2. **Add an absolute-value / `natAbs` consumer lemma**

   The next theorem ultimately needs the positive mass

$$
5^{15}a^{20}.
$$

A theorem such as

```lean
(goldenNorm (...)).natAbs = 5 ^ 15 * ...
```

could reduce later sign handling and uses of `Int.dvd_neg`.

3. **Add a valuation certificate**

   Besides the exact equality, a named theorem describing the `5`-adic valuation or prime support could make the later coprimality argument more explicit.

4. **Regularize the 0241–0243 namespace API**

   A consistent naming scheme for generic factorization, generic norm identity, and packet specialization would improve discoverability.

5. **Compare storing derived mass data directly in the packet**

   The current design stores `beta_snd` as primary data and derives the mass identity. An alternative packet could store the consumer-facing mass certificate directly.

The current implementation is already locally optimal in proof length and preserves clear mathematical provenance.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself directly needs only a small Mathlib surface:

- equality rewriting via `rw`
- polynomial normalization via `ring`

Its main dependencies are project-local declarations 0242 and the stripped-packet structure.

The declaration alone should require much less than the whole of `Mathlib`, but the surrounding `SignedGoldenConjugateCoprime.lean` module soon uses `Nat.Coprime`, integer divisibility, `natAbs`, casts, and `omega`. Therefore import minimization should be measured at module scope rather than from 0243 in isolation.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current `rw [goldenNorm_sub_conj, p.beta_snd]; ring`
- B: a `calc` proof making every mathematical step explicit
- C: a direct coordinate proof unfolding `goldenNorm`, `goldenConj`, and `beta_snd`
- D: a `norm_num` / `ring_nf` centered closed arithmetic proof
- E: proving a `natAbs` or valuation certificate directly as the consumer-facing API

Useful comparison axes are proof size, dependency depth, visibility of mathematical provenance, amount of definitional unfolding, sign/cast burden in 0244, and API stability.

The A-versus-E comparison is especially instructive: it measures whether the public API should center the **mathematically natural signed norm identity** or the **nonnegative mass certificate most convenient for downstream divisibility**.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0242 and immediately before

```lean
theorem SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    GoldenRelPrime p.beta (goldenConj p.beta) := by
  ...
```

The exact page or section in the existing Japanese and English PDFs corresponding to this internal theorem was not identified in this pass, so no PDF page number is inferred.

## Next declaration to read

The next declaration in dependency order is **0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`**.

That theorem takes an arbitrary common divisor `d` and derives

$$
N(d)\mid b^5
$$

and

$$
N(d)\mid -5^{15}a^{20}.
$$

Using the coprimality certificate stored in the power-split packet, it forces

$$
|N(d)|=1,
$$

and the unit-by-norm criterion then proves `GoldenUnit d`.

Thus 0244 is the central theorem that collects the conjugate-difference machinery from 0241–0243 and completes

$$
GoldenRelPrime(\beta,\overline{\beta}).
$$
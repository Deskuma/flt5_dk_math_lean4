# 0244 — `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`

## Lean type

```lean
/-- Every common divisor of a stripped element and its conjugate is a unit. -/
theorem SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    GoldenRelPrime p.beta (goldenConj p.beta) := by
  intro d hdbeta hdconj
  have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
    goldenDivides_sub hdbeta hdconj
  have hnormBeta : goldenNorm d ∣ goldenNorm p.beta :=
    goldenNorm_dvd_of_goldenDivides hdbeta
  have hnormDiff : goldenNorm d ∣
      goldenNorm (p.beta - goldenConj p.beta) :=
    goldenNorm_dvd_of_goldenDivides hddiff
  have hdB : (goldenNorm d).natAbs ∣ p.exceptional.powerSplit.b ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [p.beta_norm] using hnormBeta
  have hdA : (goldenNorm d).natAbs ∣
      5 ^ 15 * p.exceptional.powerSplit.a ^ 20 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm d ∣
        (5 ^ 15 * p.exceptional.powerSplit.a ^ 20 : ℕ) := by
      exact Int.dvd_neg.mp (by simpa [p.norm_sub_conj_eq] using hnormDiff)
    exact_mod_cast hpos
  have hab := p.exceptional.powerSplit.coprime_b5_scaled_a20
  have habs : Nat.Coprime (p.exceptional.powerSplit.b ^ 5)
      (5 ^ 15 * p.exceptional.powerSplit.a ^ 20) := hab
  have hone : (goldenNorm d).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes habs hdB hdA
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega
```

This is a `theorem`. It proves that the stripped element `beta` stored in 0231 `SignedGoldenRamifierStrippedPacket` is relatively prime, in the golden-order sense, to its conjugate `goldenConj beta`.

## Mathematical statement

Declaration 0208 `GoldenRelPrime` defines

$$
GoldenRelPrime(x,y)
$$

by the Bézout-free condition

$$
\forall d,\quad d\mid x\land d\mid y\Longrightarrow d\text{ is a unit}.
$$

The present theorem proves

$$
GoldenRelPrime(\beta,\overline\beta)
$$

for the stripped packet element `beta`.

Let $d$ be a common divisor. Since $d$ divides both `beta` and `conj beta`, it also divides their difference:

$$
d\mid\beta,\qquad d\mid\overline\beta
\Longrightarrow
d\mid(\beta-\overline\beta).
$$

Declaration 0192 `goldenNorm_dvd_of_goldenDivides` transports golden divisibility to divisibility of integer norms:

$$
N(d)\mid N(\beta),
$$

$$
N(d)\mid N(\beta-\overline\beta).
$$

The stripped packet stores

$$
N(\beta)=b^5,
$$

while 0243 establishes

$$
N(\beta-\overline\beta)=-5^{15}a^{20}.
$$

Therefore the natural number $|N(d)|$ divides both

$$
b^5
$$

and

$$
5^{15}a^{20}.
$$

The power-split packet already carries

$$
\gcd\!\left(b^5,5^{15}a^{20}\right)=1
$$

as `coprime_b5_scaled_a20`. Hence any natural number dividing both masses must be `1`, so

$$
|N(d)|=1.
$$

For an integer norm this means

$$
N(d)=1\quad\text{or}\quad N(d)=-1.
$$

Declaration 0201 `goldenUnit_of_norm_eq_one_or_neg_one` then shows that `d` is a `GoldenUnit`. Thus every common divisor is a unit, which is exactly the definition of relative primality.

## Role in the full proof

This theorem is the central result of `SignedGoldenConjugateCoprime.lean`. The module comment itself states the intended argument: a common divisor of `beta` and `conj(beta)` divides both the fifth-power norm mass

$$
N(\beta)=b^5
$$

and the conjugate-difference mass

$$
N(\beta-\overline\beta)=-5^{15}a^{20}.
$$

Power-split coprimality then forces the common divisor to have norm `±1`, hence to be a unit.

Declarations 0231–0243 can be read as preparation for this result:

- the stripped packet stores `beta_norm : N(beta)=b^5`;
- 0191 `goldenDivides_sub` transports a common divisor to the conjugate difference;
- 0192 transports golden divisibility to integer norm divisibility;
- 0241–0243 make the conjugate-difference norm an exact five-adic mass;
- the power-split packet supplies coprimality of `b^5` and `5^15*a^20`;
- 0201 converts norm `±1` back into a golden unit.

The resulting `GoldenRelPrime` certificate is a key hypothesis for the later fifth-power factor extraction. In the authoritative source, `p.beta_relPrime_conj` is passed directly to `GoldenCoprimeFactorOfFifthPower` in order to obtain a representation of the form

$$
\beta=\varepsilon\gamma^5.
$$

## Direct dependencies

The principal direct dependencies are:

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0208 `GoldenRelPrime`
- 0187 `GoldenDivides`
- 0191 `goldenDivides_sub`
- 0192 `goldenNorm_dvd_of_goldenDivides`
- packet field `p.beta_norm`
- 0243 `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`
- `SignedFiveAdicPowerSplit.coprime_b5_scaled_a20`
- `Int.dvd_natCast.mp`
- `Int.dvd_neg.mp`
- `Nat.eq_one_of_dvd_coprimes`
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- `omega`

Conceptually,

$$
\text{common divisor}
\to
\text{divides }N(\beta)\text{ and }N(\beta-\overline\beta)
\to
|N(d)|\mid b^5,\ 5^{15}a^{20}
\to
|N(d)|=1
\to
N(d)=\pm1
\to
GoldenUnit(d).
$$

## Proof flow

### 1. Receive an arbitrary common divisor

```lean
intro d hdbeta hdconj
```

This is the expanded shape of the `GoldenRelPrime` goal: an arbitrary `d` is assumed to divide both arguments.

### 2. Move the common divisor to the conjugate difference

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

This is the golden-order wrapper for the standard fact that a common divisor divides a difference.

### 3. Project divisibility to integer norms

```lean
have hnormBeta : goldenNorm d ∣ goldenNorm p.beta :=
  goldenNorm_dvd_of_goldenDivides hdbeta
```

and

```lean
have hnormDiff : goldenNorm d ∣
    goldenNorm (p.beta - goldenConj p.beta) :=
  goldenNorm_dvd_of_goldenDivides hddiff
```

transport the ring-theoretic divisibility statements to `ℤ`.

### 4. Convert to natural-number divisibility through `natAbs`

The proof of `hdB` uses `p.beta_norm` to obtain

$$
|N(d)|\mid b^5.
$$

The proof of `hdA` uses the signed identity from 0243, removes the minus sign through `Int.dvd_neg.mp`, and reconciles casts to obtain

$$
|N(d)|\mid5^{15}a^{20}.
$$

### 5. Collapse the common divisor of coprime masses to `1`

```lean
have hone : (goldenNorm d).natAbs = 1 :=
  Nat.eq_one_of_dvd_coprimes habs hdB hdA
```

This is the arithmetic core of the proof. The previously established power-split coprimality forces the absolute norm of every common divisor to be exactly `1`.

### 6. Return from norm `±1` to a unit

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
omega
```

`omega` converts `natAbs = 1` into the signed integer alternative `N(d)=1 ∨ N(d)=-1`, and 0201 closes the unit goal.

## Lean-specific processing

The proof crosses three representation layers:

1. `GoldenDivides` on `GoldenInt`;
2. divisibility of `goldenNorm` values in `ℤ`;
3. divisibility and coprimality of `Int.natAbs` values in `ℕ`.

`Int.dvd_natCast.mp` is the bridge from integer divisibility to natural-number divisibility of absolute values. `exact_mod_cast` reconciles the `ℤ` / `ℕ` coercions in the scaled five-adic mass.

`Int.dvd_neg.mp` removes the sign in the identity

$$
N(\beta-\overline\beta)=-M
$$

so the proof can work with the positive natural mass $M=5^{15}a^{20}$.

The final `omega` step classifies an integer whose natural absolute value is `1` as either `1` or `-1`.

## Redundancy and duplication

The mathematics is coherent, but there is some API friction in the path

$$
\mathbb Z\to\operatorname{natAbs}\to\mathbb N\to\{\pm1\}.
$$

Both `hdB` and `hdA` perform essentially the same operation: transport integer norm divisibility to natural-number divisibility. A helper such as

```lean
goldenNorm_natAbs_dvd_of_goldenDivides
```

could hide this conversion once.

Likewise, the final sequence

```lean
have hone : (goldenNorm d).natAbs = 1 := ...
apply goldenUnit_of_norm_eq_one_or_neg_one
omega
```

could be compressed by a theorem saying directly that `natAbs (goldenNorm d) = 1` implies `GoldenUnit d`.

The present form, however, has high auditability because every arithmetic interface is explicit.

## Optimization candidates

1. Add a helper returning `(goldenNorm d).natAbs ∣ (goldenNorm x).natAbs` directly from `GoldenDivides d x`.
2. Add `goldenUnit_of_natAbs_norm_eq_one` to hide the final sign classification.
3. Connect `GoldenUnit` with Mathlib `IsUnit` and reuse standard algebra APIs.
4. Bundle absolute norm as a multiplicative map into `ℕ`, making divisibility transport more generic.
5. Package the two masses `beta_norm` and `norm_sub_conj_eq` together with their coprimality as a dedicated certificate.

There is a trade-off: too much abstraction could hide the FLT5-specific five-adic structure that the current proof exposes very clearly.

## Required Mathlib imports and import optimization

The standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. The direct Mathlib surface of this theorem includes integer and natural divisibility, `Nat.Coprime`, coercion machinery, and the `omega` tactic.

Because the repository stores a flattened generated artifact, the exact minimal imports of the original standalone module cannot be read directly from a separate source file here. The manifest order places `SignedGoldenConjugateCoprime.lean` after the golden divisibility and ramifier-stripped layers.

No Lean build is performed in this museum pass, so an exact minimized import set remains unverified. It is plausible that the module could use substantially narrower imports than all of `Mathlib`, together with its upstream DkMath modules.

## Comparator challenge suitability

Yes. Three especially clear implementations can be compared:

- A: the current `GoldenDivides → ℤ divisibility → natAbs → Nat.Coprime` proof;
- B: a proof using gcd / Euclidean-domain APIs more directly;
- C: a proof in which absolute norm is bundled as a multiplicative map and relative primality is derived through generic image lemmas.

Useful comparison axes include proof size, number of coercion steps, dependence on `omega` / `exact_mod_cast`, visibility of mathematical provenance, portability to a general quadratic order, and whether the FLT5-specific five-adic masses remain easy to audit.

This theorem is therefore a strong Comparator challenge for explicit arithmetic versus abstract algebraic infrastructure.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The module comment explicitly describes the strategy: a common divisor divides both `N(beta)=b^5` and the conjugate-difference norm `-5^15*a^20`; power-split coprimality then forces norm `±1`, hence a golden unit. The present theorem is the direct Lean implementation of that strategy.

The branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0245 `SignedGoldenConjugateCoprimePacket`**:

```lean
/-- A packet retaining the stripped data and certified conjugate coprimality. -/
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

Now that 0244 provides the relative-primality certificate, 0245 packages the stripped data and that certificate into one structure. Later fifth-power extraction can therefore consume a certified conjugate-coprime state without rebuilding the argument.

# 0387 `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`

## Declaration kind

`theorem`

This theorem lives in the `GoldenZeroSectorDescentPacket` namespace and is the central re-entry result that turns the zero-sector descent input into an **honest fifth power**.

## Lean code

```lean
/-- The re-entry element is an honest fifth power; all nonzero unit sectors die mod five. -/
theorem exists_lift_eq_fifthPower (p : GoldenZeroSectorDescentPacket) :
    ∃ gamma : GoldenInt,
      goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
      goldenNorm gamma = (p.D : ℤ) := by
  have hmul :
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
        goldenPow (goldenOfInt (p.D : ℤ)) 5 := by
    calc
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
          goldenOfInt (goldenFifthSndFactor p.base.fst p.base.snd) :=
        goldenZeroSectorLift_mul_conj p.base
      _ = goldenOfInt ((p.D : ℤ) ^ 5) := by rw [p.H_eq]
      _ = goldenPow (goldenOfInt (p.D : ℤ)) 5 :=
        goldenOfInt_pow_five (p.D : ℤ)
  obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ :=
    goldenCoprimeFactorOfFifthPower
      (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base))
      (goldenOfInt (p.D : ℤ)) p.lift_relPrime_conj hmul
  obtain ⟨i, delta, hdelta⟩ :=
    goldenUnitClassesModFifth epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : goldenZeroSectorLift p.base =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hfactor, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  have hFiveAlpha : (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd := by
    rw [goldenZeroSectorLift_snd]
    rcases p.snd_eq with hs | hs
    · exact dvd_pow (by rw [hs]; exact dvd_mul_right 5 _)
        (by decide : 2 ≠ 0)
    · exact dvd_pow (by rw [hs]; exact dvd_neg.mpr (dvd_mul_right 5 _))
        (by decide : 2 ≠ 0)
  have hThetaNorm : ¬ (5 : ℤ) ∣ goldenNorm theta := by
    intro h5theta
    apply p.five_not_dvd_H
    rw [← goldenZeroSectorLift_norm p.base, hSector, goldenNorm_mul]
    apply dvd_mul_of_dvd_right
    change (5 : ℤ) ∣ goldenNorm (theta ^ 5)
    rw [goldenNorm_pow]
    exact dvd_pow h5theta (by decide : 5 ≠ 0)
  have hi : i = 0 := by
    by_contra hi
    exact hThetaNorm
      (five_dvd_norm_of_nonzero_goldenUnitSector hi hSector hFiveAlpha)
  subst i
  have hroot : goldenZeroSectorLift p.base = goldenPow theta 5 := by
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  refine ⟨theta, hroot, ?_⟩
  have hn := congrArg goldenNorm hroot
  rw [goldenZeroSectorLift_norm, p.H_eq, golden_pow_eq,
    goldenNorm_pow] at hn
  exact (show Odd 5 by decide).pow_injective hn.symm
```

## Lean type

Conceptually, the theorem has the following type.

```lean
GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower :
  (p : GoldenZeroSectorDescentPacket) →
  ∃ gamma : GoldenInt,
    goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
    goldenNorm gamma = (p.D : ℤ)
```

The only input is a descent packet `p`. The theorem constructs a golden integer `gamma` and proves two properties simultaneously.

1. The quadratic re-entry element is exactly the fifth power of `gamma`.
2. The golden norm of `gamma` is the packet parameter `D`.

Thus the conclusion is stronger than a factorization by a unit times a fifth power: the unit-sector ambiguity has been completely removed.

## Mathematical statement

Write `p.base=(r,s)` and let

$$
\alpha=T(r,s)=\operatorname{goldenZeroSectorLift}(r,s)
$$

be the quadratic re-entry element.

The packet contains the invariant

$$
H(r,s)=D^5,
$$

and the lift norm identity gives

$$
N(\alpha)=H(r,s)=D^5.
$$

Equivalently, multiplication by the conjugate yields

$$
\alpha\overline{\alpha}=D^5.
$$

By 0385 `lift_relPrime_conj`, `alpha` and `conj alpha` are relatively prime in the golden integer ring. The existing fifth-power factorization theorem therefore gives

$$
\alpha=\varepsilon\gamma^5
$$

for a golden unit `epsilon`.

The classification of units modulo fifth powers lets us absorb an additional unit fifth power into the base and normalize the factorization to

$$
\alpha=\varphi^i\theta^5,
\qquad i\in\operatorname{Fin}5.
$$

On the other hand, the second coordinate of the lift is

$$
\alpha_{\mathrm{snd}}=s^2.
$$

Since the packet also gives

$$
s=\pm5t^5,
$$

we have

$$
5\mid\alpha_{\mathrm{snd}}.
$$

If `i ≠ 0`, then 0386 `five_dvd_norm_of_nonzero_goldenUnitSector` forces

$$
5\mid N(\theta).
$$

But `theta^5` is a factor in `alpha`; divisibility of its norm by 5 would force the norm of `alpha`, hence `H(r,s)`, to be divisible by 5, contradicting 0381 `five_not_dvd_H`.

Therefore

$$
i=0,
$$

so that

$$
\alpha=\theta^5.
$$

Taking norms gives

$$
D^5=N(\alpha)=N(\theta)^5.
$$

Because the exponent 5 is odd, fifth powering is injective on the integers, hence

$$
N(\theta)=D.
$$

## Role in the full proof

This theorem is a major **bridge** in the zero-sector descent.

Before this point, the available ingredients are separate:

- the lift and its conjugate are relatively prime;
- the lift norm is a fifth power;
- golden units are classified into five classes modulo fifth powers;
- nonzero sectors are incompatible with the five-adic condition.

0387 combines all of these ingredients and establishes for the first time the recursively useful form

$$
T(r,s)=\gamma^5.
$$

Once this is available, the next theorem `fifthRoot_snd_factor_eq` projects the equality to the second coordinate and obtains

$$
s^2
 = 5\,\gamma_{\mathrm{snd}}\,
   H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

That identity then feeds the subsequent positivity, coprimality, power splitting, and strict measure decrease arguments used to construct the next descent packet.

Thus 0387 is precisely the theorem that removes the unit ambiguity and makes the infinite descent recursive again.

## Direct dependencies

The main project-local declarations used directly by this theorem are:

- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorLift`
- `goldenZeroSectorLift_mul_conj`
- `goldenZeroSectorLift_norm`
- `goldenConj`
- `goldenMul`
- `goldenPow`
- `goldenOfInt`
- `goldenOfInt_pow_five`
- `GoldenZeroSectorDescentPacket.H_eq`
- `GoldenZeroSectorDescentPacket.snd_eq`
- `GoldenZeroSectorDescentPacket.lift_relPrime_conj`
- `GoldenZeroSectorDescentPacket.five_not_dvd_H`
- `goldenCoprimeFactorOfFifthPower`
- `goldenUnitClassesModFifth`
- `goldenPhi`
- `goldenPhi_pow_zero`
- `goldenNorm_mul`
- `goldenNorm_pow`
- `five_dvd_norm_of_nonzero_goldenUnitSector`

The Mathlib-facing features visibly used in the proof include:

- existential and tuple destructuring via `obtain`
- `rw`
- `simp only` / `simpa`
- `ring`
- `dvd_pow`
- `dvd_neg.mpr`
- `dvd_mul_right`
- `dvd_mul_of_dvd_right`
- `congrArg`
- `Odd.pow_injective`
- `decide`

## Proof / construction flow

1. Build `hmul`, expressing the lift times its conjugate as a fifth power.

   Using `goldenZeroSectorLift_mul_conj` together with `p.H_eq`, the proof constructs the golden-integer identity corresponding to

   $$
   \alpha\overline\alpha=D^5.
   $$

2. Apply `goldenCoprimeFactorOfFifthPower`.

   The relative-prime fact `p.lift_relPrime_conj` and `hmul` yield

   ```lean
   obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ := ...
   ```

   providing a unit `epsilon`, a fifth-power base `gamma`, the unit proof, and the factorization.

3. Classify `epsilon` with `goldenUnitClassesModFifth`.

   This gives

   $$
   \varepsilon=\varphi^i\delta^5.
   $$

4. Define `theta := delta * gamma` and absorb the two fifth-power factors.

   The theorem `hSector` establishes

   $$
   \alpha=\varphi^i\theta^5.
   $$

   Lean unfolds the coordinate-level multiplication and power equations and closes the resulting polynomial identity with `ring`.

5. Prove `hFiveAlpha`.

   `goldenZeroSectorLift_snd` identifies the second coordinate of the lift with `s^2`. In both sign branches of `p.snd_eq`, the integer `s` is divisible by 5, hence so is its square.

6. Prove `hThetaNorm : ¬ 5 ∣ N(theta)`.

   If `5 ∣ N(theta)`, multiplicativity of the norm and `hSector` would imply divisibility of the lift norm by 5, contradicting `p.five_not_dvd_H`.

7. Show that the sector index is zero.

   Assuming `i ≠ 0`, theorem 0386 gives `5 ∣ N(theta)`, immediately contradicting `hThetaNorm`.

8. Substitute `i = 0`.

   Since `phi^0=1`, `hSector` simplifies to

   $$
   \alpha=\theta^5.
   $$

9. Apply `goldenNorm` to both sides with `congrArg`.

   Rewriting by the lift norm identity, `p.H_eq`, and norm-of-power gives

   $$
   D^5=N(\theta)^5.
   $$

10. Use `Odd.pow_injective` for exponent 5.

    This yields

    $$
    N(\theta)=D,
    $$

    and `theta` is returned as the witness.

## Lean-specific processing

### Structural unpacking with `obtain`

The factorization theorem and unit-classification theorem return several witnesses and proofs, so the proof uses

```lean
obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ := ...
obtain ⟨i, delta, hdelta⟩ := ...
```

to unpack all existential data at once.

### `let theta := ...`

The unit fifth-power part `delta^5` is absorbed into the existing `gamma^5` by introducing

```lean
let theta := goldenMul delta gamma
```

which formalizes the mathematical identity

$$
\delta^5\gamma^5=(\delta\gamma)^5.
$$

### `simp only [...]` followed by `ring`

The abstract `GoldenInt` multiplication and power operations are reduced to coordinate ring expressions with

```lean
simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
ring
```

so that the ring normalizer can close the identity.

### Handling the signed `snd_eq`

The packet allows both `+5t^5` and `-5t^5`. Only divisibility is needed here, so the negative branch removes the sign with

```lean
dvd_neg.mpr
```

and then lifts divisibility to the square using `dvd_pow`.

### `change` for representation alignment

Inside `hThetaNorm`, the proof aligns the displayed goal with the norm of a fifth power using

```lean
change (5 : ℤ) ∣ goldenNorm (theta ^ 5)
```

before applying `goldenNorm_pow`.

### `congrArg goldenNorm`

The equality of golden integers `hroot` is mapped through the norm function using

```lean
have hn := congrArg goldenNorm hroot
```

reducing the final stage to an equality of integer fifth powers.

### `Odd.pow_injective`

Even powers are not injective over the integers because they erase signs. The proof therefore explicitly supplies that 5 is odd:

```lean
(show Odd 5 by decide)
```

and then invokes `pow_injective` safely.

## Redundancy / duplication

The two branches in `hFiveAlpha` differ only by the sign in `p.snd_eq`; both establish the same divisibility statement. A packet-level lemma asserting

$$
5\mid s
$$

or directly

$$
5\mid(\operatorname{goldenZeroSectorLift}(p.base)).snd
$$

would remove this local case split.

The argument in `hThetaNorm` is also a reusable pattern: divisibility of the norm of the fifth-power factor propagates to divisibility of the full lift norm. This could be factored into a helper theorem.

By contrast, the explicit `ring` step in `hSector` keeps the algebraic normalization auditable and is not necessarily undesirable in a theorem-museum setting.

## Optimization candidates

1. **A `five_dvd_lift_snd` helper**

   A packet-level theorem returning

   ```lean
   (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd
   ```

   would separate sign bookkeeping from the core sector-exclusion argument.

2. **A unit-absorption lemma**

   A general theorem turning

   ```lean
   epsilon = phi^i * delta^5
   alpha = epsilon * gamma^5
   ```

   into

   ```lean
   alpha = phi^i * (delta * gamma)^5
   ```

   would hide the local `simp only ...; ring` normalization.

3. **Packet-level sector exclusion**

   One could combine 0386 with `hThetaNorm` into a theorem that returns `i = 0` directly for a descent packet. However, keeping 0386 packet-independent is valuable for reuse, so the present separation is also well motivated.

4. **A norm-root extraction helper**

   The final step from `D^5 = N(theta)^5` to `N(theta)=D` is generic odd-power injectivity and could be wrapped in a small helper lemma.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

The theorem itself visibly needs divisibility APIs, the simplifier, `ring`, integer powers, `Odd.pow_injective`, and basic decidability machinery, while the substantial golden-order declarations come from earlier project modules included in the standalone source.

It is likely possible to replace the umbrella `Mathlib` import by a smaller collection of algebra/divisibility/tactic modules. However, this task does not run a Lean build, so the **minimal import set is not verified**. No specific minimal module list should therefore be asserted as established fact.

## Suitability as a Comparator challenge

**Yes. It naturally splits into several useful challenge levels.**

Three especially good subchallenges are:

1. construct `hmul` and select the correct coprime-factorization API to obtain `alpha = epsilon * gamma^5`;
2. combine unit classification with theorem 0386 to force `i = 0`;
3. finish with `congrArg goldenNorm` and odd-power injectivity to prove `N(theta)=D`.

The second is particularly suitable because it tests composition of several nontrivial prior lemmas rather than merely polynomial normalization.

Using the entire theorem as a single challenge would introduce many project-local dependencies. For Comparator, a reduced environment with the preceding declarations fixed would likely be more informative.

## Next declaration to read

The next declaration is

```lean
theorem fifthRoot_snd_factor_eq
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    p.base.snd ^ 2 =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := by
  have h := congrArg (fun x : GoldenInt => x.snd) hroot
  change (goldenZeroSectorLift p.base).snd =
    (goldenPow gamma 5).snd at h
  rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
    goldenFifthSndPoly_eq] at h
  exact h
```

Now that 0387 has established

$$
T(r,s)=\gamma^5,
$$

the next theorem **projects only the second coordinate** and obtains

$$
s^2
 = 5\,\gamma_{\mathrm{snd}}\,
   H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

This product identity is the entry point for the later positivity, coprimality, fifth-power splitting, and strict measure-decrease arguments.
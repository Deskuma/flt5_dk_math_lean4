# 0386 `five_dvd_norm_of_nonzero_goldenUnitSector`

## Declaration kind

`theorem`

This is a packet-independent unit-sector arithmetic lemma placed outside the `GoldenZeroSectorDescentPacket` namespace.

## Lean code

```lean
/--
A nonzero unit sector cannot have second coordinate divisible by five while
the fifth-power base has norm prime to five.  This is the packet-independent
form of the sector calculation used by the original zero-sector reduction.
-/
theorem five_dvd_norm_of_nonzero_goldenUnitSector
    {alpha gamma : GoldenInt} {i : Fin 5}
    (hi : i ≠ 0)
    (hAlpha : alpha =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5))
    (hFive : (5 : ℤ) ∣ alpha.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
  apply five_dvd_goldenNorm_of_five_dvd_fifthFst
  fin_cases i
  · exact (hi rfl).elim
  · rw [hAlpha, golden_unit_one_mul_fifth_snd] at hFive
    have h := dvd_sub hFive hS
    ring_nf at h
    exact h
  · rw [hAlpha, golden_unit_two_mul_fifth_snd] at hFive
    have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
    ring_nf at h
    exact h
  · rw [hAlpha, golden_unit_three_mul_fifth_snd] at hFive
    have h2F : (5 : ℤ) ∣
        2 * goldenFifthFstPoly gamma.fst gamma.snd := by
      have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 3)
      ring_nf at h ⊢
      exact h
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F with h52 | hF
    · norm_num at h52
    · exact hF
  · rw [hAlpha, golden_unit_four_mul_fifth_snd] at hFive
    have h3F : (5 : ℤ) ∣
        3 * goldenFifthFstPoly gamma.fst gamma.snd := by
      have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 5)
      ring_nf at h ⊢
      exact h
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h3F with h53 | hF
    · norm_num at h53
    · exact hF
```

## Lean type

Conceptually, the full type is

```lean
five_dvd_norm_of_nonzero_goldenUnitSector :
  {alpha gamma : GoldenInt} → {i : Fin 5} →
  i ≠ 0 →
  alpha = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5) →
  (5 : ℤ) ∣ alpha.snd →
  (5 : ℤ) ∣ goldenNorm gamma
```

The inputs are golden integers `alpha`, `gamma`, together with a unit-sector index `i : Fin 5`. The three hypotheses are:

1. `hi : i ≠ 0`
2. `hAlpha : alpha = goldenPhi^i * gamma^5`
3. `hFive : 5 ∣ alpha.snd`

The conclusion is

```lean
(5 : ℤ) ∣ goldenNorm gamma
```

## Mathematical statement

Place a golden integer in a fifth-power unit sector:

$$
\alpha = \varphi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}.
$$

The theorem says that in a nonzero sector

$$
i\neq0,
$$

if the second coordinate satisfies

$$
5\mid \alpha_{\mathrm{snd}},
$$

then the norm of the fifth-power base `gamma` must be divisible by 5:

$$
5\mid N(\gamma).
$$

The core of the proof is to write the two coordinate polynomials of `gamma^5` as

$$
F=\operatorname{goldenFifthFstPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}),
$$

$$
S=\operatorname{goldenFifthSndPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}).
$$

The already established fact

$$
5\mid S
$$

is combined with the sector-specific coordinate formula for `alpha.snd`. In every nonzero sector one can extract

$$
5\mid F.
$$

The existing bridge

$$
5\mid F \Longrightarrow 5\mid N(\gamma)
$$

then finishes the proof.

## Role in the overall proof

By 0385 `lift_relPrime_conj`, the quadratic re-entry element and its conjugate are relatively prime in the golden integer ring. The following theorem `exists_lift_eq_fifthPower` can therefore apply `goldenCoprimeFactorOfFifthPower` and obtain a factorization

$$
\alpha=\varepsilon\gamma^5.
$$

Next, `goldenUnitClassesModFifth` classifies the unit `epsilon` into five sectors modulo fifth powers. After absorbing an additional fifth-power factor, the re-entry element has the form

$$
\alpha=\varphi^i\theta^5,
\qquad i\in\operatorname{Fin}5.
$$

The second coordinate of the zero-sector lift is the square of the original second coordinate. Since the packet carries

$$
s=\pm5t^5,
$$

one obtains

$$
5\mid \alpha_{\mathrm{snd}}.
$$

If `i ≠ 0`, the present theorem forces

$$
5\mid N(\theta).
$$

The packet side, however, keeps the relevant quartic/norm quantity 5-adically clean. The subsequent proof turns this into a contradiction and eliminates every nonzero sector. Hence only

$$
i=0
$$

remains, giving the honest fifth power

$$
\alpha=\theta^5.
$$

Thus 0386 is the sector-exclusion kernel that upgrades a general `unit × fifth power` factorization into the pure fifth power required by zero-sector descent.

## Direct dependencies

The main project declarations used directly by this theorem are:

- `GoldenInt`
- `goldenMul`
- `goldenPow`
- `goldenPhi`
- `goldenNorm`
- `goldenFifthFstPoly`
- `goldenFifthSndPoly`
- `five_dvd_goldenFifthSndPoly`
- `five_dvd_goldenNorm_of_five_dvd_fifthFst`
- `golden_unit_one_mul_fifth_snd`
- `golden_unit_two_mul_fifth_snd`
- `golden_unit_three_mul_fifth_snd`
- `golden_unit_four_mul_fifth_snd`

The main Mathlib facilities directly visible in the proof are:

- `Fin 5`
- `fin_cases`
- `dvd_sub`
- `dvd_mul_of_dvd_right`
- `Prime.dvd_mul`
- `ring_nf`
- `norm_num`

## Proof flow

1. Obtain the universal divisibility of the second-coordinate fifth-power polynomial:

   ```lean
   hS : (5 : ℤ) ∣ goldenFifthSndPoly gamma.fst gamma.snd
   ```

   via

   ```lean
   have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
   ```

2. Reduce the final goal `5 ∣ goldenNorm gamma` to divisibility of the first-coordinate fifth-power polynomial:

   ```lean
   apply five_dvd_goldenNorm_of_five_dvd_fifthFst
   ```

   The remaining conceptual target is

   $$
   5\mid F.
   $$

3. Exhaustively split `i : Fin 5` into the five cases 0,1,2,3,4 with `fin_cases i`.

4. The `i=0` branch immediately contradicts `hi : i ≠ 0`:

   ```lean
   exact (hi rfl).elim
   ```

5. For `i=1`, rewrite `alpha.snd` using `golden_unit_one_mul_fifth_snd`. Subtract the known divisible quantity `S` from `hFive`, normalize with `ring_nf`, and obtain `5 ∣ F` directly.

6. For `i=2`, do the same but subtract `2*S`, matching the coefficient in the sector formula:

   ```lean
   dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
   ```

7. For `i=3`, subtraction gives

   $$
   5\mid2F.
   $$

   Since 5 is prime,

   $$
   5\mid2 \quad\text{or}\quad 5\mid F.
   $$

   `norm_num` eliminates the first alternative, leaving `5 ∣ F`.

8. For `i=4`, the same argument yields

   $$
   5\mid3F,
   $$

   and `5 ∤ 3` leaves `5 ∣ F`.

9. Every nonzero sector has now established `5 ∣ F`, so the initial application of `five_dvd_goldenNorm_of_five_dvd_fifthFst` produces

   $$
   5\mid N(\gamma).
   $$

## Lean-specific processing

### `Fin 5` and `fin_cases`

The sector index is stored as the finite type `Fin 5` rather than a natural number plus a range hypothesis. Therefore

```lean
fin_cases i
```

produces exactly the five exhaustive cases.

This directly encodes the mathematical classification into five unit sectors modulo fifth powers.

### Rewriting inside `hFive`

The sector coordinate formulas are needed inside the hypothesis

```lean
hFive : (5 : ℤ) ∣ alpha.snd
```

rather than in the goal. Hence the proof uses forms such as

```lean
rw [hAlpha, golden_unit_three_mul_fifth_snd] at hFive
```

to replace `alpha.snd` by the explicit sector polynomial.

### Linear combinations of divisibility facts

`dvd_sub` and `dvd_mul_of_dvd_right` implement the elementary fact that the difference of two multiples of 5 is again a multiple of 5.

For example, in sector 2:

```lean
have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
```

cancels the unwanted `S` component.

### `ring_nf at h ⊢`

The expression obtained after subtracting sector formulas is not syntactically identical to the required `F`, `2*F`, or `3*F`. `ring_nf` normalizes the integer polynomial expressions.

### `Prime.dvd_mul`

Sectors 3 and 4 produce a small coefficient times `F`, so Euclid's lemma is used in the form

```lean
(show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F
```

The impossible alternatives `5 ∣ 2` and `5 ∣ 3` are discharged by `norm_num`, leaving `5 ∣ F`.

## Redundancy and duplication

The four nonzero sectors have the same broad structure:

- rewrite `hFive` with `hAlpha` and a sector-specific snd formula;
- subtract an appropriate integer multiple of `hS`;
- normalize with `ring_nf`;
- when needed, cancel a small coefficient to obtain `5 ∣ F`.

There is therefore visible tactic-level repetition.

That repetition is also useful for auditability: the exact arithmetic of each of the four sectors remains explicit. In particular, sectors 3 and 4 require prime cancellation through `2*F` and `3*F`, whereas sectors 1 and 2 close more directly. The branches are therefore similar but not perfectly uniform.

For a theorem museum, the current explicit split is defensible redundancy rather than merely accidental duplication.

## Optimization candidates

1. **Abstract the sector coefficient table**

   If the four `golden_unit_*_mul_fifth_snd` theorems can be represented by one formula indexed by `i : Fin 5`, much of the repeated branch code could be shortened.

   The abstraction cost may exceed the benefit for this single theorem, so this is not automatically an improvement.

2. **Factor out cancellation of 5 against small coefficients**

   The steps from `5 ∣ 2*F` and `5 ∣ 3*F` to `5 ∣ F` could be hidden behind a coprimality/cancellation lemma instead of explicit `Prime.dvd_mul` case splits.

3. **Separate the first-coordinate divisibility lemma**

   The arithmetic core could be exposed as a lemma such as

   ```lean
   nonzero_sector_five_dvd_fifthFst
   ```

   with the norm bridge applied afterward. This is useful only if `5 ∣ F` itself is reused elsewhere; for the currently visible main use, the present direct norm-divisibility endpoint is concise.

4. **Automate the finite branches**

   A compressed proof using something close to `fin_cases i <;> simp_all [...]` may be possible. However, sectors 3 and 4 still require prime cancellation, so whether such compression preserves clarity has not been verified.

## Required Mathlib import and import optimization candidates

The current stand-alone canonical source begins with

```lean
import Mathlib
```

and this theorem is written in that environment.

The Mathlib functionality directly visible in this theorem mainly consists of finite case splitting (`fin_cases`), integer divisibility and primality, `ring_nf`, and `norm_num`.

A narrower import set could potentially be assembled from modules providing:

- finite case-splitting for `Fin`;
- `ring_nf`;
- `norm_num`;
- integer prime/divisibility APIs.

However, the stand-alone artifact concatenates all preceding project definitions into one file. The **exact minimal Mathlib import set** for this theorem cannot be established from source inspection alone. Because no Lean build is performed in this task, any narrower import set remains an unverified optimization candidate.

For reproducing the museum code exactly as it currently stands, `import Mathlib` is the verified entry point.

## Comparator challenge feasibility

**Yes. This is a particularly suitable local challenge.**

The statement is compact and the proof burden is concentrated in finite sector classification plus elementary divisibility arithmetic.

### Lightweight challenge

Provide the following dependencies as established lemmas:

- `five_dvd_goldenFifthSndPoly`
- `five_dvd_goldenNorm_of_five_dvd_fifthFst`
- the four `golden_unit_*_mul_fifth_snd` formulas

and leave only the present theorem as the hole.

This tests selection of `Fin 5` case analysis, divisibility linear combinations, prime cancellation, and polynomial normalization.

### Stronger challenge

Move some of the sector-specific coordinate formulas into the challenge as well. That raises the difficulty substantially because the solver must then handle golden-integer multiplication/power coordinate arithmetic rather than merely consume those formulas.

For Comparator, the lightweight form is better suited to measuring mathematical branch selection: the case space is finite, but the nonzero sectors have slightly different cancellation patterns and cannot all be closed by one completely uniform trivial step.

## Next declaration to read

The next declaration returns to the `GoldenZeroSectorDescentPacket` namespace:

```lean
/-- The re-entry element is an honest fifth power; all nonzero unit sectors die mod five. -/
theorem exists_lift_eq_fifthPower (p : GoldenZeroSectorDescentPacket) :
    ∃ gamma : GoldenInt,
      goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
      goldenNorm gamma = (p.D : ℤ) := by
  ...
```

Its declaration kind is `theorem`.

It is the first theorem that combines the relative-prime factorization from 0385 with the nonzero-sector obstruction proved in 0386, producing the honest fifth-power re-entry

$$
\operatorname{goldenZeroSectorLift}(p.base)=\gamma^5.
$$

It also fixes the norm exactly as

$$
N(\gamma)=D,
$$

which prepares the coordinates for construction of the next descent packet.

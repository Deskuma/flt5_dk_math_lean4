# 0272 — `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`

## Declaration kind

This declaration is a **`theorem`**.

0271 `SignedGoldenUnitFifthPowerExclusion` only fixed the reusable proposition expressing that a packet's `beta` cannot be a unit times a fifth power. The present theorem actually constructs that contract from

- the mod-fifth unit classification `GoldenUnitClassesModFifth`,
- the zero-sector exclusion `SignedGoldenZeroSectorExclusion`, and
- the already established nonzero-sector exclusion.

## Lean type

```lean
/-- Unit classification plus the zero-sector theorem excludes every unit-times-fifth-power. -/
theorem signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
    (hClasses : GoldenUnitClassesModFifth)
    (hZero : SignedGoldenZeroSectorExclusion) :
    SignedGoldenUnitFifthPowerExclusion := by
  intro u v w p epsilon gamma hepsilon hbeta
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hbeta, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  by_cases hi : i = 0
  · subst i
    apply hZero p theta
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  · exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

Mathematically, the type reads

$$
\text{GoldenUnitClassesModFifth}
\land
\text{SignedGoldenZeroSectorExclusion}
\Longrightarrow
\text{SignedGoldenUnitFifthPowerExclusion}.
$$

Thus, if every golden unit is represented modulo fifth powers by one of

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4,
$$

and the zero sector is impossible, then every unit-times-fifth-power representation of a packet's `beta` is impossible.

## Mathematical meaning

`GoldenUnitClassesModFifth` says that every unit $\epsilon$ admits a representation

$$
\epsilon=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

Assume the contradiction input

$$
\beta=\epsilon\gamma^5.
$$

Substituting the unit classification gives

$$
\beta
=\varphi^i\delta^5\gamma^5
=\varphi^i(\delta\gamma)^5.
$$

Define

$$
\theta:=\delta\gamma.
$$

The problem is then reduced to the finite-sector normal form

$$
\beta=\varphi^i\theta^5,
\qquad i\in\mathrm{Fin}(5).
$$

Only two cases remain.

- If $i=0$, then $\varphi^0=1$, so $\beta=\theta^5$. This is excluded by `hZero`.
- If $i\neq0$, then the sector is one of $1,2,3,4$, and `signedGolden_nonzero_unitSector_false` excludes it.

Hence all unit-times-fifth-power possibilities are closed.

## Role in the full proof

This theorem is the **closure point of the finite-sector decomposition** in the signed golden branch.

Conceptually, the preceding development has the following architecture.

1. Classify golden units modulo fifth powers by the finite representatives $\varphi^i$.
2. Compute the second coordinates in sectors $1$ through $4$.
3. Compare them with the packet's five-adic second-coordinate invariant and eliminate every nonzero sector.
4. Delegate sector $0$ to the independent zero-sector arithmetic/descent argument.
5. Recombine the two routes here and produce `SignedGoldenUnitFifthPowerExclusion`.

The theorem therefore introduces no new local number-theoretic calculation. Its role is to glue the finite unit classification and the zero-sector theorem together into a single contradiction API that later layers can reuse.

## Direct dependencies

### `GoldenUnitClassesModFifth`

The canonical source defines it as

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

The proof consumes this classification directly through

```lean
obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
```

### `SignedGoldenZeroSectorExclusion`

The canonical source defines

```lean
abbrev SignedGoldenZeroSectorExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (gamma : GoldenInt),
    p.beta = goldenPow gamma 5 → False
```

It excludes the pure fifth-power case in sector $0$.

### `SignedGoldenUnitFifthPowerExclusion`

This is the conclusion contract introduced in 0271:

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

### `signedGolden_nonzero_unitSector_false`

This theorem eliminates sectors $1$ through $4$ in one step. The nonzero branch of the present proof simply delegates to it:

```lean
exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

### `goldenPhi_pow_zero`

This reduces the zero representative to

$$
\varphi^0=1.
$$

It is used to turn `hSector` into a pure fifth-power equation in the zero branch.

### `goldenMul`, `goldenPow`, `golden_mul_eq`, `golden_pow_eq`

These are the project-side golden arithmetic API and its bridge to the underlying ring operations. Together with `mul_pow`, they justify

$$
\delta^5\gamma^5=(\delta\gamma)^5.
$$

## Proof flow

### 1. Expand the exclusion contract

```lean
intro u v w p epsilon gamma hepsilon hbeta
```

Because 0271 is a transparent `abbrev`, Lean can introduce the quantified arguments of `SignedGoldenUnitFifthPowerExclusion` directly.

The relevant hypotheses are

```lean
hepsilon : GoldenUnit epsilon
hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)
```

### 2. Classify the unit into a finite sector

```lean
obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
```

This produces

```lean
i : Fin 5
delta : GoldenInt
hdelta : epsilon =
  goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

### 3. Absorb the fifth-power factor

```lean
let theta := goldenMul delta gamma
```

Mathematically, this is $\theta=\delta\gamma$.

### 4. Build the sector normal form

```lean
have hSector : p.beta =
    goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
  rw [hbeta, hdelta]
  simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
  ring
```

The proof substitutes the unit classification, lowers the project arithmetic notation to ring operations, combines fifth powers using `mul_pow`, and finishes the harmless reassociation/commutation by `ring`.

### 5. Split into zero and nonzero sectors

```lean
by_cases hi : i = 0
```

Rather than performing five explicit `fin_cases`, the proof makes exactly the distinction required by the architecture: sector $0$ versus sectors $1$–$4$.

### 6. Zero sector

```lean
· subst i
  apply hZero p theta
  simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
```

After substituting $i=0$, `hSector` simplifies to

$$
\beta=\theta^5,
$$

which is precisely the input required by `hZero`.

### 7. Nonzero sectors

```lean
· exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

All arithmetic for sectors $1$–$4$ is delegated to the existing theorem.

The fact that this branch closes in one line confirms that the preceding sector arithmetic has formed a useful abstraction boundary.

## Lean-specific processing

### Transparency of `abbrev`

The target is named `SignedGoldenUnitFifthPowerExclusion`, yet no explicit `unfold` is required before `intro`. This is a consequence of defining the contract as a transparent `abbrev : Prop`.

### `obtain`

The nested existential

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

is unpacked in one step.

### `let theta`

The repeated product `delta * gamma` is given a local mathematical name, which lets the same fifth-power base be passed cleanly to both the zero-sector and nonzero-sector theorems.

### Lowering from the project API to the ring API

```lean
simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
ring
```

converts `goldenMul` / `goldenPow` to ordinary multiplication / powers and performs algebraic normalization.

### `by_cases hi : i = 0`

Although `i : Fin 5`, the proof intentionally avoids a five-way case split. The existing nonzero-sector theorem already handles four cases at once, so the two-way split reflects the mathematical proof structure more faithfully.

### `subst i`

In the zero branch this replaces the finite representative by the concrete exponent `0`, after which `goldenPhi_pow_zero` finishes the reduction.

## Redundancy and duplication

The proof is already compact and has little internal redundancy.

In particular, it does not repeat the coordinate calculations for sectors $1$–$4`; these are delegated to `signedGolden_nonzero_unitSector_false`.

There is, however, a small structural duplication in the construction of `hSector`. The same normalization pattern

$$
\epsilon=\varphi^i\delta^5,
\qquad
\epsilon\gamma^5=\varphi^i(\delta\gamma)^5
$$

also appears in a nearby finite-sector core theorem in the canonical standalone source. That theorem similarly obtains `i` and `delta`, chooses `goldenMul delta gamma`, rewrites the unit classification, invokes `mul_pow`, and closes by `ring`.

This suggests a possible helper lemma converting a unit-times-fifth-power representation into canonical `Fin 5` sector form. Because the current proofs are short, such an abstraction should only be introduced if the pattern occurs in enough downstream locations to justify the extra API surface.

## Optimization candidates

### 1. Extract a sector-normalization helper

A helper of the conceptual form

```lean
lemma unitFifthPower_to_sector
    (hClasses : GoldenUnitClassesModFifth)
    (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    ∃ i : Fin 5, ∃ theta : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := ...
```

could remove duplication between this theorem and the finite-sector core.

### 2. Possibly avoid `ring`

If the commutative-ring structure of `GoldenInt` is exposed conveniently enough, the normalization might be closed by targeted rewrites using `mul_pow`, associativity, and commutativity instead of `ring`.

The current `ring` proof is nevertheless clear and robust, so this is a low-priority optimization.

### 3. Preserve the zero/nonzero split

Replacing the two-way `by_cases` with `fin_cases i` would expand the proof and duplicate the existing sector theorem. It would not be an optimization.

### 4. Keep the local name `theta`

Inlining `goldenMul delta gamma` everywhere would make both branches harder to read. The local definition is mathematically appropriate.

## Required Mathlib imports and import-optimization candidates

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the manifest identifies this theorem as belonging to the `DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean` section.

The proof directly uses Lean/Mathlib functionality including

- `Fin 5`,
- existential elimination via `obtain`,
- local definitions via `let`,
- equality rewriting (`rw`, `subst`),
- `by_cases`,
- `simp` / `simpa`,
- `mul_pow`, and
- the `ring` tactic.

Thus `ring` is a genuine tactic dependency of this proof as written.

The repository snapshot available here is a generated standalone concatenation. It does not establish the minimal imports of the original `SignedGoldenSectorArithmetic.lean` module independently, so the exact minimal Mathlib import set is **not confirmed**.

An import minimization pass would have to replace the umbrella `Mathlib` import with the required algebra, `Fin`, tactic, and project modules and then verify compilation. No Lean build is performed in this task, so no unverified minimal import list is claimed.

## Comparator challenge suitability

**Yes; this is a good Comparator challenge.**

It is more valuable than using the 0271 `abbrev` alone because the short proof exercises several proof-design skills:

1. unpacking an existential unit classification,
2. absorbing two fifth powers into one,
3. building a finite-sector normal form,
4. splitting zero from nonzero sectors, and
5. reusing a downstream contradiction theorem instead of reproving arithmetic.

A good challenge can expose the statement together with

```lean
hClasses : GoldenUnitClassesModFifth
hZero : SignedGoldenZeroSectorExclusion
signedGolden_nonzero_unitSector_false
goldenPhi_pow_zero
```

and ask for the proof body.

For a harder version, hide the introduction of `theta` and the intermediate statement `hSector`. Hiding the definitions of the major contracts themselves would shift the task too far toward API discovery rather than proof construction.

## Relation to the PDFs

The target branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`.

In this run the GitHub PDF binaries could not be retrieved in a form suitable for inspecting their contents. Therefore the exact PDF page, section number, and one-to-one prose correspondence for this theorem are **not confirmed**, and no such mapping is guessed here.

The technical account in this document is grounded primarily in the canonical Lean source on the target branch and its explicit generated source-module boundary.

## Next declaration to read

Immediately after this theorem, the canonical Lean source ends the `SignedGoldenSectorArithmetic.lean` section and begins `SignedGoldenZeroSector.lean`.

The next declaration in dependency order is

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

0272 completes the boundary at which all nonzero unit sectors are closed and only the zero sector remains. The next declaration begins the arithmetic-invariant development used to eliminate that remaining zero sector.
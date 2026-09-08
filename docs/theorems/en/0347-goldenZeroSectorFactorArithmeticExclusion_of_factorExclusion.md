# 0347 — `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

## Declaration kind

This declaration is a **`theorem`**.

```lean
/-- Excluding the three exact factor packets excludes every original zero-sector
candidate.  `SignedGoldenClosure` identifies this contract definitionally with its
public zero-sector arithmetic exclusion. -/
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
  rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
  let source := goldenZeroSectorCandidate_of_raw r s a b
    ha hb hab h5b hNorm hProduct hrs c d hsAbs hHAbs
  exact hFactor (goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket source))
```

## Lean type

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion
```

Assuming the packet-level exclusion from 0345,

```lean
GoldenZeroSectorFactorExclusion
```

that is,

```lean
GoldenZeroSectorFactorPacket → False
```

we obtain the raw arithmetic contract from 0346,

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

Because 0346 is an `abbrev`, its chain of universal quantifiers and implications is transparently exposed during elaboration, so the proof can `intro` the raw data and assumptions directly.

## Mathematical statement

Mathematically, the theorem says that once every certified factor packet has been excluded, every raw zero-sector arithmetic configuration is excluded as well.

The raw side consists of integers $r,s$, naturals $a,b$, and assumptions including

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1,\qquad 5\nmid b,
$$

$$
\operatorname{goldenNorm}(r,s)=\pm b,
$$

$$
s\,\operatorname{goldenFifthSndFactor}(r,s)=-5^6a^{10},
$$

$$
\gcd(|r|,|s|)=1,
$$

and witnesses $c,d\in\mathbb N$ such that

$$
|s|=5^6c^{10},
\qquad
|\operatorname{goldenFifthSndFactor}(r,s)|=d^{10}.
$$

The theorem repackages these assumptions into a `GoldenZeroSectorCandidate`, sends it through the already established inversion-packet and factor-packet pipeline, and finally applies `hFactor` to obtain `False`.

## Role in the overall proof

This theorem is the **public bridge** of the zero-sector factorization layer.

Earlier declarations already provide a certified pipeline

$$
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}.
$$

Downstream closure code, however, wants the exclusion statement in raw arithmetic-contract form.

Declaration 0347 connects the two layers as

$$
\text{factor-packet exclusion}
\Longrightarrow
\text{raw arithmetic exclusion}.
$$

Thus it proves no new arithmetic lemma. Its purpose is architectural: it composes previously proved constructors in one direction and closes the dependency boundary.

## Direct dependencies

The project declarations referenced directly are:

- `GoldenZeroSectorFactorExclusion`
- `GoldenZeroSectorFactorArithmeticExclusion`
- `goldenZeroSectorCandidate_of_raw`
- `goldenZeroSectorInversionPacket`
- `goldenZeroSectorFactorPacket_of_inversion`

The dependency flow is

```text
goldenZeroSectorCandidate_of_raw
  → goldenZeroSectorInversionPacket
  → goldenZeroSectorFactorPacket_of_inversion
  → hFactor
```

Definitions such as `goldenNorm`, `goldenFifthSndFactor`, `Nat.Coprime`, and `Int.natAbs` occur inside the expanded type of the raw contract, but the proof script does not invoke separate arithmetic lemmas about them.

## Proof flow

1. Use `intro` to receive every variable and assumption from the raw arithmetic contract.
2. Destructure `hsplit` with `rcases`, obtaining the tenth-power witnesses `c,d` and equalities `hsAbs`, `hHAbs`.
3. Feed all raw data to `goldenZeroSectorCandidate_of_raw` and define `source : GoldenZeroSectorCandidate`.
4. Build the inversion certificate with `goldenZeroSectorInversionPacket source`.
5. Build the certified exact factor packet with `goldenZeroSectorFactorPacket_of_inversion`.
6. Apply `hFactor` to that packet and obtain `False`.

The essential final composition is

```lean
hFactor (goldenZeroSectorFactorPacket_of_inversion
  (goldenZeroSectorInversionPacket source))
```

## Lean-specific processing

### Transparency of the `abbrev`

The target `GoldenZeroSectorFactorArithmeticExclusion` is an `abbrev`, so the proof can start with

```lean
intro r s a b ...
```

without an explicit `unfold`.

### Destructuring the existential package

The final hypothesis of 0346 has the form

```lean
∃ c d : ℕ,
  s.natAbs = 5 ^ 6 * c ^ 10 ∧
  (goldenFifthSndFactor r s).natAbs = d ^ 10
```

so

```lean
rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
```

extracts exactly the witnesses and proofs required by the raw-candidate constructor.

### `let source := ...`

The long constructor application is given the local name `source`. This keeps the dependent packet chain readable and avoids repeating the raw arithmetic data.

### Composition of proof-carrying data

`goldenZeroSectorInversionPacket source` and `goldenZeroSectorFactorPacket_of_inversion ...` construct structures carrying proofs in their fields. Lean's type checker guarantees that the factor packet is compatible with the inversion packet derived from the same source.

## Redundancy and duplication

There is almost no duplicated mathematics inside this theorem.

The long sequence of assumptions is introduced and immediately passed to `goldenZeroSectorCandidate_of_raw`, but this is a consequence of the design of 0346: the raw contract is repeated there to preserve an acyclic module dependency direction.

The code

```lean
let source := ...
exact hFactor (... source ...)
```

could technically be inlined into one expression. Doing so would make the constructor application much harder to read, so the current form is preferable.

## Optimization candidates

The main possible optimization concerns API ergonomics rather than proof length.

If the raw assumptions could eventually be placed in a dependency-neutral structure, the long `intro` sequence and constructor argument list could be shortened. However, as discussed for 0346, placing such a structure in the wrong module could reintroduce the dependency cycle that the current architecture avoids. This is therefore not a purely local refactor.

Locally, the theorem is already close to minimal. No `simpa`, rewriting, `ring`, `omega`, or `norm_num` is needed; the proof is a direct composition of the packet pipeline.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the generated artifact as a whole.

The proof script itself mainly needs basic elaboration and tactic support:

- `intro`
- `rcases`
- `let`
- structure / function application
- `False`

All arithmetic work is encapsulated in the upstream APIs; this theorem itself does not use `ring`, `omega`, or `norm_num`.

The project modules defining the packet APIs likely provide most required imports transitively. Because no Lean build is performed in this run, the exact minimal Mathlib import set has not been verified and is therefore left unspecified.

## Comparator challenge suitability

**Yes; this is an excellent challenge.**

A suitable exercise is:

```lean
example
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  -- intro the raw assumptions
  -- rcases the power-split witnesses
  -- construct the raw candidate
  -- inversion → factor packet → False
```

This tests:

- understanding of reducible contracts,
- introduction of a long implication chain,
- existential destructuring,
- construction of proof-carrying structures,
- composition of project APIs.

It therefore evaluates Lean proof architecture rather than the underlying number-theoretic calculation.

## Next declaration to read

The next declaration is

```lean
/-- The factor-packet receiver has exactly the public zero-sector contract. -/
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

This is a thin adapter theorem. It exposes the raw arithmetic exclusion produced by 0347 as the public contract `GoldenZeroSectorArithmeticExclusion`, which is definitionally the same contract at the closure layer. This is where factor-packet exclusion is connected to the public zero-sector closure API.

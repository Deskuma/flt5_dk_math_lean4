# 0410 `goldenZeroSectorFactorExclusion`

## Declaration kind

`theorem`

## Lean type

```lean
theorem goldenZeroSectorFactorExclusion : GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

`GoldenZeroSectorFactorExclusion` is an `abbrev` defined in the preceding factorization layer. Expanded, it is

```lean
GoldenZeroSectorFactorPacket → False
```

Thus this theorem proves unconditionally that every certified zero-sector factor packet leads to a contradiction.

## Mathematical statement

A `GoldenZeroSectorFactorPacket` retains an inversion packet constructed from the primitive arithmetic data of the zero sector, together with one of the three exact factor branches obtained from that inversion.

The factor branch is one of

- the odd branch,
- the even-left-low branch,
- the even-right-low branch,

and each branch records data such as fifth-power factorization, coprimality, the allocation of powers of two, and an exact difference equation.

However, 0410 does not perform a new case split over those three branches and derive a separate contradiction in each case.

Every factor packet retains the original `GoldenZeroSectorCandidate` completely through

```lean
packet.inversion.source
```

and the impossibility of that candidate has already been proved by the preceding infinite-descent theorem

```lean
goldenZeroSectorCandidate_false
```

Therefore the logical path is simply

$$
\mathrm{GoldenZeroSectorFactorPacket}
\longrightarrow
\mathrm{GoldenZeroSectorInversionPacket}
\longrightarrow
\mathrm{GoldenZeroSectorCandidate}
\longrightarrow
\bot.
$$

In other words, regardless of which branch was selected by the factorization layer, one can follow the packet's provenance back to the original candidate and eliminate it uniformly by the already proved strict infinite descent.

## Role in the overall proof

This theorem is the first finalization theorem in `SignedGoldenZeroSectorFinal.lean`.

Up to this point, the zero-sector proof proceeds schematically as follows.

1. Collect the raw primitive zero-sector arithmetic conditions in `GoldenZeroSectorCandidate`.
2. Perform the inversion and construct `GoldenZeroSectorInversionPacket`, which retains the product, difference, positivity, and related data for `A0` and `B0`.
3. Split according to the two-adic structure into three factor branches and construct `GoldenZeroSectorFactorPacket`.
4. In the separate descent layer, turn a candidate into a `GoldenZeroSectorDescentPacket` and repeatedly construct a strictly smaller packet.
5. Use `Nat.strong_induction_on` to prove `goldenZeroSectorDescentPacket_false`, and from it obtain `goldenZeroSectorCandidate_false`.

0410 connects the factor packet from step 3 to the candidate-level impossibility from step 5.

Through this connection, the receiver exposed by the factorization layer,

```lean
GoldenZeroSectorFactorExclusion
```

is no longer merely a hypothesis: it is supplied by an actual theorem.

The following declarations convert this factor-level exclusion back into the public

```lean
GoldenZeroSectorArithmeticExclusion
```

receiver and eventually feed it into `PositiveFermat5Refuter` and `FLT5Target`.

Thus 0410 is not primarily a place where new number theory is proved. Rather, it is a **final closure bridge** that routes the result of the long zero-sector descent back into the factorization API.

## Direct dependencies

### `GoldenZeroSectorFactorExclusion`

The receiver proposition defined in the factorization layer.

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

This is exactly the conclusion type of 0410.

### `GoldenZeroSectorFactorPacket`

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

This is the complete packet after factorization.

0410 directly uses only

```lean
packet.inversion
```

rather than `factors`. This is significant: none of the details of the three factor branches are reopened in this theorem.

### `GoldenZeroSectorInversionPacket.source`

The original candidate retained by `GoldenZeroSectorInversionPacket`.

Hence

```lean
packet.inversion.source
```

has type

```lean
GoldenZeroSectorCandidate
```

Because the original primitive arithmetic provenance is preserved through the factorization process, this projection alone is sufficient to return to the input type expected by the descent theorem.

### `goldenZeroSectorCandidate_false`

A theorem from the preceding descent layer.

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

It places any `GoldenZeroSectorCandidate` into the recursive descent invariant and eliminates it by strict descent.

The mathematical content used by 0410 is precisely the application of this already proved theorem to the source candidate stored in the factor packet.

## Proof flow

The proof has only two steps.

### 1. Introduce the factor-exclusion argument

```lean
intro packet
```

Because `GoldenZeroSectorFactorExclusion` is a reducible abbreviation, Lean effectively treats the goal as

```lean
GoldenZeroSectorFactorPacket → False
```

so after `intro packet` the context is

```lean
packet : GoldenZeroSectorFactorPacket
⊢ False
```

### 2. Send the source candidate to the already proved infinite descent

```lean
exact goldenZeroSectorCandidate_false packet.inversion.source
```

The projections have the successive types

```lean
packet.inversion
  : GoldenZeroSectorInversionPacket

packet.inversion.source
  : GoldenZeroSectorCandidate
```

and `goldenZeroSectorCandidate_false` maps that candidate directly to `False`, so the goal closes immediately.

No new branch split, congruence calculation, coprimality argument, valuation calculation, or descent construction occurs here. All of those ingredients are encapsulated in earlier theorems.

## Lean-specific handling

### Transparent reduction of `abbrev`

The conclusion is named

```lean
GoldenZeroSectorFactorExclusion
```

but no explicit `unfold` is required at the beginning of the proof.

Lean treats an `abbrev` as reducible and can expose the function type

```lean
GoldenZeroSectorFactorPacket → False
```

needed by `intro packet` automatically.

### Nested structure projection

```lean
packet.inversion.source
```

is a two-level structure projection.

From

```lean
packet : GoldenZeroSectorFactorPacket
```

Lean infers the type of `.inversion`, and from that result it infers the type of `.source`.

Because this provenance chain is retained in the types themselves, no intermediate arithmetic data has to be reconstructed.

### Direct application of a theorem returning `False`

The expression

```lean
goldenZeroSectorCandidate_false packet.inversion.source
```

already has result type `False`, so `exact` finishes the proof.

Neither `False.elim` nor `by_contra` is necessary.

### It is type-safe not to consume the branch data

`GoldenZeroSectorFactorPacket` also contains

```lean
factors : GoldenZeroSectorFactorData inversion
```

but 0410 never refers to this field.

Lean does not require every field of a structure to be used in a proof. The existence of the packet already entails the existence of its source candidate, and that source is known to be impossible. Therefore the branch data is unnecessary for this particular closure theorem.

## Redundancy and duplication

There is essentially no duplication in the proof body of 0410 itself.

At first sight, the entire factorization layer may appear redundant because constructing a `GoldenZeroSectorFactorPacket` requires substantial work, while the final exclusion never inspects `packet.factors`.

However, the repository structure shows that the factorization layer has independent mathematical value.

- It exposes exact two-adic branch data.
- It records the modulo-eleven channel in the odd branch.
- It provides an auditable intermediate structure between source-level arithmetic and branch-level arithmetic.
- It establishes the receiver boundary `GoldenZeroSectorFactorArithmeticExclusion`.

Meanwhile, the current unconditional closure already has the stronger theorem `goldenZeroSectorCandidate_false`. Therefore there is no reason for 0410 to reproduce branch-specific contradictions.

The natural interpretation is thus not that the factorization is redundant, but that the final theorem is deliberately short because it reuses the strongest already proved result.

## Optimization candidates

### 1. It could be shortened to a term-style proof

The current proof

```lean
by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

is already very short, but technically it could be written as

```lean
fun packet => goldenZeroSectorCandidate_false packet.inversion.source
```

The present form arguably makes it slightly clearer that the theorem implements a function-valued receiver, so the practical optimization gain is negligible.

### 2. Do not add branch-by-branch contradictions

One could `cases` on `packet.factors` and handle all three branches separately, but that would be redundant because the source candidate is already impossible.

For 0410, the current provenance-based proof is the better design.

### 3. A provenance shortcut accessor is unnecessary

A helper such as

```lean
GoldenZeroSectorFactorPacket.source
```

could shorten `packet.inversion.source`, but the existing two-level projection is already explicit and readable. A dedicated helper would add little value.

## Required Mathlib imports

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The proof body of 0410 itself directly uses almost no Mathlib theorem or tactic. Its real dependencies are the previously defined FLT5 declarations.

The directly needed logical interface consists of

- `GoldenZeroSectorFactorPacket`,
- `GoldenZeroSectorFactorExclusion`,
- `GoldenZeroSectorInversionPacket.source`,
- `GoldenZeroSectorCandidate`,
- `goldenZeroSectorCandidate_false`.

In the generated module order, this theorem appears in `SignedGoldenZeroSectorFinal.lean` after both the factorization and descent layers have already been loaded.

### Import optimization candidate

For 0410 alone, `import Mathlib` is much broader than the proof body requires.

At the split-module level, conceptually the theorem only needs

- the factorization module providing the factor packet and factor-exclusion receiver,
- the descent module providing `goldenZeroSectorCandidate_false`.

However, no Lean build is performed in this documentation task, so the exact minimal import set has not been mechanically verified. It would therefore be speculative to assert a precise smallest list of import modules.

## Comparator challenge suitability

**Yes, but it is low difficulty in isolation.**

It can serve as a challenge for tracing structure provenance and reducing a receiver abbreviation correctly.

For example, one could provide only

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False

axiom goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False
```

and context showing that

```lean
packet.inversion.source : GoldenZeroSectorCandidate
```

then ask the model to fill the proof hole for 0410.

This evaluates whether it can

- understand the reduction of `abbrev`,
- trace nested structure projections,
- notice that the branch data is unnecessary,
- reuse the strongest available theorem along the shortest dependency path.

If the goal is to evaluate arithmetic reasoning or infinite descent itself, `goldenZeroSectorDescentPacket_false` or `GoldenZeroSectorDescentPacket.strictDescent` would be substantially more meaningful Comparator challenges than this wrapper theorem.

## Next declaration to read

The next declaration is 0411:

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

Whereas 0410 supplies

$$
\mathrm{GoldenZeroSectorFactorExclusion}
$$

unconditionally, 0411 converts that factor-level receiver into the source-level receiver exposed publicly by `SignedGoldenClosure`,

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

Thus the finalization path starts with

$$
\mathrm{GoldenZeroSectorCandidate}
\xrightarrow{\text{strict descent}}
\bot,
$$

uses 0410 to obtain

$$
\mathrm{GoldenZeroSectorFactorExclusion},
$$

and then uses 0411 to return to

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

The declaration after that applies this conversion to 0410 itself and thereby makes the public zero-sector arithmetic exclusion unconditional.
# 0088 — `signedFiveAdicPowerSplit_of_packet`

## Lean type

```lean
noncomputable def signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    SignedFiveAdicPowerSplit u v w :=
  Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

This declaration is not a theorem but a `noncomputable def`. From

```lean
Nonempty (SignedFiveAdicPowerSplit u v w)
```

proved by 0087 `nonempty_signedFiveAdicPowerSplit_of_packet`, it uses `Classical.choice` to select one witness and returns a `SignedFiveAdicPowerSplit u v w` that downstream proofs can use directly.

## Mathematical statement

The mathematical content has already been established in 0087. Given a signed five-adic packet, there exist positive coprime natural numbers $a,b$ such that

$$
\operatorname{carrier}=5^4a^5,
$$

$$
\operatorname{residual}=5b^5,
$$

$$
\operatorname{distinguished}=5ab.
$$

This declaration adds no new arithmetic condition. It merely selects one of the existing power splits and exposes it as named data.

Mathematically, it corresponds to passing from

$$
\exists s:\mathrm{SignedFiveAdicPowerSplit}(u,v,w)
$$

to a chosen

$$
s:\mathrm{SignedFiveAdicPowerSplit}(u,v,w).
$$

## Role in the whole proof

Up to 0087, the development only proved that an exact fifth-power split exists for a packet, and that result is wrapped in `Nonempty`.

Instead of repeatedly writing

```lean
rcases nonempty_signedFiveAdicPowerSplit_of_packet p with ⟨s⟩
```

in downstream theorems, it is cleaner to expose a reusable selection API such as

```lean
let s := signedFiveAdicPowerSplit_of_packet p
```

or even use projections directly, for example

```lean
(signedFiveAdicPowerSplit_of_packet p).carrier_eq.
```

This declaration is that selection layer.

Conceptually,

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit})
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$

The first step is 0087; this declaration performs the second.

As a result, the long gcd-stripping, mod-25, and fifth-power factor-splitting construction is completely hidden from downstream code.

## Direct dependencies

The direct dependencies are very small:

- `SignedFiveAdicPacket`
- `SignedFiveAdicPowerSplit`
- `nonempty_signedFiveAdicPowerSplit_of_packet` (0087)
- `Classical.choice`

In particular, this declaration does not directly use

- `signedFiveAdicPacket_gcd_eq_five`
- `fifth_power_factor_split`
- the mod-$25$ lemmas
- the power API for `Nat.Coprime`
- `ring`
- `omega`
- `norm_num`

because all of that arithmetic has already been encapsulated inside 0087.

## Proof flow

The proof has only one conceptual step.

### 1. Obtain the existence proof from 0087

```lean
nonempty_signedFiveAdicPowerSplit_of_packet p
```

returns

```lean
Nonempty (SignedFiveAdicPowerSplit u v w).
```

### 2. Select a witness with `Classical.choice`

```lean
Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

extracts one

```lean
SignedFiveAdicPowerSplit u v w
```

from that `Nonempty`, and this becomes the value of the definition.

There is no new arithmetic computation and no case split.

## Lean-specific processing

The Lean-specific content is almost entirely concentrated in `Classical.choice`.

`Nonempty α` expresses, propositionally, that the type `α` has an element. It does not by itself provide a computationally extractable value of type `α`. In Lean's constructive core, one cannot in general extract arbitrary data from a proposition merely because existence has been proved.

Classical choice is therefore used to select a witness from the existence proof. This is why the declaration is marked

```lean
noncomputable.
```

Importantly, `noncomputable` here does not indicate any weakness in the mathematical proof. The existence theorem from 0087 is kernel-checked; this declaration simply gives a name to some witness without requiring a computational rule for deciding which witness is chosen.

The witness selected by `Classical.choice` need not be canonical. Downstream code should depend only on the fields guaranteed by `SignedFiveAdicPowerSplit`, not on implementation details about which particular $a,b$ were selected.

## Redundancy and duplication

The code itself is one line and has essentially no local redundancy.

At the API-design level, however, 0087 and this declaration form the familiar two-stage pattern

```lean
private theorem ... : Nonempty T
noncomputable def ... : T := Classical.choice ...
```

This cleanly separates existence proof from witness selection and is easy to audit. On the other hand, if the proof from 0087 could be reorganized as a constructive definition returning `SignedFiveAdicPowerSplit` directly, this declaration could in principle disappear.

Because 0087 itself consumes existential witnesses from `fifth_power_factor_split`, the current `Nonempty` plus `Classical.choice` organization is natural for the present proof style.

## Optimization candidates

### Candidate A — Keep the current two-stage design

This is the most conservative and readable choice:

- 0087: existence proof
- 0088: selection API

The responsibilities are clearly separated.

### Candidate B — Return a constructive constructor directly

If the witnesses inside 0087 can be assembled directly as a term, one could write

```lean
def signedFiveAdicPowerSplit_of_packet ... : SignedFiveAdicPowerSplit ... := by
  ...
```

and potentially remove both `noncomputable` and `Classical.choice`.

Since no computational use of the witness is currently required, the practical gain may be limited.

### Candidate C — Standardize the choice-wrapper pattern

If the surrounding module family contains many declarations of the form

```lean
private theorem nonempty_X ... : Nonempty X
noncomputable def X_of_... := Classical.choice ...
```

then standardizing naming and API conventions may be worthwhile. A generic helper would not shorten the code beyond a one-line `Classical.choice`, so the value would be architectural consistency rather than code reduction.

## Required Mathlib imports and import optimization

The generated standalone artifact on the target branch uses `import Mathlib`.

For this declaration alone, the only Mathlib-side functionality directly needed is essentially the basic `Nonempty`/`Classical.choice` infrastructure. Therefore importing all of `Mathlib` is clearly excessive for this declaration in isolation.

However, the actual `SignedFiveAdicPowerSplit.lean` module also contains 0087 immediately before it, and that proof uses natural-number gcd and coprimality, primes, powers, division, and the `ring`, `omega`, and `norm_num` tactics. Therefore the minimal imports for the module cannot be inferred from this wrapper alone.

Any import optimization should enumerate the dependencies of the complete source module, narrow the umbrella import incrementally, and verify each step with a Lean build. No build is performed in this task.

## Comparator challenge suitability

Yes, but it is better suited as a Lean API-design comparator than as a number-theory proof-search challenge.

Three natural alternatives are:

1. the current `Nonempty` + `Classical.choice` approach;
2. a direct constructive `def` returning the witness;
3. exposing only the existence theorem and using `rcases` at every call site.

Useful evaluation criteria include:

- whether classical choice is required;
- downstream API ergonomics;
- locality of the proof term;
- simplicity of downstream code;
- resistance to accidental dependence on the concrete chosen witness.

The current design gives a good balance between downstream readability and auditability of the existence proof.

## PDF and source basis

The formal source of truth is the target branch's `Flt5DkMath/FLT5StandAlone.lean`, where this declaration is confirmed to belong to the `SignedFiveAdicPowerSplit.lean` section and to occur immediately after 0087.

The existing Japanese and English PDFs are treated as narrative background. In this run, GitHub code search returned a 502 upstream error, so no exact PDF page or section corresponding one-to-one with this choice wrapper could be verified. Therefore no PDF theorem number, page number, or wording is supplied by conjecture.

## Next declaration to read

The next declaration in the source is

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

The next article should therefore study the composition

$$
\mathrm{SignedBranchANormalForm}
\Longrightarrow
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$

This gives a single public entry point from the signed normal form all the way to the exact power split.
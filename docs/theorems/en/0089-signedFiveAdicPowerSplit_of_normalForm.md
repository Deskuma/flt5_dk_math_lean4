# 0089 — `signedFiveAdicPowerSplit_of_normalForm`

## Lean type

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

This declaration is not a theorem but a `noncomputable def`. It composes two existing adapters: first it constructs a signed five-adic packet from `SignedBranchANormalForm u v w`, then it selects an exact power split from that packet.

## Mathematical statement

The input is a signed Branch-A normal form. Through the already constructed five-adic packet, it yields positive coprime natural numbers $a,b$ together with exact power-split data.

Thus the returned value `s : SignedFiveAdicPowerSplit u v w` carries at least

$$
s.fiveAdic : \mathrm{SignedFiveAdicPacket}(u,v,w),
$$

$$
s.fiveAdic.carrier = 5^4 s.a^5,
$$

$$
s.fiveAdic.residual = 5 s.b^5,
$$

$$
s.fiveAdic.distinguished = 5 s.a s.b,
$$

$$
0<s.a,\qquad 0<s.b,\qquad \gcd(s.a,s.b)=1.
$$

This declaration does not re-prove any of those arithmetic facts. Mathematically it is simply the composition

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$

## Role in the overall proof

This declaration is the public entry point that connects a signed normal form directly to the exact power-split layer.

Earlier, 0053 `SignedBranchANormalForm` provides the orientation-preserving normal form, and 0077 `signedFiveAdicPacket_of_normalForm` constructs from it a packet carrying the carrier / residual / distinguished data and the five-adic conditions. Articles 0087–0088 establish existence of, and then select, the exact fifth-power split of such a packet.

This declaration compresses those steps into one layer, so downstream code does not need to name the intermediate packet explicitly. It can simply use

```lean
signedFiveAdicPowerSplit_of_normalForm hNF
```

to reach the exact split.

Immediately after this API boundary, the source introduces `SignedFiveAdicPowerSplitCore`. In the proof architecture, this is therefore the final adapter from a normal form to the exact split packet that the remaining arithmetic core is expected to refute.

## Direct dependencies

The direct dependencies are only these four declarations:

- `SignedBranchANormalForm`
- `SignedFiveAdicPowerSplit`
- `signedFiveAdicPacket_of_normalForm` (0077)
- `signedFiveAdicPowerSplit_of_packet` (0088)

Indirectly, through 0088, it depends on the constructor existence proof of 0087, the exact gcd theorem of 0082, 0027 `fifth_power_factor_split`, and the mod-$25$ and coprimality lemmas. None of those appear in this declaration's own proof term.

## Proof flow

The proof is completed by one composition step.

### 1. Build a packet from the normal form

```lean
signedFiveAdicPacket_of_normalForm hNF
```

produces

```lean
SignedFiveAdicPacket u v w
```

from the normal form.

### 2. Select a power split from the packet

That value is passed to

```lean
signedFiveAdicPowerSplit_of_packet
```

to obtain

```lean
SignedFiveAdicPowerSplit u v w
```

The whole Lean term is

```lean
signedFiveAdicPowerSplit_of_packet
  (signedFiveAdicPacket_of_normalForm hNF)
```

with no case split, rewrite, or arithmetic tactic.

## Lean-specific processing

The main Lean-specific point is that the implicit indices `{u v w : ℕ}` are inferred consistently through both adapters.

The type of `hNF` determines `u v w`, and the result of

```lean
signedFiveAdicPacket_of_normalForm hNF
```

has the same indices. Therefore `signedFiveAdicPowerSplit_of_packet` can infer the same indices without additional annotations.

The declaration is also `noncomputable`. This is inherited from 0088, which uses `Classical.choice` to select a witness from `Nonempty (SignedFiveAdicPowerSplit u v w)`. This declaration itself performs no new classical reasoning; noncomputability merely propagates along the adapter chain.

## Redundancy and duplication

The body is one line, so there is essentially no local redundancy.

Mathematically, however, it is a pure composition wrapper. The declaration could be removed if every call site instead wrote

```lean
signedFiveAdicPowerSplit_of_packet
  (signedFiveAdicPacket_of_normalForm hNF)
```

directly.

There is still a strong reason to keep the named wrapper. In the downstream theorem `signedBranchARefuter_of_powerSplitCore`, this single API name makes the architectural step “move from normal form to exact split” explicit. The declaration therefore favors semantic boundary naming over raw line-count reduction.

## Optimization candidates

### Candidate A — Keep the current wrapper

This is the most natural option. The declaration name describes the layer conversion directly and makes downstream proofs easier to read.

### Candidate B — Move toward function-composition style

Conceptually this is just a composition of two functions, so a more point-free local helper could be imagined. With dependent indices, however, the current explicit application tends to produce clearer type inference and error messages.

### Candidate C — Merge into a constructive chain

If 0087–0088 were redesigned as a constructive constructor, this declaration could potentially become a computable `def` rather than `noncomputable`. In this proof-only API layer, however, the practical gain from computability would be small.

### Candidate D — Standardize adapter naming

This region already uses names such as `..._of_normalForm`, `..._of_packet`, and `..._of_powerSplitCore`. Extending that `_of_` convention consistently across other bridge modules would make the proof graph easier to follow by declaration names alone.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact on the target branch is built with `import Mathlib`.

This declaration itself uses no Mathlib arithmetic theorem or tactic directly; it only type-checks two project-local adapter applications. Thus there is no reason for this declaration in isolation to require the entire `Mathlib` umbrella import.

The actual `SignedFiveAdicPowerSplit.lean` module, however, also contains 0087 and therefore uses natural-number gcd, coprimality, primes, powers, division, `ring`, `omega`, and `norm_num`. Import minimization has to be decided at the module level with those dependencies included.

A sensible optimization procedure would enumerate the theorems and tactics used by the source module, gradually narrow the umbrella import, and verify each step with a Lean build. No Lean build is performed in this task, so a concrete minimal import set is not asserted speculatively.

## Comparator challenge suitability

Yes, but it is better suited to an API / proof-architecture comparator than to a number-theory proof-search challenge.

Useful variants to compare include:

1. The current named composition wrapper.
2. Direct composition of the two adapters at every call site.
3. A design that merges the packet and power-split conversion into one constructor.
4. A constructive constructor that removes `noncomputable`.

Relevant evaluation criteria are proof-graph visibility, downstream brevity, dependency boundaries, locality of error messages, and how clearly classical dependencies are exposed.

The key comparator question is whether this one-line declaration is merely a redundant alias or a useful semantic adapter. In the present architecture, the latter interpretation is well supported.

## PDF and source basis

The formal basis is the target branch's `Flt5DkMath/FLT5StandAlone.lean`. The generated manifest places this declaration in the `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` section, immediately after 0088 `signedFiveAdicPowerSplit_of_packet` and immediately before `SignedFiveAdicPowerSplitCore`.

Existing Japanese and English PDFs are treated as narrative background sources. During this run GitHub code search returned a 502 upstream error, so no PDF page or section corresponding one-to-one with this adapter could be confirmed. Therefore no PDF-specific theorem number, page number, or quotation is supplied speculatively.

## Next declaration to read

The declaration immediately following it in source order is

```lean
abbrev SignedFiveAdicPowerSplitCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False
```

This is the receiver contract that sends every exact power-split packet to contradiction. The next article should therefore examine

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\to\bot,
$$

which isolates the remaining arithmetic core. The following theorem, `signedBranchARefuter_of_powerSplitCore`, then uses the adapter studied in this article to lift that core contract to a refuter for the whole signed Branch-A route.
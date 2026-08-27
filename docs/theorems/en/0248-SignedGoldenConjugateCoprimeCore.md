# 0248 — `SignedGoldenConjugateCoprimeCore`

## Lean type

```lean
/-- Receiver contract for contradictions on packets carrying certified conjugate
relative primality. -/
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

This is an `abbrev`, not a theorem, and its value lies in `Prop`. It names a contradiction-receiver contract: given a `SignedGoldenConjugateCoprimePacket`, the receiver must return `False`.

## Mathematical statement and meaning of the declaration

Mathematically, the declaration packages the assertion that for arbitrary `u v w : ℕ`, any packet carrying the certified conjugate-coprimality state leads to a contradiction:

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenConjugateCoprimePacket}(u,v,w)
\to \bot.
$$

By declarations 0245–0247, the producer side has already progressed from the signed normal form to ramifier-stripped data and then to a packet that carries

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta}).
$$

Declaration 0248 isolates only the remaining task: once such a certified packet is available, derive `False`.

Thus 0248 proves no new number-theoretic identity itself. It turns the unresolved downstream contradiction step into an explicit function type and gives that type a stable project-local name.

## Role in the full proof

The purpose of this declaration is to separate the producer pipeline from the contradiction pipeline.

Upstream, the development constructs a

$$
\mathrm{SignedGoldenRamifierStrippedPacket},
$$

proves relative primality between `beta` and its conjugate in 0244, packages that certificate in `SignedGoldenConjugateCoprimePacket` in 0245, and exposes a direct normal-form producer in 0247.

Declaration 0248 then compresses everything that remains into

$$
\text{certified packet}
\longrightarrow
\mathrm{False}.
$$

This boundary allows the downstream mechanism—fifth-power extraction, unit analysis, descent, or any later replacement—to change without forcing the upstream routing layer to know its details.

In the canonical source, the next declaration is

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

which lifts this receiver contract to a refuter for the entire signed Branch-A normal-form interface.

## Direct dependencies

The direct dependency surface is very small:

- `SignedGoldenConjugateCoprimePacket`
- universal quantification `∀`
- implication `→`
- `False`

The packet from 0245 itself carries

```lean
stripped : SignedGoldenRamifierStrippedPacket u v w
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

so 0248 receives the stripped state and the relative-primality certificate as one certified object rather than as separate arguments.

No earlier theorem is directly used in the body of this declaration. Results such as 0244 and the producer from 0247 are operationally important downstream, but they are not required to define the alias itself.

## Construction flow

The construction is only a transparent type abbreviation:

```lean
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

1. Quantify over arbitrary implicit natural numbers `u v w`.
2. Receive a `SignedGoldenConjugateCoprimePacket u v w`.
3. Require a result of type `False`.

There is no proof script, rewriting, or tactic execution in 0248 itself.

## Lean-specific processing

### `abbrev`

`abbrev` creates a transparent abbreviation. Lean can unfold `SignedGoldenConjugateCoprimeCore` back to its function type during elaboration when needed. The declaration therefore does not introduce a new opaque logical object; it gives a readable API name to a long proposition.

### A proposition that behaves as a function

Because the right-hand side is

```lean
∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

a hypothesis

```lean
hCore : SignedGoldenConjugateCoprimeCore
```

can be applied like a function. Declaration 0249 uses exactly this form:

```lean
hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

### Implicit indices

The indices `u v w` are implicit. Lean infers them from the packet type, so consumers normally do not need to supply those indices explicitly.

## Redundancy and duplication

Declaration 0237 already introduced the analogous contract

```lean
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

Declaration 0248 differs only in the refinement level of the packet: the receiver now gets a state in which relative primality between `beta` and its conjugate has already been certified.

Logically, the development could omit 0248 and repeat the full function type in every consumer theorem. Naming the phase-specific contract is nevertheless useful because it:

- distinguishes stripped-stage responsibility from conjugate-coprime-stage responsibility;
- makes the achieved proof-state visible in theorem signatures;
- stabilizes the upstream facade against downstream implementation changes;
- keeps later theorem types short and discoverable.

Thus the similarity with 0237 is intentional API-level duplication rather than accidental mathematical duplication.

## Optimization candidates

1. **Keep the phase-specific core name**
   - this gives the clearest proof-state boundary and is easy to audit.

2. **Introduce a generic contradiction receiver**
   - for example, a generic alias such as `Refuter P := P → False` could factor out the repeated shape;
   - this reduces repeated syntax but weakens domain-specific theorem discovery.

3. **Standardize packet-refinement and core-lift naming**
   - if more stages such as stripped, conjugate-coprime, and fifth-power cores accumulate, a stronger naming convention or namespace structure could make the pipeline easier to scan.

4. **Compare with `Not` notation**
   - `SignedGoldenConjugateCoprimePacket u v w → False` is equivalent to `¬ SignedGoldenConjugateCoprimePacket u v w`;
   - the current function form is particularly convenient for direct application in 0249.

The local implementation is already a one-line abbreviation, so meaningful optimization is architectural rather than syntactic.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but 0248 itself uses no advanced Mathlib theorem or tactic.

Its direct language-level requirements are effectively only:

- `Nat`
- `Prop`
- `False`
- `SignedGoldenConjugateCoprimePacket`

The packet's upstream construction depends on a much broader surface including `GoldenRelPrime`, golden norms, Euclidean-domain infrastructure, and integer divisibility. Consequently import minimization must be evaluated at the full `SignedGoldenConjugateCoprime.lean` module level rather than from 0248 in isolation.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes, although the interesting comparison is API architecture rather than tactic performance.

Possible variants include:

- A: the current phase-specific `abbrev`;
- B: repeat the full function type directly in each consumer;
- C: introduce a generic `Refuter` alias;
- D: express the contradiction contract as negation of an existential or packet inhabitance statement.

Useful comparison axes are theorem-signature size, visibility of proof phases, elaboration simplicity, theorem discovery, refactor resistance, and consumer readability.

The A-versus-C comparison is especially useful for evaluating whether domain-specific naming reduces cognitive load enough to justify a thin API layer.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The canonical source places this declaration immediately after 0247 and immediately before 0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore`.

The target branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal receiver contract was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore`**:

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

Declaration 0248 defines the receiver contract from certified packets to `False`; 0249 composes that receiver with the normal-form producer from 0247 and thereby lifts it to a refuter for the full signed Branch-A normal-form interface.
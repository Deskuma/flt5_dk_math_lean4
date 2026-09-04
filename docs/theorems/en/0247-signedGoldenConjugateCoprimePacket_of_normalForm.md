# 0247 — `signedGoldenConjugateCoprimePacket_of_normalForm`

## Lean type

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

This is a `noncomputable def`, not a theorem. It takes a `SignedBranchANormalForm`, constructs the corresponding ramifier-stripped packet, and then passes that packet through the canonical producer from 0246 to obtain a packet carrying a conjugate-coprimality certificate.

## Mathematical statement and meaning of the declaration

This declaration proves no new number-theoretic proposition by itself. It composes two already established transformations,

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

and

$$
\mathrm{SignedGoldenRamifierStrippedPacket}
\longrightarrow
\mathrm{SignedGoldenConjugateCoprimePacket},
$$

into the direct entry point

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenConjugateCoprimePacket}.
$$

The returned packet retains the stripped-state element `beta` together with certificates conceptually expressing

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
\qquad
\tau\nmid\beta,
$$

and, in addition,

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta}).
$$

Thus the definition makes the certified state required by downstream fifth-power factor extraction reachable from a signed normal form through a single function call.

## Role in the full proof

In the signed exceptional branch of the FLT5 development, the pipeline proceeds from a normal form through five-adic splitting, transfer to the golden order, removal of the visible ramifier `tau`, and finally certification that the remaining element is relatively prime to its conjugate.

Declaration 0236 already provided

```lean
signedGoldenRamifierStrippedPacket_of_normalForm
```

as a direct facade from the normal form to the stripped packet. Declaration 0244 proved relative primality between `beta` and its conjugate, 0245 packaged that fact into `SignedGoldenConjugateCoprimePacket`, and 0246 promoted any stripped packet to the certified packet.

Declaration 0247 composes those stages so that upstream consumers do not need to manipulate the intermediate stripped packet manually.

Conceptually, it is the facade for the proof-state pipeline

$$
\text{normal form}
\longrightarrow
\text{ramifier stripped}
\longrightarrow
\text{conjugate-coprime certified}.
$$

This layer lets later fifth-power decomposition or contradiction cores start from a normal form while remaining independent of the intermediate construction order and individual theorem names.

## Direct dependencies

The direct dependencies are:

- `SignedBranchANormalForm`
- 0236 `signedGoldenRamifierStrippedPacket_of_normalForm`
- 0245 `SignedGoldenConjugateCoprimePacket`
- 0246 `signedGoldenConjugateCoprimePacket_of_stripped`

The body is essentially the composition

```lean
signedGoldenConjugateCoprimePacket_of_stripped
  (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

Declaration 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` is an indirect dependency because 0246 uses it to fill the certificate field.

## Construction flow

The construction has exactly two stages.

1. Pass `hNF : SignedBranchANormalForm u v w` to

```lean
signedGoldenRamifierStrippedPacket_of_normalForm hNF
```

to obtain a `SignedGoldenRamifierStrippedPacket u v w`.

2. Pass that stripped packet to

```lean
signedGoldenConjugateCoprimePacket_of_stripped
```

to obtain a `SignedGoldenConjugateCoprimePacket u v w`.

No new arithmetic calculation, rewrite, or tactic proof occurs here. The declaration only composes constructions whose correctness has already been established upstream.

## Lean-specific processing

### 1. `noncomputable def`

Declaration 0246 itself is an ordinary `def` because no choice is required once a concrete stripped packet is supplied. The present declaration is `noncomputable` because its first stage,

```lean
signedGoldenRamifierStrippedPacket_of_normalForm
```

ultimately uses a stripped packet selected through `Classical.choice` upstream.

Therefore noncomputability is not newly introduced by 0247; it propagates from an earlier packet-selection boundary.

### 2. Inference of implicit parameters

The parameters `u v w` are implicit. Lean infers them from the type of `hNF` and automatically aligns the type parameters of the two producer functions.

### 3. A value definition rather than a theorem proof

The result is not a proposition but an inhabitant of `SignedGoldenConjugateCoprimePacket u v w : Type`. Consequently there is no `by` proof block: the composition expression itself is the definition body.

## Redundancy and duplication

Logically, this declaration is a pure composition wrapper. A consumer could always write

```lean
signedGoldenConjugateCoprimePacket_of_stripped
  (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

directly and obtain the same result.

So the declaration adds no mathematical information. As a facade, however, it has useful API value:

- it hides the intermediate stripped packet from normal-form consumers;
- it records the intended proof pipeline in a discoverable declaration name;
- downstream code need not know both 0236 and 0246;
- changes to the intermediate representation can be hidden behind a stable normal-form entry point;
- higher-level contradiction cores can keep a narrower dependency surface.

Thus the redundancy is reasonable at the API level.

## Optimization candidates

1. **Keep the current facade**
   - It is concise and provides a stable consumer-facing entry point.

2. **Factor repeated conversion chains into shared helpers**
   - If many `*_of_normalForm` bridges follow the same pattern, the conversion pipeline could be organized more systematically in a namespace or helper layer.

3. **Concentrate the choice boundary further upstream**
   - If `noncomputable` propagates through many facades, isolating the canonical packet selection in one place could make the source of noncomputability clearer.

4. **Remove intermediate facade layers**
   - Consumers could directly compose 0236 and 0246, reducing API count at the cost of weaker phase boundaries and greater coupling to intermediate representations.

The present one-line body is already close to locally optimal; the meaningful optimization questions are architectural rather than proof-level.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself directly uses no Mathlib tactic or generic theorem; it only composes project-local declarations.

Its immediate surface dependencies are essentially:

- `SignedBranchANormalForm`
- `SignedGoldenRamifierStrippedPacket`
- `SignedGoldenConjugateCoprimePacket`
- the two producer definitions above

The upstream modules, however, depend on a much wider Mathlib surface for integer divisibility, golden norms, Euclidean-domain infrastructure, and relative-primality arguments. Therefore the minimal import set cannot be inferred from 0247 alone and must be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes, although the comparison is primarily about API and pipeline design rather than theorem proving.

Useful variants are:

- A: the current named facade
- B: direct composition of 0236 and 0246 at each consumer
- C: one large constructor from normal form directly to the certified packet
- D: a generic conversion/composition layer for proof-state transitions

Useful comparison axes include:

- consumer code size
- coupling to intermediate representations
- visibility of the noncomputable boundary
- robustness under refactoring
- discoverability of declarations
- clarity of proof phases in the type-level API

The comparison between A and B is especially useful for measuring how much a small facade reduces cognitive load in a long formal development.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places the present declaration immediately after 0246 in the following form:

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

The target branch also contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact page or section corresponding to this architectural facade was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0248 `SignedGoldenConjugateCoprimeCore`**:

```lean
/-- Receiver contract for contradictions on packets carrying certified conjugate
relative primality. -/
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

By 0247, the producer side from a signed normal form to a conjugate-coprime certified packet is complete. Declaration 0248 introduces the contradiction receiver contract that consumes such a packet and returns `False`, connecting the producer pipeline to the remaining contradiction core.
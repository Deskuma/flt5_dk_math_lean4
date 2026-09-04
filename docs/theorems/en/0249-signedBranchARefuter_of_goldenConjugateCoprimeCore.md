# 0249 — `signedBranchARefuter_of_goldenConjugateCoprimeCore`

## Lean type

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

This is a `theorem`. It lifts the contradiction receiver provided by 0248 `SignedGoldenConjugateCoprimeCore` to the project-level `SignedBranchARefuter` interface for all signed Branch-A normal forms.

## Mathematical statement

The core from 0248 supplies, for arbitrary `u v w : ℕ`,

$$
\mathrm{SignedGoldenConjugateCoprimePacket}(u,v,w)
\to \bot.
$$

Meanwhile, 0247 `signedGoldenConjugateCoprimePacket_of_normalForm` constructs such a certified packet from a signed Branch-A normal form.

The present theorem simply composes those two maps and obtains

$$
\mathrm{SignedBranchANormalForm}(u,v,w)
\to \bot.
$$

No new number-theoretic identity or divisibility argument appears here. This is a routing theorem connecting the conjugate-coprime certified state built in declarations 0241–0247 to the Branch-A refutation interface.

## Role in the full proof

This theorem is an important phase boundary in the proof pipeline.

Upstream, the development constructs a

$$
\mathrm{SignedGoldenRamifierStrippedPacket},
$$

proves relative primality between `beta` and `goldenConj beta`, packages that certificate into

$$
\mathrm{SignedGoldenConjugateCoprimePacket},
$$

and in 0247 exposes a facade that produces this packet directly from the signed normal form. Declaration 0248 then specifies only the remaining contradiction contract on such certified packets.

Declaration 0249 combines that producer and receiver and thereby yields the higher-level `SignedBranchARefuter` expected by the routing layer.

Its architectural role is therefore

$$
\text{normal-form producer}
+\text{conjugate-coprime contradiction core}
\longrightarrow
\text{Branch-A refuter}.
$$

The immediately following declaration 0250 `branchB_false_of_goldenConjugateCoprimeCore` passes the resulting `SignedBranchARefuter` into the existing Branch-B routing theorem and propagates the contradiction back to the original counterexample packet.

## Direct dependencies

The direct dependencies are:

- 0248 `SignedGoldenConjugateCoprimeCore`
- 0247 `signedGoldenConjugateCoprimePacket_of_normalForm`

The conclusion type also depends on the already defined interfaces:

- `SignedBranchARefuter`
- `SignedBranchANormalForm`

Conceptually, the dependency graph is just

$$
\mathrm{SignedBranchANormalForm}
\xrightarrow{\text{0247}}
\mathrm{SignedGoldenConjugateCoprimePacket}
\xrightarrow{\text{0248}}
\bot.
$$

## Proof flow

The proof is only three lines:

```lean
by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

1. Expand the function type represented by `SignedBranchARefuter` and introduce `u v w` together with `hNF`.
2. Build the certified packet with `signedGoldenConjugateCoprimePacket_of_normalForm hNF`.
3. Feed that packet to `hCore` and obtain `False`.

There is no rewriting, arithmetic tactic, or existential witness construction.

## Lean-specific processing

### `intro` through an abbreviated interface

`SignedBranchARefuter` behaves as a proposition-valued function type, so `intro u v w hNF` exposes its arguments directly. No explicit `unfold` is needed.

### Inference of implicit indices

The core has type

```lean
∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

with implicit indices. The packet returned by 0247 determines `u v w`, so Lean can elaborate

```lean
hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

without supplying them explicitly.

### Pure term composition via `exact`

The proof uses no automation beyond elaboration. It is essentially a function-composition proof term written in tactic syntax.

## Redundancy and duplication

Declaration 0238 `signedBranchARefuter_of_goldenRamifierStrippedCore` has almost the same shape.

0238 proves

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\to \mathrm{SignedBranchARefuter},
$$

whereas 0249 proves

$$
\mathrm{SignedGoldenConjugateCoprimeCore}
\to \mathrm{SignedBranchARefuter}.
$$

The only structural difference is the refinement level of the packet produced from the normal form.

One could factor both through a generic lifting helper. However, the phase-specific theorem names make the achieved proof state visible and are useful when auditing a long formal development. The duplication is therefore better understood as intentional API redundancy than as accidental mathematical repetition.

## Optimization candidates

1. **Keep the current theorem**
   - the proof phase is visible directly in the theorem name and the implementation is already minimal.

2. **Introduce a generic refuter-lifting helper**
   - abstract from a producer `A → B` and a core `B → False` to a refuter `A → False`;
   - the gain is small because the current proof is only one substantive expression, while theorem discovery may become weaker.

3. **Compare with a point-free term-style definition**
   - the theorem could be written as a direct `fun ... => ...` term;
   - the current `intro` style exposes indices and the normal-form hypothesis more clearly.

4. **Standardize core / producer naming**
   - if stripped, conjugate-coprime, fifth-power, and later phases continue to accumulate, a stricter naming convention for `*_of_*Core` and `*_Packet_of_*` could make the pipeline easier to scan.

Locally, there is little to optimize in proof length; the interesting design choices are architectural.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but this theorem itself directly uses no advanced Mathlib theorem or tactic.

Its effective dependencies are project-local:

- `SignedGoldenConjugateCoprimeCore`
- `SignedBranchARefuter`
- `signedGoldenConjugateCoprimePacket_of_normalForm`

Thus the Mathlib surface of this declaration in isolation is tiny. The surrounding module, however, depends on `GoldenRelPrime`, norm arithmetic, divisibility, and Euclidean-domain infrastructure, so import minimization must be evaluated at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes, although the interesting comparison concerns API architecture rather than tactic performance.

Possible variants are:

- A: the current phase-specific theorem;
- B: a generic refuter-lift helper;
- C: a point-free direct term;
- D: remove the 0248 core alias and write the full function type directly in the theorem signature.

Useful metrics are proof-term size, elaboration simplicity, visibility of phase boundaries, theorem discovery, refactor resistance, and consumer readability.

The A-versus-B comparison is a compact way to test whether abstracting one-line routing theorems actually improves a large Lean development.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The canonical source places this theorem immediately after 0248 and immediately before

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

The target branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal routing theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0250 `branchB_false_of_goldenConjugateCoprimeCore`**:

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

Declaration 0249 lifts the conjugate-coprime core to a signed Branch-A refuter. Declaration 0250 then passes that refuter to the existing Branch-B routing theorem and propagates the contradiction back to the original counterexample packet.
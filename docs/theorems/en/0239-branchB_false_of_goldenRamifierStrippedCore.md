# 0239 — `branchB_false_of_goldenRamifierStrippedCore`

## Lean type

```lean
/-- The stripped core also closes every routed Branch-B counterexample pack. -/
theorem branchB_false_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

This is a `theorem`. It takes the contradiction core for ramifier-stripped packets from 0237 `SignedGoldenRamifierStrippedCore`, lifts it to a `SignedBranchARefuter` through 0238, and then feeds that refuter into the existing Branch-B routing theorem to derive `False` from the original `CounterexamplePack`.

## Mathematical statement

Conceptually, the theorem takes three inputs:

- `hCore`: every ramifier-stripped packet is contradictory;
- `hPack`: a `CounterexamplePack x y z` representing an FLT5 counterexample candidate;
- `hBranch`: the Branch-B condition `¬ 5 ∣ z - y`.

Declaration 0238 already establishes

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}.
$$

An upstream routing theorem then provides

$$
\mathrm{SignedBranchARefuter}
\Longrightarrow
\bigl(\mathrm{CounterexamplePack}\land \neg 5\mid(z-y)\bigr)
\Longrightarrow
\bot.
$$

The present theorem composes those two steps and yields

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\bigl(\mathrm{CounterexamplePack}\land \neg 5\mid(z-y)\bigr)
\Longrightarrow
\bot.
$$

Thus this theorem proves no new integer or golden-order identity. Its mathematical role is that of a **routing / lifting bridge** that transports an already-established contradiction receiver back to the original Branch-B entry point.

## Role in the full proof

Inside `SignedGoldenRamifierStripped.lean`, exceptional five-adic data are converted into a golden integer

$$
\alpha=M+N\varphi,
$$

and the visible ramifier

$$
\tau=2+\varphi
$$

is removed once, producing

$$
\alpha=\tau\beta.
$$

Declarations 0231–0237 package this stripped state and abstract the remaining arithmetic contradiction as a receiver contract.

Declaration 0238 lifts that local core to `SignedBranchARefuter`. The present declaration then lifts once more and reconnects the result to the pre-existing Branch-B routing layer.

The conceptual pipeline is therefore

$$
\text{Branch-B counterexample}
\longrightarrow
\text{signed Branch-A normal form}
\longrightarrow
\text{ramifier-stripped packet}
\longrightarrow
\bot.
$$

This separation keeps the golden-order arithmetic independent of the outer `CounterexamplePack` routing details, while the routing layer does not need to know anything about `beta`, `tau`, norms, or conjugation.

## Direct dependencies

The direct named dependencies are:

- 0237 `SignedGoldenRamifierStrippedCore`
- 0238 `signedBranchARefuter_of_goldenRamifierStrippedCore`
- `branchB_false_of_signedBranchARefuter`

The statement also mentions:

- `CounterexamplePack`
- the Branch-B condition `¬ 5 ∣ z - y`

The direct dependency chain is

$$
hCore
\xrightarrow{\text{0238}}
\mathrm{SignedBranchARefuter}
\xrightarrow{\text{Branch-B routing}}
\bot.
$$

## Proof flow

The proof is a single `exact` application:

```lean
by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

1. Apply 0238 to `hCore` and obtain a `SignedBranchARefuter`.
2. Pass that refuter together with `hPack` and `hBranch` to `branchB_false_of_signedBranchARefuter`.
3. The result has type `False`, so the goal closes immediately.

There is no case split, rewrite, simplification, ring normalization, or arithmetic tactic. The proof is pure theorem composition.

## Lean-specific processing

Lean treats theorems as functions, so

```lean
signedBranchARefuter_of_goldenRamifierStrippedCore hCore
```

is itself a term of type `SignedBranchARefuter`. That term is passed directly as the first argument to

```lean
branchB_false_of_signedBranchARefuter.
```

The indices `{x y z : ℕ}` are implicit binders. Lean infers them from the type of `hPack : CounterexamplePack x y z` and from `hBranch`.

The expression `hBranch : ¬ 5 ∣ z - y` is parsed as `¬ (5 ∣ z - y)`. The theorem does not unfold divisibility; it simply forwards the already-established Branch-B routing condition to the upstream theorem.

## Redundancy and duplication

Logically, the theorem is a thin wrapper. Downstream code could write

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

directly and obtain the same result.

The named theorem nevertheless has clear API value:

- it exposes the connection between the stripped-core layer and the Branch-B routing layer as a named boundary;
- downstream proofs do not need to know that 0238 is the intermediate adapter;
- the stripped-core implementation can change without forcing callers to depend on its internal lifting path;
- the theorem museum can follow the dependency pipeline declaration by declaration.

The redundancy is therefore best viewed as deliberate architectural API redundancy rather than accidental duplication.

## Optimization candidates

1. **Keep the current named theorem**
   - preserves the clearest dependency boundary.

2. **Use term-style syntax**

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

   could likely be placed directly after `:=`.

3. **Introduce a generic contradiction-lifting helper**
   - the pattern is just composition of `A → B` with `B → False`, but the abstraction overhead would probably outweigh any benefit for a one-line bridge.

4. **Standardize routing theorem names**
   - a consistent `..._of_<Core>` / `branchB_false_of_<Core>` pattern would make the dependency graph easier to scan.

The main optimization priority is therefore API consistency rather than local proof compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but this theorem itself needs only a very small Lean / Mathlib surface:

- dependent function application;
- `False`;
- natural numbers and divisibility notation.

Most of the real dependency weight lies in project-local declarations such as `SignedBranchARefuter`, `CounterexamplePack`, and the stripped-core adapter.

The theorem in isolation should not require all of `Mathlib`, but the enclosing module depends on the five-adic packet and golden-order development. Therefore import minimization should be measured at module scope. No Lean build is performed in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes, although the theorem is tiny. Natural variants are:

- A: current `by exact ...` proof;
- B: term-style `:= ...` composition;
- C: implementation through a generic contradiction-composition helper.

Useful comparison axes include proof-term size, elaboration stability, visibility of the dependency boundary, source-audit readability, and the blast radius of future routing-API changes.

A versus B is especially clean because the mathematics is identical and only the Lean presentation style changes.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0238 and immediately before 0240 `SignedGoldenFifthPowerUpToUnitCore`.

Japanese and English PDFs are present on the target branch, but this declaration is an internal routing bridge and no exact PDF page or section was identified in this pass. No page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0240 `SignedGoldenFifthPowerUpToUnitCore`**:

```lean
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

Declarations through 0239 are still concerned with routing contradiction receivers. Declaration 0240 changes mode and specifies the central algebraic output required from a stripped packet:

$$
\beta=\varepsilon\gamma^5.
$$

From there the proof moves into conjugate coprimality, Euclidean-domain gcd theory, and fifth-power factor extraction.
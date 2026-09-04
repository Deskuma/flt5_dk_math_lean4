# 0234 — `signedGoldenRamifierStrippedPacket_of_exceptional`

## Lean type

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

This is a `noncomputable def`, not a theorem. It takes the existence result proved in 0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` and selects one actual `SignedGoldenRamifierStrippedPacket u v w` for direct downstream use.

## Mathematical statement and meaning of the declaration

Declaration 0233 proves that from an exceptional packet `p`, a ramifier-stripped packet exists:

$$
\exists P:\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w).
$$

Declaration 0234 adds no new number-theoretic fact. Instead, it chooses one representative

$$
P=\operatorname{choice}(\text{the existence proof from 0233}).
$$

The selected packet carries all fields of 0231, so downstream code can directly access certificates such as

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

and

$$
\tau\nmid\beta.
$$

## Role in the full proof

Declarations 0231–0234 form the ramifier-stripping block.

- 0231 defines the target stripped-packet structure.
- 0232 proves the primitive certificate `5 ∤ b`.
- 0233 constructs a proof that the stripped-packet type is `Nonempty`.
- 0234 selects an actual packet object and exposes it as a data-level API.

This lets downstream modules write code conceptually like

```lean
let p' := signedGoldenRamifierStrippedPacket_of_exceptional p
```

and then project `p'.beta`, `p'.beta_norm`, `p'.tau_not_dvd_beta`, and the other stored certificates without repeatedly destructuring an existential witness.

Thus 0234 is the boundary that turns an existence theorem into a consumer-friendly data object.

## Direct dependencies

The direct dependency surface is very small:

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`
- `Classical.choice`

All number-theoretic work—factor extraction, norm arithmetic, and five-adic primitiveness—has already been completed in 0233. This declaration does not recompute any of it.

Conceptually,

$$
\texttt{Nonempty P}
\longrightarrow
\texttt{Classical.choice}
\longrightarrow
P.
$$

## Construction flow

The body is a single expression:

```lean
Classical.choice
  (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

1. Apply 0233 to `p` and obtain `Nonempty (SignedGoldenRamifierStrippedPacket u v w)`.
2. Pass that proof to `Classical.choice`.
3. Return one inhabitant of `SignedGoldenRamifierStrippedPacket u v w`.

The explicit formulas for the witnesses are not unfolded here. From the consumer's point of view, the important fact is only that the selected object satisfies all fields required by 0231.

## Lean-specific processing

`Classical.choice` extracts an element of `α` from a proof of `Nonempty α`.

Because this is a classical choice operation, the declaration is marked `noncomputable def`. It is accepted by Lean as a definition, but it does not claim to provide an executable witness-extraction algorithm.

This is notable because 0233 itself constructs `k`, `beta`, and all certificates explicitly. The current design nevertheless places a clean boundary between:

- proposition-valued existence in 0233, and
- data-valued selection in 0234.

That separation keeps the long construction proof independent from the simple downstream API.

## Redundancy and duplication

The clearest possible duplication is the two-layer design formed by 0233 and 0234.

Since 0233 explicitly constructs all witnesses, one could in principle move that constructor logic into a direct definition such as

```lean
def signedGoldenRamifierStrippedPacket_of_exceptional ... := { ... }
```

and then derive a `Nonempty` theorem from the resulting object.

The current organization still has useful advantages:

- the complicated proof-producing part can be audited independently;
- the existence statement does not itself depend on exposing a chosen object;
- downstream code gets a simple object-valued API;
- the theorem / definition boundary makes the purpose of each declaration obvious.

So the design is two-layered in code but not gratuitously redundant.

## Optimization candidates

1. **Merge into a direct constructor definition**
   - move the explicit witness construction from 0233 into a data-valued `def` and derive `Nonempty` afterward.

2. **Keep the current theorem / choice split**
   - this remains attractive when proof auditability is a priority.

3. **Introduce a shared constructor helper**
   - a helper could be reused by both an existence theorem and a selected-object definition, reducing duplication while preserving both APIs.

4. **Expose only accessor theorems**
   - if downstream consumers only need particular fields, one could avoid exposing a selected packet object and publish existential or accessor theorems instead.

At present, the current one-line choice definition is already locally optimal in simplicity.

## Required Mathlib imports and import optimization

The direct Mathlib surface needed by this declaration is mainly:

- `Nonempty`
- `Classical.choice`

The golden-order and five-adic dependencies belong to 0231 and 0233 upstream.

Therefore this declaration alone should require far less than all of `Mathlib`. However, the surrounding module contains the long proof from 0233 using arithmetic tactics, prime divisibility, casts, and ring reasoning, so import minimization must be evaluated at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. The alternatives are easy to compare:

- A: current `Nonempty` theorem + `Classical.choice`
- B: direct explicit data constructor
- C: existential theorem API only, without a selected packet object
- D: shared constructor helper reused by both theorem and definition

Useful comparison axes include proof auditability, noncomputable dependencies, downstream ergonomics, code duplication, locality of constructor logic, and refactoring robustness.

The A-vs-B comparison is particularly useful for studying the Lean design tradeoff between separating existence from choice and directly exposing an explicit witness.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The current 0233 source document records that the next declaration is exactly

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

Japanese and English PDFs also exist on the target branch, but the exact page or section corresponding to this one-line choice definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration should be selected by rereading the repository source immediately after 0234 in the next pass.

Now that a ramifier-stripped packet can be obtained as a data object, the development is expected to move into the conjugate-coprimality block, where `beta` and `goldenConj beta` are analyzed for common factors. The exact declaration name and order should nevertheless be confirmed from the repository rather than inferred from memory.

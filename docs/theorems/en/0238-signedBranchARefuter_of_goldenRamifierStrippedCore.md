# 0238 — `signedBranchARefuter_of_goldenRamifierStrippedCore`

## Lean type

```lean
/-- A refuter for all stripped packets closes both signed orientations. -/
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

This is a `theorem`. It lifts the local contradiction contract from 0237 `SignedGoldenRamifierStrippedCore`—which says that every packet with the visible ramifier removed leads to `False`—to the higher-level `SignedBranchARefuter` interface.

## Mathematical statement

Declaration 0237 is conceptually the proposition

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w)
\longrightarrow \bot.
$$

On the other hand, `SignedBranchARefuter` is the receiver contract

$$
\forall u,v,w,\quad
\mathrm{SignedBranchANormalForm}(u,v,w)
\longrightarrow \bot.
$$

The present theorem inserts the already constructed map

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

between them. It therefore transports a contradiction on stripped packets back to a contradiction on every signed Branch-A normal form.

No new number-theoretic identity is proved here. The mathematical content is exactly the composition

$$
hNF
\longmapsto
\mathrm{signedGoldenRamifierStrippedPacket\_of\_normalForm}(hNF)
\longmapsto
\bot.
$$

## Role in the full proof

Inside `SignedGoldenRamifierStripped.lean`, the exceptional five-adic packet produces a golden integer

$$
\alpha=M+N\varphi,
$$

from which the visible ramifier

$$
\tau=2+\varphi
$$

is removed once, giving

$$
\alpha=\tau\beta.
$$

The stripped packet also retains certificates such as

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

Declaration 0237 abstracts the remaining arithmetic problem as the statement that every such stripped state is contradictory. Declaration 0238 is the adapter that transports that local core back to the signed Branch-A normal form layer.

This bridge means that downstream arguments do not need to reopen the construction of the stripped packet. They can work through the existing high-level `SignedBranchARefuter` API. The immediately following declaration 0239 passes the result of 0238 to `branchB_false_of_signedBranchARefuter`, closing the routed Branch-B candidate.

Conceptually, the hierarchy is

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
\Longrightarrow
\text{Branch-B contradiction}.
$$

## Direct dependencies

The direct dependencies are:

- 0237 `SignedGoldenRamifierStrippedCore`
- `SignedBranchARefuter`
- `signedGoldenRamifierStrippedPacket_of_normalForm`

The last declaration packages the existing pipeline from a signed normal form through the five-adic power split and square-golden exceptional packet to the ramifier-stripped packet.

The present theorem does not directly use coordinate formulas on `GoldenInt`, norm arithmetic, divisibility, or the Euclidean-domain structure. Those details are encapsulated in the lower layers that construct the stripped packet.

## Proof flow

The proof has only two conceptual steps:

```lean
by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

1. `intro u v w hNF` receives arbitrary indices together with a signed normal-form packet, as required by `SignedBranchARefuter`.
2. `signedGoldenRamifierStrippedPacket_of_normalForm hNF` constructs the corresponding stripped packet.
3. Applying `hCore` to that packet produces `False` and closes the goal.

There is no case split, arithmetic tactic, rewrite, or coordinate calculation. By this point the preceding interfaces are strong enough that only function composition remains.

## Lean-specific processing

Both `SignedGoldenRamifierStrippedCore` and `SignedBranchARefuter` are transparent `abbrev ... : Prop` declarations. Lean can unfold them as necessary, so `intro u v w hNF` behaves as ordinary function introduction.

The indices are implicit binders in the underlying contracts, but tactic mode introduces them as local variables.

`signedGoldenRamifierStrippedPacket_of_normalForm` is a `noncomputable def`, because its construction ultimately passes through classical choice. That causes no difficulty here: this theorem lives in `Prop` and never evaluates the chosen packet computationally. It only needs a term of the required packet type.

In

```lean
exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

Lean infers the implicit indices of `hCore` from the type of the stripped packet supplied as its argument.

## Redundancy and duplication

Logically, this theorem is a very thin wrapper. Downstream code could repeat

```lean
hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

each time and obtain the same result, so a minimal API could omit the named theorem.

However, the development consistently places a receiver contract and a lifting theorem at each reduction boundary. The five-adic core, power-split core, square-golden core, and related stages follow the same architectural pattern.

Thus the redundancy here is intentional API redundancy. The theorem name makes the dependency boundary visible and lets downstream code depend on the high-level refuter rather than on the details of packet construction.

## Optimization candidates

1. **Keep the present theorem**
   - this preserves the clearest reduction-layer boundary.

2. **Use a term-style definition**

```lean
fun hNF => hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

   may shorten the proof. Exact elaboration of the implicit binders is not verified here because this museum pass does not run a Lean build.

3. **Introduce a generic core-lifting helper**
   - a generic combinator can turn `A → B` and `B → False` into `A → False`, but adding abstraction for a one-line proof may make the actual proof route less visible.

4. **Regularize naming for packet-conversion pipelines**
   - if more layers are added, consistently naming the normal-form → five-adic → power-split → exceptional → stripped conversions may improve navigation more than shortening this local proof.

At present, preserving the named architectural boundary is more valuable than saving a line of tactic code.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The theorem itself, however, directly requires only basic dependent-function elaboration and the project declarations listed above. It uses no advanced Mathlib theorem or arithmetic tactic.

Its effective dependencies are almost entirely internal:

- `SignedGoldenRamifierStrippedCore`
- `SignedBranchARefuter`
- `signedGoldenRamifierStrippedPacket_of_normalForm`

Therefore the import surface of this declaration in isolation is very small. The complete module still depends on the upstream golden-order, five-adic, and square-golden layers, so actual import minimization must be measured at module scope. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes, although it is a small challenge. Useful variants are:

- A: current tactic proof with `intro` and `exact`
- B: direct term-style lambda composition
- C: implementation through a generic contradiction-lifting combinator

Useful comparison axes are proof-term size, visibility of the dependency boundary, elaboration robustness, audit readability, and the size of the change required if the packet-conversion API is refactored.

A versus B is especially clean because the mathematics is identical; only Lean style and API readability differ.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this theorem appears immediately after 0237 `SignedGoldenRamifierStrippedCore` and immediately before `branchB_false_of_goldenRamifierStrippedCore`.

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. This declaration is an internal receiver bridge, and no exact PDF page or section corresponding to it was identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0239 `branchB_false_of_goldenRamifierStrippedCore`**:

```lean
theorem branchB_false_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

Declaration 0238 lifts the stripped core to `SignedBranchARefuter`; 0239 then passes that refuter through the existing signed-routing theorem to derive a contradiction for the original Branch-B counterexample pack.
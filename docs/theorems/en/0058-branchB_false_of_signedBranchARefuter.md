# 0058 — `branchB_false_of_signedBranchARefuter`

## Lean type

```lean
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
  · exact hRefuter hDiff
  · exact hRefuter hSum
```

This theorem states that, once a `SignedBranchARefuter` is available for eliminating every signed Branch A normal form, any `CounterexamplePack` satisfying the Branch B condition is itself contradictory.

## Mathematical statement

There are three assumptions.

1. `hRefuter : SignedBranchARefuter`: every signed Branch A normal form can be refuted.
2. `hPack : CounterexamplePack x y z`: `x,y,z` form a positive primitive Fermat-five candidate.
3. `hBranch : ¬ 5 ∣ z - y`: the Branch B condition, namely that the gap `z-y` is not divisible by 5.

The routing theorem from the preceding articles sends such a Branch B candidate to one of

$$
\operatorname{SignedBranchANormalForm}(y,x,z)
\quad\text{or}\quad
\operatorname{SignedBranchANormalForm}(x,y,z).
$$

Because `SignedBranchARefuter` sends either coordinate ordering of a normal form to `False`, both branches are contradictory. Thus

$$
\operatorname{CounterexamplePack}(x,y,z)
\land 5\nmid(z-y)
\land \operatorname{SignedBranchARefuter}
\Longrightarrow \bot.
$$

## Role in the full proof

This theorem is the **closure bridge** that composes the routing theorem from 0056 with the refuter contract from 0057.

The upstream layer handles the arithmetic of Branch B and, when necessary, swaps `x,y` before normalizing to a common `SignedBranchANormalForm`. The downstream layer does not need to know where the normal form came from; it only has to return `False`. This theorem connects those two layers.

```text
CounterexamplePack x y z
       +
5 ∤ z-y
       ↓ 0056
SignedBranchANormalForm y x z
          ∨
SignedBranchANormalForm x y z
       ↓ 0057
      False
```

Consequently, later five-adic, power-split, and golden-order layers do not need to reimplement the Branch B case split. Each layer only needs to construct a `SignedBranchARefuter`, after which this theorem closes Branch B as a whole.

## Direct dependencies

The direct dependencies are:

- `SignedBranchARefuter`
- `CounterexamplePack`
- `signedBranchA_normalForm_of_branchB`

In particular, the producer used by the proof is

```lean
signedBranchA_normalForm_of_branchB hPack hBranch
```

whose result type is

```lean
SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z
```

Because `SignedBranchARefuter` quantifies implicitly over `u v w`, Lean infers the coordinate triple from the type of the normal form, so each branch needs only `hRefuter hDiff` or `hRefuter hSum`.

## Proof flow

### 1. Route the Branch B candidate to a signed normal form

```lean
rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
```

This splits into two cases:

- `hDiff : SignedBranchANormalForm y x z`
- `hSum : SignedBranchANormalForm x y z`

The first is the difference orientation; internally, 0056 reaches it through `CounterexamplePack.swap`. The second is the sum orientation and preserves the original coordinate order.

### 2. Feed the difference branch to the refuter

```lean
exact hRefuter hDiff
```

The implicit arguments of `hRefuter` are inferred from `hDiff` as `(u,v,w)=(y,x,z)`.

### 3. Feed the sum branch to the refuter

```lean
exact hRefuter hSum
```

Here they are inferred as `(u,v,w)=(x,y,z)`.

Both branches therefore close the goal `False`.

## Lean-specific processing

### `rcases ... with hDiff | hSum`

This destructures the disjunction and names the proof object in each branch directly. It is a compact alternative to a more verbose `cases` block.

### Implicit argument inference

`SignedBranchARefuter` has type

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

so applying `hRefuter hDiff` determines `u=y, v=x, w=z` from the type of `hDiff`. No coordinate triple is supplied manually, which lets the type checker enforce consistency even in the swapped branch produced by 0056.

### A closure theorem returning `False` directly

The conclusion is exactly `False`, rather than another wrapper proposition. Consumers can therefore write

```lean
exact branchB_false_of_signedBranchARefuter hRefuter hPack hBranch
```

and use the contradiction immediately.

## Redundancy and duplication

The proof is only three lines and contains essentially no structural redundancy.

The two branches duplicate

```lean
exact hRefuter ...
```

but keeping them explicit preserves the semantic distinction between difference and sum routing. The proof could be compressed to something like

```lean
rcases signedBranchA_normalForm_of_branchB hPack hBranch with h | h <;>
  exact hRefuter h
```

but this removes the meaningful names `hDiff` and `hSum`. For a theorem museum, the current form is more readable.

## Optimization candidates

### 1. Tactic compression is possible but low-value

Using `<;>` can reduce line count, but this proof is already near-minimal, so the readability tradeoff is not compelling.

### 2. Functional presentation with a generic sum eliminator

In principle one could use `Or.elim` and write something close to

```lean
exact Or.elim
  (signedBranchA_normalForm_of_branchB hPack hBranch)
  hRefuter
  hRefuter
```

The left and right normal forms carry different type parameters, however, so Lean may require annotations depending on elaboration. The current `rcases` form makes the type flow explicit and robust.

### 3. Do not over-abstract this bridge

One could abstract the general pattern of deriving `False` from `P ∨ Q`, `P → False`, and `Q → False`. Here, however, routing into `SignedBranchANormalForm` is an important architectural boundary in the formalization. Keeping a named project-specific closure theorem is valuable documentation.

## Required Mathlib imports

The generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

for the artifact as a whole.

This theorem itself directly uses only `rcases`, disjunction elimination, implicit argument inference, and function application; it calls no new arithmetic tactic or Mathlib theorem. Its substantive dependencies are the project declarations `SignedBranchARefuter` and `signedBranchA_normalForm_of_branchB`.

The exact import list of the original split module `DkMath/FLT/Five/SignedBranchA.lean` cannot be recovered from the generated standalone artifact inspected in this run, so the following is **inference**. If imports are minimized, the full module must be audited because the same file also contains modular arithmetic and finite-classification proofs. This theorem alone is not sufficient evidence that `Mathlib` can be removed from the module.

### Import optimization candidate

For this theorem in isolation, no special extra Mathlib import appears necessary beyond the logic and the project modules defining its dependencies. At module level, however, `SignedBranchA.lean` also contains uses of finite residue reasoning and tactics such as `norm_num`/case analysis, so import minimization should be performed against the entire file.

## Comparator challenge suitability

**Suitable, with low-to-medium difficulty.**

A challenge can expose an API of the form

```lean
hRoute : A → B ∨ C
hRefuteB : B → False
hRefuteC : C → False
```

or use the project types directly, then ask for the smallest proof that closes a Branch B candidate.

Useful comparison points are:

- `rcases` vs `cases` vs `Or.elim`
- correct use of implicit arguments
- whether the solution relies on the type system for the swapped coordinate order
- whether it unnecessarily re-proves the arithmetic hidden behind 0056

It is especially good as a proof-engineering challenge about composing an existing API instead of unfolding and rebuilding lower-level arguments.

## Evidence and inference

The declaration of `branchB_false_of_signedBranchARefuter`, its complete three-line proof, and its position at the end of `SignedBranchA.lean` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The same artifact shows that `SignedFiveAdic.lean` follows next and develops `SignedFiveAdicSource`, `SignedFiveAdicPacket`, `SignedFiveAdicCore`, `signedBranchARefuter_of_fiveAdicCore`, and `branchB_false_of_fiveAdicCore`.

Existing Japanese and English PDFs were searched for by the known filenames during this run, but their concrete contents could not be retrieved from the expected GitHub paths. Therefore no PDF-derived claim was added. The corresponding PDF passage is **unverified**, and nothing has been guessed from it.

## Next declaration to read

Next, at the entrance to the new five-adic layer, read

```lean
DkMath.FLT.Five.SumGN5
```

This is the positive natural-number residual for the sum orientation near the beginning of `SignedFiveAdic.lean`. The difference orientation can use the existing `GN5 (w-v) v`, whereas the sum orientation takes `(u+v)` as its carrier and therefore needs a corresponding residual defined inside `ℕ`. This starts the preparation for merging both signed orientations into one exact five-adic packet.
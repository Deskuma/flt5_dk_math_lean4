# 0057 — `SignedBranchARefuter`

## Lean type

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

`SignedBranchARefuter` is not a theorem but an abbreviation (`abbrev`) of a proposition. It expresses the common refuter contract saying that, for arbitrary natural numbers `u v w`, any `SignedBranchANormalForm u v w` can be sent to `False`.

## Mathematical statement

The signed Branch A normal form constructed in the preceding articles packages a positive primitive Fermat-5 candidate together with one of the two exceptional five-adic orientations. This declaration collects into one proposition the requirement that either orientation must eventually lead to contradiction.

Conceptually,

$$
\forall u,v,w\in\mathbb N,
\quad
\operatorname{SignedBranchANormalForm}(u,v,w)
\Longrightarrow \bot.
$$

No concrete reason for the contradiction is supplied here. Later layers—five-adic valuation, power splitting, square-golden reduction, golden-order arithmetic, and so on—implement this contract.

## Role in the overall proof

`SignedBranchARefuter` is the interface separating the front-end routing from the back-end descent.

The front end uses `signedBranchA_normalForm_of_branchB` to route a Branch B candidate to

```text
SignedBranchANormalForm y x z
        ∨
SignedBranchANormalForm x y z
```

The back end does not need to know where the coordinates came from or which routing branch was taken. It only needs to accept a normal form and return `False`.

Thus the proof acquires the clear two-stage shape

```text
Branch B candidate
      ↓ routing
SignedBranchANormalForm
      ↓ SignedBranchARefuter
     False
```

## Direct dependencies

The only direct type dependency is:

- `SignedBranchANormalForm u v w`

That structure contains `CounterexamplePack u v w` and `SignedBranchAOrientation u v w`.

The declaration itself does not mention `signedBranchA_normalForm_of_branchB` in its type, but the immediately following theorem `branchB_false_of_signedBranchARefuter` composes the two, so article 0056 is the direct producer in the explanatory dependency order.

## Proof flow

Because this declaration is an `abbrev`, it has no proof body. After unfolding its meaning, an implementation has the shape

```lean
intro u v w hNF
-- goal: False
-- hNF : SignedBranchANormalForm u v w
...
```

That is, an implementer receives arbitrary `u v w` and a normal form `hNF`, and must construct a contradiction.

Later source code actually builds this contract repeatedly from deeper cores. At the five-adic layer, for example, the pattern is conceptually

```lean
intro u v w hNF
exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

where the normal form is converted into a more precise packet and that packet is passed to a core that excludes it.

## Lean-specific processing

### `abbrev ... : Prop`

`abbrev` gives a lightweight definitional alias. No new inductive type or structure is created; the universally quantified function type

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

is simply given a name.

### Implicit arguments `{u v w : ℕ}`

The three coordinates are implicit arguments, so in ordinary use one can write `hRefuter hNF` and Lean can infer `u v w` from the type of `hNF`.

### `→ False` and negation

In Lean, `¬ P` is notation for `P → False`. Therefore this contract is definitionally equivalent in spirit to

```lean
∀ {u v w : ℕ}, ¬ SignedBranchANormalForm u v w
```

The current function-style form is convenient for consumers because it can be applied directly as `hRefuter hNF`.

## Redundancy and duplication

This declaration is extremely small and has essentially no implementation redundancy.

Logically, however, it could also be written as

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, ¬ SignedBranchANormalForm u v w
```

After unfolding negation, this is the same type, so there is no mathematical difference.

Later layers also introduce many contracts of the same general shape, such as `SignedFiveAdicCore` and `SignedFiveAdicPowerSplitCore`, each sending an arbitrary packet to `False`. This repetition is intentional and makes layer boundaries explicit, although a generic refuter type could abstract it.

## Optimization candidates

### 1. Abstract a generic refuter

For example:

```lean
abbrev Refuter (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {u v w : ℕ}, P u v w → False
```

Then one could write

```lean
abbrev SignedBranchARefuter := Refuter SignedBranchANormalForm
```

This reduces repetition, but it can also weaken the explanatory value of layer-specific names. From the museum perspective, the current explicit naming is quite reasonable.

### 2. Use `¬` notation

Replacing `→ False` with `¬` would make the negation visually explicit, but it would not change downstream function application. This is mostly a style choice.

## Required Mathlib imports

The generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch imports

```lean
import Mathlib
```

for the complete artifact.

`SignedBranchARefuter` itself uses no special Mathlib theorem or tactic. It only needs `ℕ`, `Prop`, `False`, and the project declaration `SignedBranchANormalForm`.

The exact import line of the original split module `DkMath/FLT/Five/SignedBranchA.lean` cannot be recovered from the generated artifact, so the following is explicitly a **conjecture**: a minimized module would likely need only the project module that provides `SignedBranchANormalForm` and its transitive dependencies rather than all of Mathlib.

### Import optimization candidate

This declaration alone does not justify any additional Mathlib import. Import minimization should be decided by auditing all tactics and arithmetic used in `SignedBranchA.lean`, rather than by shrinking imports solely around this `abbrev`.

## Comparator challenge suitability

**Yes, but low difficulty.**

A suitable challenge would ask:

> Define a proposition-level contract that excludes `SignedBranchANormalForm u v w` for arbitrary triples, and make it directly applicable as a function by consumers.

Useful comparison points are:

- `abbrev` versus `def`
- `→ False` versus `¬`
- use of implicit arguments
- avoiding an unnecessary structure

This is more of a Lean API-design Comparator challenge than a mathematical proof challenge.

## Evidence and conjecture

The declaration of `SignedBranchARefuter`, the fact that `branchB_false_of_signedBranchARefuter` immediately follows it, and the existence of later implementation bridges such as `signedBranchARefuter_of_fiveAdicCore` were confirmed in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The exact import line of the original split `SignedBranchA.lean` is not recoverable from the standalone artifact, so statements about minimal imports are explicitly marked as conjectural.

## Next theorem to read

Next:

```lean
DkMath.FLT.Five.branchB_false_of_signedBranchARefuter
```

This theorem directly composes the routing theorem from article 0056 with the refuter contract from this article, yielding `False` from any Branch B candidate. At that point, the front-end branch routing and the shared back-end descent become fully connected.

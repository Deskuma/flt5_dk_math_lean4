# 0117 — `branchB_false_of_squareGoldenExceptionalCore`

## Lean type

```lean
/-- The same square-golden core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_squareGoldenExceptionalCore hCore) hPack hBranch
```

This theorem is a closure theorem: assuming a core that sends every square-golden exceptional packet to contradiction, every `CounterexamplePack` satisfying the Branch-B condition is contradictory.

## Mathematical statement

There are three inputs.

1. `hCore : SignedSquareGoldenExceptionalCore`
2. `hPack : CounterexamplePack x y z`
3. `hBranch : ¬ 5 ∣ z - y`

Conceptually, `SignedSquareGoldenExceptionalCore` is the refuter

$$
\forall u,v,w,\quad
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot.
$$

On the other hand, from `hPack` and the Branch-B condition

$$
5\nmid(z-y),
$$

0058 `branchB_false_of_signedBranchARefuter` returns `False` whenever it is given a refuter eliminating every signed Branch-A normal form.

By 0116 `signedBranchARefuter_of_squareGoldenExceptionalCore`, we have

$$
\operatorname{SignedSquareGoldenExceptionalCore}
\longrightarrow
\operatorname{SignedBranchARefuter}.
$$

Therefore the present theorem composes two existing transformations to obtain

$$
\operatorname{SignedSquareGoldenExceptionalCore}
\longrightarrow
\bigl(\operatorname{CounterexamplePack}(x,y,z)\land 5\nmid(z-y)\bigr)
\longrightarrow
\bot.
$$

No new integer identity, five-adic valuation fact, or golden-integer arithmetic is proved here. Its mathematical content is the transport of an already established contradiction interface all the way to the Branch-B closure API.

## Role in the full proof

This theorem is the final declaration of `SignedSquareGoldenExceptional.lean`, so it serves as the **exit** of that module.

The preceding flow can be summarized as follows.

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
  → False
```

In 0116, that packet-level contradiction was pulled back to

```text
SignedBranchANormalForm → False
```

namely `SignedBranchARefuter`.

0117 then uses the existing signed-routing theorem 0058 to pull the contradiction back once more:

```text
CounterexamplePack + Branch-B condition
  → Signed Branch-A routing
  → SignedBranchARefuter
  → False
```

Consequently, no matter which golden-order or descent argument is later used to implement the square-golden exceptional core, once that implementation satisfies `SignedSquareGoldenExceptionalCore`, it connects automatically to the Branch-B contradiction. This interface separation is the theorem's most important architectural role.

## Direct dependencies

### `SignedSquareGoldenExceptionalCore`

The packet-level contradiction contract explained in 0115.

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ},
    SignedSquareGoldenExceptionalPacket u v w → False
```

### `signedBranchARefuter_of_squareGoldenExceptionalCore`

The adapter theorem explained in 0116.

```lean
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

It converts the packet-level core into a normal-form-level refuter.

### `branchB_false_of_signedBranchARefuter`

The existing Branch-B closure theorem explained in 0058.

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

Because this theorem handles the difference/sum signed-orientation split internally, 0117 does not need to expose those cases again.

### `CounterexamplePack`

The basic packet storing a positive primitive FLT5 candidate. 0117 does not inspect its fields directly; it forwards the packet unchanged to 0058.

### Branch-B condition `¬ 5 ∣ z - y`

The assumption that activates Branch-B routing. 0117 performs no divisibility reasoning itself and simply forwards this hypothesis to 0058.

## Proof flow

The proof is a single composition.

1. Pass `hCore` to 0116.
2. Obtain a `SignedBranchARefuter`.
3. Pass that refuter together with `hPack` and `hBranch` to 0058.
4. Obtain `False`.

As a Lean term, the entire proof is

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_squareGoldenExceptionalCore hCore)
  hPack
  hBranch
```

The mathematical composition is therefore

$$
\text{square-golden core}
\xrightarrow{\;0116\;}
\text{signed Branch-A refuter}
\xrightarrow{\;0058\;}
\text{Branch-B contradiction}.
$$

## Lean-specific processing

### The theorem closes with `exact` alone

There is not even an `intro` in the proof body. The theorem parameters are already bound in the declaration header, and the goal is `False`, so Lean accepts the compound term of exactly that expected type.

### Inference of implicit arguments

The `{x y z : ℕ}` parameters of `branchB_false_of_signedBranchARefuter` are implicit. Lean infers the indices from `hPack : CounterexamplePack x y z` and the type of `hBranch`, so explicit arguments such as

```lean
(x := x) (y := y) (z := z)
```

are unnecessary.

Likewise, the internal indices of the `SignedBranchARefuter` returned by 0116 are inferred when 0058 applies the refuter.

### Interface matching through `abbrev`

`SignedSquareGoldenExceptionalCore` and `SignedBranchARefuter` are proposition interfaces defined with `abbrev`. Reducibility lets Lean use them as their underlying function types, but 0117 does not need to expand either definition. The composition works entirely through the named interfaces.

### No algebra tactic appears

There is no `ring`, `omega`, `norm_num`, `simp`, `rw`, `push_cast`, or `exact_mod_cast`. The substantial mathematics—square-golden identities, signed routing, and the five-adic split—has already been isolated upstream.

## Redundancy and duplication

Logically, this theorem is a very thin wrapper.

Conceptually it has the form

```lean
A → B
B → C → D → False
-----------------
A → C → D → False
```

Moreover, 0116 itself is the adapter

```text
SignedSquareGoldenExceptionalCore
  → SignedBranchARefuter
```

so it would be possible in principle to inline 0116 and directly expand the producer in 0117.

For example, conceptually one could write

```lean
branchB_false_of_signedBranchARefuter
  (fun hNF => hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF))
  hPack hBranch
```

This, however, is less a removal of redundancy than a break in the abstraction boundary. The current theorem chain gives an explicit name to each layer transition and therefore documents the proof graph.

## Optimization candidates

### 1. Keep the current named adapter

This is the strongest default. The code is already near-minimal, and the division of responsibility between 0116 and 0058 is clear.

### 2. Inline 0116

The proof can be compressed into one larger term, but the important transition `SignedSquareGoldenExceptionalCore → SignedBranchARefuter` loses its name. The current form is preferable for maintainability and readability.

### 3. Generic refuter transport helper

A generic helper for precomposition of negations could abstract away families of adapters like 0116 and 0117.

However, theorem names serve as a mathematical routing map in this FLT5 development. Unless many structurally identical wrappers accumulate, generic abstraction offers little benefit.

### 4. Document the theorem chain at module level

A more useful improvement than reducing code may be to document

```text
ExceptionalCore → SignedBranchARefuter → Branch-B False
```

at module level. This theorem is exactly the module boundary exit, so the chain deserves to be visible in architectural documentation.

## Required Mathlib imports and import optimization candidates

The repository's standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The elements directly needed by 0117 are very small in number:

- `ℕ`
- `False`
- divisibility notation `∣`
- natural subtraction `z - y`
- the project declaration `CounterexamplePack`
- `SignedSquareGoldenExceptionalCore`
- `signedBranchARefuter_of_squareGoldenExceptionalCore`
- `branchB_false_of_signedBranchARefuter`

The proof body uses no Mathlib tactic.

Therefore `Mathlib` as a whole is unlikely to be necessary solely for this theorem in the modular source. However, in this repository the original modular source has been assembled into the standalone generated artifact, and the formal source inspected here is that generated section. We have not removed imports and run a Lean build, so the exact minimal import set is **unverified**.

A safe import-optimization exercise would first enumerate the project modules directly referenced by `SignedSquareGoldenExceptional.lean`, then test the transitive Mathlib imports with `lake build`. The theorem museum does not run Lean builds, so this remains an optimization candidate rather than a verified change.

## Comparator challenge suitability

**Yes. It is well suited to a proof-composition and abstraction-boundary comparison.**

Possible variants include:

- the current named two-stage composition,
- a version with 0116 inlined,
- an explicit lambda version using `fun hNF => ...`,
- a version using a generic refuter-transport helper,
- a fully inlined version that also exposes the signed-orientation routing from 0058.

Useful evaluation criteria are:

- line count,
- elaboration stability,
- locality of error messages,
- readability of dependencies,
- resistance to upstream implementation changes,
- the value of theorem names as proof-graph documentation.

The fully inlined version is especially instructive: it is likely to re-expose the difference/sum routing and packet construction, making the proof longer while weakening responsibility separation. The challenge therefore tests not merely which proof is shortest, but **why preserving API boundaries can produce a stronger formalization**.

## Correspondence with the existing PDFs

The target branch contains the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

and the TeX source archive `docs/pdf/TeX/TeX-FLT5_Fermat's_Last_Theorem_for_Exponent_Five-v0-r1.zip`.

The formal basis for this article is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The GitHub connector was not used to expand and compare the exact corresponding pages of the PDFs in this run. Therefore no PDF section or page number is guessed here. The PDFs are treated as confirmed narrative context, while the Lean declaration remains the final authority.

## Next declaration to read

This theorem is the final declaration of `SignedSquareGoldenExceptional.lean`. Immediately afterward the module closes and the next generated source, `DkMath/FLT/Five/GoldenOrder.lean`, begins.

Its first not-yet-explained declaration is not a theorem but the structure

```lean
/-- An integral pair representing `a+b*φ` in the basis `1,φ`, with `φ^2=φ+1`. -/
structure GoldenInt where
  fst : ℤ
  snd : ℤ
deriving DecidableEq
```

It represents the golden integer

$$
a+b\varphi,
\qquad \varphi^2=\varphi+1
$$

by an integral pair $(a,b)$.

By 0117, the interface saying “a square-golden exceptional core closes Branch B” is complete. The next module begins constructing the golden-order arithmetic that will eventually supply such a core. In dependency order, `GoldenInt` is therefore the natural declaration for article 0118.

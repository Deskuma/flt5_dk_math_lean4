# 0092 — `branchB_false_of_powerSplitCore`

## Lean type

```lean
theorem branchB_false_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

This theorem is the terminal theorem of `SignedFiveAdicPowerSplit.lean`. It lifts the exact power-split refuter supplied by 0090 `SignedFiveAdicPowerSplitCore` to a signed Branch-A refuter via 0091 `signedBranchARefuter_of_powerSplitCore`, then passes that refuter to 0058 `branchB_false_of_signedBranchARefuter` to close a routed Branch-B candidate.

## Mathematical statement

There are three assumptions.

1. Every `SignedFiveAdicPowerSplit u v w` is contradictory.
2. A positive primitive FLT5 candidate `CounterexamplePack x y z` is given.
3. The Branch-B condition $5\nmid z-y$ holds.

The conclusion is `False`.

Conceptually, the already established routing closes the composite

$$
\mathrm{CounterexamplePack}(x,y,z)
\land 5\nmid(z-y)
\longrightarrow
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\bot.
$$

Thus this theorem is not a new arithmetic lemma. It is a closure theorem that promotes a contradiction core on the power-split layer to a refutation of the whole Branch-B route.

## Role in the full proof

Along the FLT5 Branch-B route, upstream results turn `CounterexamplePack` together with $5\nmid z-y$ into a signed normal form, then into a five-adic packet, and finally into an exact power split.

This theorem closes that route from the opposite abstraction boundary:

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\xrightarrow{\;0091\;}
\mathrm{SignedBranchARefuter}
\xrightarrow{\;0058\;}
\text{Branch-B contradiction}.
$$

Consequently, once a concrete implementation of `SignedFiveAdicPowerSplitCore` is obtained downstream, Branch-B does not need to re-open the routed candidate and repeat its construction details.

In the source this theorem is immediately followed by the end of `SignedFiveAdicPowerSplit.lean`, after which `SquareGoldenBridge.lean` begins. It is therefore the final public closure API of the exact five-adic power-split layer.

## Direct dependencies

The direct dependencies are:

1. `SignedFiveAdicPowerSplitCore` (0090)
2. `signedBranchARefuter_of_powerSplitCore` (0091)
3. `branchB_false_of_signedBranchARefuter` (0058)
4. `CounterexamplePack` (0002)
5. the Branch-B condition `¬ 5 ∣ z - y`

The theorem itself does not inspect the fields of `SignedFiveAdicPowerSplit`, gcd facts, mod-$25$ facts, fifth-power decompositions, or `padicValNat`. Those details are sealed inside the power-split construction up through 0090 and inside the implementation of `hCore`.

## Proof flow

The proof is a single `exact`:

```lean
exact branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

Expanded, it has two steps.

1. `signedBranchARefuter_of_powerSplitCore hCore` turns the exact power-split contradiction core into a `SignedBranchARefuter`.
2. That refuter, together with `hPack` and `hBranch`, is passed to `branchB_false_of_signedBranchARefuter`, producing `False`.

Mathematically this is pure function composition. There is no new case split or formula manipulation in this theorem.

## Lean-specific processing

### 1. Closure through high-level APIs only

The proof body contains no `rw`, `simp`, `ring`, `omega`, or `norm_num`. All arithmetic work has already been absorbed into the types of the dependency theorems.

### 2. Implicit argument inference

The indices `{x y z : ℕ}` are inferred from `hPack` and `hBranch`. On the 0091 side, signed-normal-form indices are likewise inferred from witness types, so this theorem does not need to restate them.

### 3. Composition of proposition-valued refuters

`SignedFiveAdicPowerSplitCore` and `SignedBranchARefuter` are both function contracts that ultimately return `False`. Lean's type checker directly verifies the contravariant refuter lifting and its connection to the Branch-B closure theorem.

### 4. No propagation of `noncomputable`

0091 internally uses `signedFiveAdicPowerSplit_of_normalForm`, a `noncomputable def` arising from classical choice. This theorem only derives proof-only `False`, so the theorem itself does not need a `noncomputable` modifier.

## Redundancy and duplication

Judged only by code size, this theorem merely gives a name to the composition of 0091 and 0058 and could be inlined.

In principle, one could expand 0091 directly at the call site of `branchB_false_of_signedBranchARefuter`. Doing so, however, would erase the named proof-graph edge

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\text{Branch-B contradiction}.
$$

Because this theorem is the module-ending closure API, it is better viewed as an intentional layer-boundary adapter than as accidental duplication.

## Optimization candidates

### Candidate A — keep the current named closure theorem

This best preserves domain terminology. Downstream modules need no knowledge of Branch-B routing internals.

### Candidate B — inline 0091

A form such as

```lean
exact branchB_false_of_signedBranchARefuter
  (fun u v w hNF => hCore (signedFiveAdicPowerSplit_of_normalForm hNF))
  hPack hBranch
```

may be possible, but it makes the proof graph less explicit.

### Candidate C — introduce a generic closure combinator

Abstractly this is the pattern

$$
(A\to B)\to(B\to\bot)\to(A\to\bot).
$$

A generic refuter-lifting helper could encode it, but at the cost of hiding FLT5-specific layer names.

### Candidate D — make the module-level façade explicit

The theorem could be treated as the export point of `SignedFiveAdicPowerSplit.lean`, while internal construction helpers are given narrower visibility. This is a module-architecture optimization rather than a mathematical one.

## Required Mathlib imports and import optimization

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses `import Mathlib`.

This theorem itself only composes project-local declarations with `exact`; it invokes no individual Mathlib arithmetic theorem or tactic directly. From the theorem-local viewpoint, the umbrella `Mathlib` import is therefore much larger than necessary.

However, earlier parts of the actual `SignedFiveAdicPowerSplit.lean` module use natural-number divisibility, coprimality, primality, powers, division, and tactics such as `ring`, `omega`, and `norm_num`. The minimal import set for the whole module is consequently determined by those earlier declarations.

In this reading, the standalone artifact was available, but the independent import header of the split source file could not be fetched directly from the repository. No Lean build was run, as requested. Therefore the exact minimal Mathlib module list is not asserted by guesswork.

A safe import-optimization pass would inspect the original module's direct imports and tactic usage separately, then verify a narrowed import set with a dedicated build in a different task.

## Comparator challenge suitability

Suitable, but primarily as a proof-architecture challenge rather than a number-theory challenge.

Natural variants include:

1. the current named composition of 0091 and 0058;
2. inlining 0091;
3. using a generic refuter-lifting helper;
4. merging the Branch-B closure and power-split closure into one theorem;
5. retaining this theorem as a module façade while narrowing helper visibility.

Evaluation criteria should include code length, domain terminology, visibility of dependency direction, locality of type errors, reuse, and auditability of the proof graph.

The current implementation is one line, yet it explicitly records the module-ending edge `SignedFiveAdicPowerSplitCore → Branch-B contradiction`, which gives it substantial architectural value.

## PDF and source basis

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The source confirms that this is the last theorem in `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`, immediately before that module ends.

Existing Japanese and English PDFs are treated as narrative background. In this run GitHub code search again returned an upstream 502 error, so no exact PDF page or section corresponding one-to-one with this closure theorem could be established. No PDF-specific theorem number, page number, or wording is therefore guessed.

The presumed split-source path `Flt5DkMath/DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` also returned 404 on the target branch; the primary material actually verified here is the generated standalone artifact. This distinction between confirmed evidence and inference is intentional.

## Next declaration to read

The next module in source order is `DkMath/FLT/Five/SquareGoldenBridge.lean`, whose first declaration is

```lean
def GoldenNorm (m n : ℤ) : ℤ :=
  m ^ 2 + m * n - n ^ 2
```

This is the entry point to the next layer, where the fifth cyclotomic factor is rewritten as the golden-ratio quadratic form. The following declarations `GN5_eq_square_cross_form`, `square_cross_coordinate_change`, and `GN5_eq_goldenNorm_squareLink` establish the bridge expressing `GN5` through

$$
\mathrm{GoldenNorm}(m,n)=m^2+mn-n^2.
$$

Thus 0092 closes the exact five-adic power-split module, and 0093 begins the square/golden-norm bridge chapter.
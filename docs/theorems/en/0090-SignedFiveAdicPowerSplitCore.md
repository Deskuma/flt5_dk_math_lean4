# 0090 — `SignedFiveAdicPowerSplitCore`

## Lean type

```lean
abbrev SignedFiveAdicPowerSplitCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False
```

This declaration is not a theorem but a proposition alias introduced with `abbrev`. In one line it defines the type of a contradiction receiver: for arbitrary `u v w : ℕ`, if it is given the corresponding exact power-split packet

```lean
SignedFiveAdicPowerSplit u v w
```

it must return `False`.

## Mathematical statement

Mathematically, this is the specification of a refuter asserting that no exact five-adic power split defined in 0083 can exist.

In other words, it expresses

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\Longrightarrow\bot.
$$

A value `SignedFiveAdicPowerSplit u v w` contains positive coprime natural numbers $a,b$ attached to a five-adic packet together with the exact fifth-power split data

$$
carrier=5^4a^5,
$$

$$
residual=5b^5,
$$

$$
distinguished=5ab,
$$

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1.
$$

Thus this core is the receiving interface through which later arithmetic or algebraic arguments are expected to send any data satisfying all of these exact split conditions to contradiction.

The important point is that this declaration itself does not prove the contradiction. It only fixes the type of the function that later work must implement: a function sending every exact split to `False`.

## Role in the overall proof

By 0087–0089, the construction path from a signed normal form to an exact power split has been completed.

Conceptually,

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$

The present declaration defines the API boundary on the consuming side: it receives the constructed exact split and is required to produce a contradiction.

The immediately following theorem

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

constructs a split using 0089 `signedFiveAdicPowerSplit_of_normalForm` and simply passes it to `hCore`, thereby obtaining a refuter for all signed Branch-A normal forms.

The next theorem, `branchB_false_of_powerSplitCore`, then closes every routed Branch-B candidate through the existing `branchB_false_of_signedBranchARefuter` adapter.

Therefore this declaration is the proof-architecture boundary separating the first half, which constructs the five-adic power decomposition, from the second half, which must contradict that decomposition using the later golden-ratio / quadratic-form machinery or related arithmetic.

## Direct dependencies

There is only one direct dependency.

- `SignedFiveAdicPowerSplit` (0083)

The type body of this declaration does not directly mention `SignedFiveAdicPacket`, `SignedBranchANormalForm`, `GN5`, `SumGN5`, `padicValNat`, modulo $25$, or gcd lemmas. Those ingredients have already been encapsulated in the 0083 record and its construction path.

Indirectly, through 0087–0089, this layer is connected to the five-adic packet construction, exact gcd information, and the fifth-power factor split, but the core interface itself requires only the exact split.

## Proof flow

This declaration has no proof script. Because it is an `abbrev` defining a type, the required behavior has only three stages.

1. Receive arbitrary implicit indices `{u v w : ℕ}`.
2. Receive a value `SignedFiveAdicPowerSplit u v w`.
3. Return `False`.

In other words, it fixes in advance the function type that the later contradiction argument must satisfy.

With this interface in place, downstream theorems do not need to know the internal contradiction proof and can simply apply

```lean
hCore split
```

to obtain `False`.

## Lean-specific processing

### Reducibility of `abbrev`

`abbrev` introduces a reducible alias. Lean may unfold

```lean
SignedFiveAdicPowerSplitCore
```

as needed to

```lean
∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False.
```

This makes it possible to use a value of the core directly as a function, for example `hCore split`, without extra adapters merely to expose the underlying function type.

### Implicit parameters

The indices `{u v w : ℕ}` are implicit. Lean can normally infer them from the type of

```lean
split : SignedFiveAdicPowerSplit u v w.
```

Accordingly, the immediately following theorem can write

```lean
hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

without explicitly supplying `u v w`.

### `Prop` and a proof-only API

This core does not produce computational data; its output is always `False`. It is therefore a proof-only contract living in `Prop`.

Declarations 0088–0089 are `noncomputable` because they use or propagate `Classical.choice`, but this core itself performs no choice and therefore is not declared `noncomputable`.

## Redundancy and duplication

Locally, the code is only one line and contains essentially no redundancy.

Structurally, however, it closely mirrors 0078 `SignedFiveAdicCore`.

Declaration 0078 is

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

whereas the present declaration simply strengthens the domain from

```lean
SignedFiveAdicPacket
```

to

```lean
SignedFiveAdicPowerSplit.
```

This is duplication, but it is meaningful duplication: it records by name the proof layer at which contradiction is assumed. One route may contradict the five-adic packet directly, while another may proceed to the exact fifth-power split and contradict the stronger structure there. Separate core contracts make those routes visible in the proof graph.

## Optimization candidates

### Candidate A — Keep the current domain-specific core

This is the clearest option. The name `SignedFiveAdicPowerSplitCore` immediately says that the remaining arithmetic core is formulated at the exact split layer.

### Candidate B — Introduce a generic refuter alias

One could define something like

```lean
abbrev Refuter (α : Sort _) : Prop := α → False
```

and reuse it. However, generalizing all the way to an indexed family such as

```lean
∀ {u v w}, SignedFiveAdicPowerSplit u v w → False
```

adds abstraction machinery and may make the FLT5 proof graph harder rather than easier to read.

### Candidate C — Share infrastructure with 0078

`SignedFiveAdicCore` and `SignedFiveAdicPowerSplitCore` have the same receiver pattern, so a shared constructor or adapter framework is possible.

On the other hand, they expose different amounts of mathematical information. The packet core has only the five-adic packet, while the power-split core has the exact fifth-power decomposition available. Retaining the domain-specific names may therefore be better for architectural readability.

### Candidate D — Accept a thinner contradiction kernel

If later golden-ratio / quadratic-form arguments turn out to use only a subset of the fields of `SignedFiveAdicPowerSplit`, the core could potentially accept a thinner record containing exactly those fields.

This is an optimization candidate to evaluate only after reading the downstream theorems; at this stage it remains a hypothesis rather than a confirmed improvement.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact on the target branch is built with `import Mathlib`.

This declaration itself does not directly use Mathlib arithmetic theorems or tactics. Lean's basic logic plus the project-local type `SignedFiveAdicPowerSplit` is enough to state it, so the umbrella `Mathlib` import is not required for this one line in isolation.

The manifest places this region in `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`. At module scope, however, the preceding construction uses gcd, coprimality, primes, natural-number division, powers, `ring`, `omega`, and `norm_num`, so the true minimal import set must be determined for the module as a whole.

A reasonable import optimization path is to inventory the theorems and tactics used by the split module and replace umbrella `Mathlib` incrementally with narrower imports. Because this task does not run a Lean build, no exact minimal import set is asserted here.

## Comparator challenge suitability

This declaration is suitable for a Comparator challenge, but mainly as a proof-architecture / API-design challenge rather than a numerical-theorem challenge.

Useful alternatives to compare are:

1. The current domain-specific `SignedFiveAdicPowerSplitCore`.
2. Repeating the raw function type directly in theorem arguments.
3. Introducing a generic `Refuter` or indexed-refuter abstraction.
4. Sharing a common framework with 0078 `SignedFiveAdicCore`.
5. Passing a minimal contradiction kernel instead of the full `SignedFiveAdicPowerSplit` record.

Evaluation criteria include proof-graph visibility, downstream theorem brevity, locality of type errors, dependency boundaries, and abstraction cost.

The current design tolerates a small amount of duplicated interface code in exchange for keeping the mathematical layer boundary visible in the declaration name. The central Comparator question is therefore genericity versus domain readability.

## PDF and source basis

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. In that source this declaration belongs to the generated `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` section and appears immediately after 0089 `signedFiveAdicPowerSplit_of_normalForm` and immediately before `signedBranchARefuter_of_powerSplitCore`.

The existing Japanese and English PDFs are treated as narrative background. During this run GitHub code search returned an upstream 502 error, so a specific PDF page or section corresponding one-to-one with this one-line `abbrev` could not be confirmed. No PDF theorem number, page number, or wording has therefore been guessed.

## Next theorem to read

The theorem immediately following in the source is

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

The present article fixes the type of the exact power-split contradiction receiver. The next article will combine that core with the normal-form-to-split adapter from 0089 and lift it to `SignedBranchARefuter`.

Thus the next step is the closure adapter

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}.
$$

At that point, contradiction at the exact split layer propagates to all signed Branch-A normal forms.
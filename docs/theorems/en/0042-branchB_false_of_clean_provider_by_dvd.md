# 0042 — `branchB_false_of_clean_provider_by_dvd`

## 1. Declaration

```lean
theorem branchB_false_of_clean_provider_by_dvd
    (hProvider : BranchBCleanGN5ChannelProvider)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases hProvider hPack hBranch with ⟨q, hClean⟩
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

This theorem belongs to the `DkMath.FLT.Five` namespace and is located in `Provider.lean`.

## 2. Lean type

There are three inputs.

- `hProvider : BranchBCleanGN5ChannelProvider`
- `hPack : CounterexamplePack x y z`
- `hBranch : ¬ 5 ∣ z - y`

The output is `False`. Therefore, this theorem is a conditional Branch B refuter under the assumption of a clean-channel provider.

The variables `x`, `y`, and `z` are implicit arguments inferred from the types of `hPack` and `hBranch`.

## 3. Mathematical statement

`CounterexamplePack x y z` represents a positive primitive candidate for the Fermat fifth-power equation

$$
x^5+y^5=z^5.
$$

The Branch B condition says that for the gap $g=z-y$,

$$
5\nmid g.
$$

The provider supplies a natural number $q$ and a clean channel

$$
CleanGN5Channel(g,y,q)
$$

from this candidate and the Branch B condition. Conceptually, the clean channel records that $q$ is prime and that

$$
q\mid GN5(g,y),\qquad q\nmid g,
$$

while

$$
q^2\nmid GN5(g,y).
$$

On the other hand, the Fermat equation forces the full body to be a perfect fifth power:

$$
Body5(g,y)=g\,GN5(g,y)=x^5.
$$

The clean channel excludes the possibility that this full body is a perfect fifth power, yielding a contradiction.

## 4. Role in the complete proof

This theorem is the consumer connecting the provider API to the local divisibility refuter.

```text
BranchBCleanGN5ChannelProvider
              ↓ existential witness q
CleanGN5Channel (z - y) y q
              ↓
counterexample_false_of_clean_GN5Channel_by_dvd
              ↓
False
```

No new number-theoretic fact is proved here. The prime-supply problem is delegated to `hProvider`, and the result is connected to the already completed local contradiction.

This separation allows the construction of the provider to change without modifying the local refuter. Conversely, the local valuation argument may be improved while preserving the provider interface.

## 5. Direct dependencies

### `BranchBCleanGN5ChannelProvider`

A bundled provider interface returning the existence of a clean channel for every Branch B counterexample candidate.

### `CounterexamplePack`

The structure collecting positivity, primitiveness, and the Fermat fifth-power equation.

### `CleanGN5Channel`

The structure bundling a prime channel whose local valuation is exactly one.

### `counterexample_false_of_clean_GN5Channel_by_dvd`

The local refuter documented in article 0038. Given one concrete clean channel, it contradicts the perfect-fifth-power body forced by the Fermat equation with the square-divisibility obstruction and returns `False`.

## 6. Proof flow

### 6.1 Apply the provider

```lean
hProvider hPack hBranch
```

produces the existential statement

```lean
∃ q : ℕ, CleanGN5Channel (z - y) y q
```

### 6.2 Eliminate the existential witness

```lean
rcases hProvider hPack hBranch with ⟨q, hClean⟩
```

introduces the prime candidate `q` and its clean-channel proof `hClean` into the local context.

### 6.3 Apply the local refuter

```lean
exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

closes the proof. The hypothesis `hBranch` is not passed directly to the local refuter because it has already been consumed by the provider when producing the clean channel.

## 7. Lean-specific processing

### Implicit argument inference

In `counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean`, Lean infers `x`, `y`, `z`, and `q` from the argument types.

### Transparent unfolding of `abbrev`

`BranchBCleanGN5ChannelProvider` is an abbreviation for a proposition. Lean unfolds it transparently during function application, so `unfold BranchBCleanGN5ChannelProvider at hProvider` is unnecessary.

### Existential elimination with `rcases`

`rcases ... with ⟨q, hClean⟩` extracts the witness and proof from `Exists`. The internal fields of `CleanGN5Channel` are deliberately not decomposed; the bundled object is passed intact to the next theorem.

### Direct construction of `False`

Because the goal is `False`, the `False` returned by the local refuter can be used directly with `exact`.

## 8. Redundancy and duplication

The proof is only two lines long and contains almost no logical redundancy.

The following style is equivalent:

```lean
  obtain ⟨q, hClean⟩ := hProvider hPack hBranch
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

This is merely a stylistic variation rather than a real simplification.

Although `q` is not explicitly named in the second line, it occurs in the type of `hClean`, so the existential witness must remain available. Anonymous pattern variants provide little practical benefit.

## 9. Optimization candidates

The current proof is already essentially minimal. Preserving the readability of the API boundary is more valuable than further compression.

A more compact term proof is possible, but it would obscure the existential-elimination step. The current form clearly exhibits the three roles: provider, witness, and consumer.

If the local refuter is later reorganized as a method-like API on the clean channel itself, the overall structure of this theorem will remain unchanged.

## 10. Required Mathlib imports and import optimization

The generated standalone source uses `import Mathlib`, but this theorem itself directly requires only:

- natural numbers `ℕ`
- divisibility notation `∣`
- the existential type `Exists`
- the `rcases` tactic
- preceding FLT5 definitions and theorems

At the actual module boundary, `Provider.lean` should only need the preceding FLT5 module exposing the provider interfaces and `counterexample_false_of_clean_GN5Channel_by_dvd`, corresponding at least to `BranchB.lean`.

However, the exact minimal set of individual Mathlib imports was not verified with a Lean build while preparing this article. The following are therefore optimization proposals rather than confirmed changes:

- avoid the umbrella `Mathlib` import;
- avoid excessive dependence on accidental transitive imports inside FLT5;
- audit whether the tactic import providing `rcases` is already exported by the parent module, using `lake env lean` and import linting.

## 11. Comparator challenge suitability

This theorem is suitable for a Comparator challenge, although it is an API-wiring challenge rather than a mathematical-discovery challenge.

### Example challenge

Assume:

```lean
hProvider : BranchBCleanGN5ChannelProvider
hPack : CounterexamplePack x y z
hBranch : ¬ 5 ∣ z - y
```

The goal is to prove `False` under the following constraints:

- do not manually unfold `BranchBCleanGN5ChannelProvider`;
- do not decompose the fields of `CleanGN5Channel`;
- do not reprove `counterexample_false_of_clean_GN5Channel_by_dvd`.

This compares how directly a solution connects an existential provider to a bundled consumer.

Evaluation criteria include:

- correct elimination of the witness;
- preservation of the bundled abstraction;
- avoidance of unnecessary `unfold` operations or field decomposition;
- clarity of dependencies.

## 12. Evidence and audit qualifications

The declaration name, type, proof body, source comment, and following declaration were checked in the repository's generated `Flt5DkMath/FLT5StandAlone.lean` source.

The Japanese and English PDFs provide narrative context for the complete proof, but the formal statements in this article follow the Lean source as the primary authority.

The import-minimization discussion is an unbuilt proposal and is not presented as a verified fact.

## 13. Next theorem to read

The next theorem is

```lean
DkMath.FLT.Five.branchB_false_of_noLiftEscape_by_dvd
```

It converts `BranchBNoLiftEscape` into a bundled provider through the adapter documented in article 0041 and passes that provider to the consumer of the present article. It therefore closes the path from the unbundled no-lift kernel to the Branch B contradiction in a single composition theorem.

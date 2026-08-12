# 0039 — `BranchBCleanGN5ChannelProvider`

## 1. Declaration

```lean
/-- A Branch-B counterexample receives at least one existential clean GN5 channel. -/
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

## 2. Lean type

`BranchBCleanGN5ChannelProvider` is not a value-producing computational function. It is an abbreviation for a proposition of type `Prop`.

For implicit natural numbers `x y z`, it receives:

- `CounterexamplePack x y z`,
- the Branch B condition `¬ 5 ∣ z - y`,

and returns a natural number `q` together with a proof that `q` satisfies `CleanGN5Channel (z-y) y q`.

Because this is an `abbrev`, Lean unfolds it transparently at use sites.

## 3. Mathematical statement

Suppose a positive primitive Fermat counterexample candidate satisfies

$$
x^5+y^5=z^5
$$

and belongs to Branch B, meaning

$$
5\nmid z-y.
$$

Then the provider contract asserts the existence of at least one prime `q` such that

$$
q\mid GN5(z-y,y),
$$

$$
q\nmid z-y,
$$

and

$$
q^2\nmid GN5(z-y,y).
$$

These four conditions, including primality, are bundled in the `CleanGN5Channel` structure.

The declaration itself does not prove that such a `q` always exists. It names the hypothesis interface through which an existence proof can be passed to later consumers.

## 4. Role in the complete proof

The previous theorem, `counterexample_false_of_clean_GN5Channel_by_dvd`, sends a Branch B counterexample candidate to `False` as soon as one concrete clean channel is supplied. The responsibility for finding `q` remained open there.

This declaration isolates that responsibility as a provider API.

- The provider side constructs `q` and the clean-channel proof.
- The refuter side consumes that proof and derives the contradiction with the perfect-fifth-power body.

This separation makes prime discovery and no-lift verification independently auditable from the local contradiction.

The source comment states that this provider remains a useful conditional public interface, while the final unconditional FLT5 route does not assume a global provider and instead proceeds through signed five-adic normalization and golden descent.

## 5. Direct dependencies

### 5.1 `CounterexamplePack`

This input package stores positivity, `Nat.Coprime x y`, and the Fermat equation. The present declaration does not project its fields; it uses the structure directly as the provider input type.

### 5.2 `CleanGN5Channel`

```lean
CleanGN5Channel (z - y) y q
```

bundles:

- `Nat.Prime q`,
- `q ∣ GN5 (z-y) y`,
- `¬ q ∣ z-y`,
- `¬ q^2 ∣ GN5 (z-y) y`.

### 5.3 Natural subtraction and Branch B

The term `z-y` is truncated subtraction on `ℕ`. However, the provider receives a `CounterexamplePack`, from which earlier lemmas derive `y<z`. The declaration therefore does not add a separate order argument; an implementation may recover the required order fact from `hPack`.

## 6. Proof flow

This declaration is an `abbrev`, so it has no proof body. Its logical use proceeds as follows.

1. Take arbitrary `x y z`.
2. Receive `hPack : CounterexamplePack x y z`.
3. Receive `hBranch : ¬ 5 ∣ z-y`.
4. Choose a clean-channel witness `q`.
5. Construct the four fields of `CleanGN5Channel (z-y) y q`.
6. Return the witness and proof as `⟨q, hClean⟩`.

A later adapter eliminates this existential with `rcases` and passes the resulting channel to the local refuter.

## 7. Lean-specific processing

### 7.1 Transparency of `abbrev`

An `abbrev` is unfolded more eagerly than an ordinary `def`. Thus a hypothesis

```lean
hProvider : BranchBCleanGN5ChannelProvider
```

can normally be applied directly as

```lean
hProvider hPack hBranch
```

without `unfold BranchBCleanGN5ChannelProvider`.

### 7.2 Implicit universal quantification

The variables `{x y z : ℕ}` are implicit. Lean infers them from the type of `hPack`, so consumers usually write only `hProvider hPack hBranch`.

### 7.3 Curried implication

The type

```lean
CounterexamplePack x y z → ¬ 5 ∣ z-y → ∃ q, ...
```

is a curried function type. The provider first receives the package, then the Branch B proof, and finally returns an existential proof.

### 7.4 Existential witness plus structure

The result `∃ q, CleanGN5Channel ... q` has two layers: an outer existential witness and an inner four-field proposition structure.

## 8. Redundancy and duplication

After unfolding, `BranchBCleanGN5ChannelProvider` is only one universally quantified proposition and adds no logical content. Its value is the named boundary it fixes:

- the input is an arbitrary Branch B `CounterexamplePack`,
- the output is the existence of a concrete prime channel,
- provider implementation and consumer implementation remain separate.

One could return the four conditions as a raw conjunction, but reusing `CleanGN5Channel` avoids duplication and allows existing downstream lemmas to apply directly.

## 9. Optimization candidates

### 9.1 Replace `abbrev` with `def` or `class`

A `def` would create a stronger API boundary but require more explicit unfolding. A `class` would permit typeclass search, but that would hide a mathematically substantial assumption in implicit instance resolution. The current explicit `abbrev` is easier to audit.

### 9.2 Bundle the Branch B input

`CounterexamplePack` and `¬ 5 ∣ z-y` could be bundled into one Branch B structure. That would reduce one argument but would add another structure for a very small adapter layer.

### 9.3 Use a prime subtype as the witness

The witness could be a subtype carrying primality instead of `q : ℕ` with `Nat.Prime q` inside the structure. Existing divisibility APIs are centered on natural numbers, however, so this may introduce additional coercions.

These are design proposals only. No Lean build was run during preparation of this article.

## 10. Required Mathlib imports and import optimization

The generated standalone source uses `import Mathlib` for the complete file. The declaration itself directly needs only natural numbers, divisibility, existential quantification, and proposition structures.

Within the project, the imported environment must expose at least:

- `CounterexamplePack`,
- `CleanGN5Channel`.

Therefore the individual `Provider.lean` module may only need a project import such as `DkMath.FLT.Five.BranchB`, or `DkMath.FLT.Five.CleanChannel` together with `DkMath.FLT.Five.Basic`. This is an inference, not a verified minimal import set, because the standalone artifact does not preserve the original per-module import lines. A module-level `lake env lean` audit would be required to confirm import minimization; no Lean build is performed in this museum update.

## 11. Comparator challenge suitability

This declaration is suitable for an API-design and logical-type-reading challenge rather than a proof-search challenge.

### Challenge A — reconstruct the provider type

Give only the prose specification and ask for the same proposition using `CounterexamplePack` and `CleanGN5Channel`. Evaluation points include implicit variables, placement of the Branch B condition, and existential witness order.

### Challenge B — bundled versus unbundled output

Compare the version returning `CleanGN5Channel` with one returning a raw conjunction of four conditions. Ask about reuse, projections, and direct application of downstream lemmas.

### Challenge C — `abbrev` versus `def` versus `class`

Compare transparency, assumption visibility, and the risk of hiding the provider behind typeclass search.

## 12. Confirmed facts and explicit inferences

Confirmed:

- declaration name, type, and `abbrev` body,
- its placement at the beginning of `Provider.lean`,
- its intended role as a conditional clean-channel interface,
- the source comment that the unconditional final route uses signed five-adic normalization and golden descent,
- the next declaration is `BranchBNoLiftEscape`.

Inferences and audit candidates:

- the exact import lines and minimal import set of the individual `Provider.lean` module,
- maintenance consequences of replacing the abbreviation with a definition or Branch B structure,
- practical value of a prime-subtype witness.

## 13. Next declaration

The next declaration is

```lean
DkMath.FLT.Five.BranchBNoLiftEscape
```

It returns the same local data as an explicit conjunction of primality and three divisibility conditions rather than as a `CleanGN5Channel` structure. Thus `BranchBCleanGN5ChannelProvider` is the bundled provider interface, while `BranchBNoLiftEscape` is its unbundled kernel. After that, `branchBCleanGN5ChannelProvider_of_noLiftEscape` repackages the conjunction into the structure.
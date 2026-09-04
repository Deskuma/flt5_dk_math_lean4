# 0107 — `branchB_false_of_squareGoldenCore`

## Lean type

```lean
/-- A contradiction for every square-golden packet closes Branch B. -/
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

## Mathematical statement

This theorem states that if a counterexample candidate `CounterexamplePack x y z` satisfies the Branch-B condition

$$
5\nmid(z-y),
$$

and if a core

$$
\operatorname{BranchBSquareGoldenCore}
$$

is available that sends every `BranchBSquareGoldenNormalForm` packet to contradiction, then `False` follows.

By 0105, a Branch-B counterexample candidate yields natural numbers $a,b$ such that

$$
\operatorname{BranchBSquareGoldenNormalForm}(x,y,z,a,b).
$$

By contrast, 0106 is a function-shaped proposition that rejects every such packet. Mathematically, this is therefore the final connection

$$
\bigl(\exists a,b,\ P(a,b)\bigr)
\land
\bigl(\forall a,b,\ P(a,b)\to\bot\bigr)
\Longrightarrow \bot.
$$

## Role in the overall proof

This is the terminal theorem of the `SquareGoldenNormalForm.lean` section. It is an **adapter theorem** that converts the square/golden reduction back into the Branch-B contradiction.

Upstream, 0105 `exists_branchB_squareGoldenNormalForm` constructs witnesses $a,b$ and a normal-form packet from Branch-B. 0106 `BranchBSquareGoldenCore` defines an abstract interface that returns contradiction from such a packet. The present theorem only connects those two components.

The proof architecture is

$$
\text{CounterexamplePack}
+\text{Branch-B}
\longrightarrow
\exists a,b,\ \text{SquareGoldenNormalForm}
\longrightarrow
\text{SquareGoldenCore}
\longrightarrow
\bot.
$$

The important point is that this theorem does not reprove any formula involving `GoldenNorm`, the square discriminant, $a^{10}$, or discriminant $5$. Those facts were already packaged before 0105 and are completely hidden behind the abstraction barrier here.

## Direct dependencies

The direct dependencies are:

1. `CounterexamplePack x y z`
2. 0105 `exists_branchB_squareGoldenNormalForm`
3. 0106 `BranchBSquareGoldenCore`

The only project-local theorem explicitly invoked in the proof body is 0105. 0106 is used as the type of the hypothesis `hCore`.

Indirectly, through 0105, this theorem receives the whole square/golden bridge involving `BranchBFifthPowerNormalForm`, `SquareGoldenM`, `SquareGoldenN`, `GoldenNorm`, `squareGolden_tenth_boundary_base`, `squareGolden_square_discriminant`, `goldenNorm_eq_fifth_power_of_GN5`, and `four_mul_goldenNorm_eq_discriminant_five`.

## Proof flow

The proof has only two stages.

### 1. Extract witnesses for the normal-form packet

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

From 0105 we obtain

```lean
∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

and `rcases` decomposes it into the witnesses $a,b$ and the proof `hNF`.

### 2. Apply the universal refuter

```lean
exact hCore hNF
```

The underlying type of `hCore` is

```lean
∀ {x y z a b : ℕ},
  BranchBSquareGoldenNormalForm x y z a b → False
```

so passing `hNF` immediately yields `False`. The parameters $x,y,z,a,b$ are inferred from the type of `hNF` as implicit arguments.

## Lean-specific processing

### 1. `rcases ... with ⟨a, b, hNF⟩`

The existential witnesses are unpacked into three components at once. The witnesses themselves are not used in any downstream arithmetic; only the packet proof `hNF` is passed to the core.

Thus $a,b$ are logically needed for unpacking, even though the consumer side does not refer to them explicitly afterward.

### 2. Implicit arguments make `exact hCore hNF` possible

Because `BranchBSquareGoldenCore` binds $x,y,z,a,b$ implicitly, the proof can simply write

```lean
exact hCore hNF
```

instead of

```lean
exact hCore (x := x) (y := y) (z := z) (a := a) (b := b) hNF
```

### 3. Tactic-free algebra boundary

This theorem contains no `ring`, `norm_num`, `omega`, `exact_mod_cast`, or `norm_cast`. All algebraic and coercion complexity has been sealed in upstream theorems.

This is a particularly clear example of an abstraction barrier working well in Lean.

## Redundancy and duplication

### Same bridge pattern as `branchB_false_of_fifthPowerCore`

An earlier theorem uses the same general producer-consumer pattern for the fifth-power normal form:

```lean
rcases exists_... with ⟨..., hNF⟩
exact hCore ...
```

So the proof pattern itself is duplicated. However, having a closure theorem at each reduction layer makes it explicit at which abstraction level Branch-B is closed. This is intentional duplication that improves maintainability.

### The witness names `a`, `b` are unused afterward

Since `a` and `b` are not mentioned after `rcases`, one could instead write

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
```

The current form, however, documents the mathematical meaning of the existential witnesses.

## Optimization candidates

### Candidate A — replace `rcases` with `obtain`

```lean
obtain ⟨a, b, hNF⟩ := exists_branchB_squareGoldenNormalForm hPack hBranch
exact hCore hNF
```

This is semantically identical and mostly a stylistic choice.

### Candidate B — discard witness names

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
exact hCore hNF
```

This is slightly shorter, but it obscures that $a,b$ are the normal-form witnesses.

### Candidate C — define the core as existential nonexistence

If 0106 were defined as

```lean
¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

then this theorem would need to repackage the witnesses into an existential proposition before applying the core. The current function-style core is simpler here because it supports the local application `hCore hNF`.

### Candidate D — generalize the producer-consumer bridge

One could define a generic theorem expressing that from `A → ∃ w, P w` and `∀ w, P w → False`, one obtains `A → False`. But the present proof is already only two lines long, and such generalization would erase the square/golden phase from the theorem name. The specialized theorem therefore has substantial explanatory value.

## Required Mathlib imports and import optimization

This theorem itself only uses existential elimination and function application. It requires no Mathlib tactic.

Its effective dependencies are the project-local declarations providing:

- `CounterexamplePack`
- `BranchBSquareGoldenCore`
- `exists_branchB_squareGoldenNormalForm`

The standalone artifact globally uses `import Mathlib`, but this theorem does not itself justify such a broad import. The entire `SquareGoldenNormalForm.lean` module still contains upstream proofs using `ring`, `simpa`, `exact_mod_cast`, and related machinery, so any module-level import minimization must be checked against those declarations as well.

Because this museum run does not execute a Lean build, an exact minimal import set is recorded only as an optimization candidate, not as a verified fact.

## Comparator challenge suitability

**Highly suitable**, though as a proof-plumbing / API-design challenge rather than an algebra challenge.

Possible variants include:

```lean
-- A: current version
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
exact hCore hNF

-- B: discard witness names
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
exact hCore hNF

-- C: obtain
obtain ⟨a, b, hNF⟩ := exists_branchB_squareGoldenNormalForm hPack hBranch
exact hCore hNF
```

Useful comparison axes are brevity, readability of the proof state, preservation of witness meaning, error messages, and maintainability if the packet changes later.

The current version A is already a strong local optimum: only two lines while still exposing the mathematical meaning of the witnesses.

## Correspondence with existing materials

The formal source of truth is the generated `DkMath/FLT/Five/SquareGoldenNormalForm.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch `docs/flt5-theorem-museum`.

The GitHub connector's code search returned an upstream 502 error during this run, so the exact page or section positions in the existing Japanese and English PDFs could not be established. No PDF page or section number has therefore been guessed.

In the Lean source, this theorem is immediately followed by the end of the generated `SquareGoldenNormalForm.lean` section and the beginning of the next module, `SignedSquareGoldenExceptional.lean`.

## Next declaration to read

The first declaration in the next module `SignedSquareGoldenExceptional.lean` is

```lean
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  ...
```

Therefore, in dependency order, the next article should study `SignedSquareGoldenExceptionalPacket` and examine how the signed five-adic power split is extended into a square/golden exceptional packet.

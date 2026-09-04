# 0034 — `branchB_false_of_fifthPowerCore`

## Declaration

```lean
theorem branchB_false_of_fifthPowerCore
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq
```

## Lean type

The theorem receives an assumption eliminating the remaining arithmetic core of Branch B,

```lean
hCore : BranchBFifthPowerCore
```

together with an arbitrary `CounterexamplePack x y z` and the Branch B condition

```lean
hBranch : ¬ 5 ∣ z - y
```

and returns `False`.

Expanding the abbreviation introduced in the previous article, `BranchBFifthPowerCore` is the following universal refuter.

```lean
∀ {a b y : ℕ},
  0 < a →
  0 < y →
  Nat.Coprime a y →
  ¬ 5 ∣ a →
  GN5 (a ^ 5) y = b ^ 5 →
  False
```

## Mathematical statement

The complete normal form extracted from a Branch B counterexample candidate supplies natural numbers $a,b$ satisfying

$$
a>0,\qquad y>0,\qquad \gcd(a,y)=1,\qquad 5\nmid a,
$$

and

$$
GN5(a^5,y)=b^5.
$$

The hypothesis `hCore` uniformly excludes every such triple $a,b,y$. Therefore no Branch B `CounterexamplePack` can exist.

## Role in the full proof

This theorem is the adapter between the elementary reduction and the deeper arithmetic that follows.

- The provider `exists_branchB_fifthPowerNormalForm` constructs a complete normal-form packet from a counterexample candidate.
- The consumer `BranchBFifthPowerCore` asks only for the five components needed for contradiction.
- This theorem projects those components from the packet and passes them to the core.

Consequently, the later golden-integer and descent arguments do not need to handle the original variables $x,y,z$ or the original fifth-power equation directly. They only need to refute the reduced `GN5` equation.

## Direct dependencies

### `BranchBFifthPowerCore`

The minimal interface for the refuter, presented as a chain of curried implications.

### `CounterexamplePack`

The original candidate packaging positivity, primitivity, and the fifth-power equation. This theorem does not unpack `hPack` itself; it passes the packet to the provider.

### `exists_branchB_fifthPowerNormalForm`

From `hPack` and `hBranch`, it constructs

```lean
∃ a b, BranchBFifthPowerNormalForm x y z a b
```

### Projections of `BranchBFifthPowerNormalForm`

Only the following five fields are consumed.

```lean
hNF.a_pos
hNF.pack.hy
hNF.coprime_a_y
hNF.five_not_dvd_a
hNF.GN_eq
```

## Proof flow

1. Apply `exists_branchB_fifthPowerNormalForm hPack hBranch`.
2. Use `rcases` to extract witnesses `a`, `b`, and the normal form `hNF`.
3. Pass to `hCore`, in order, proofs of $a>0$, $y>0$, `Coprime a y`, $5∤a$, and `GN5 (a^5) y = b^5`.
4. Close the theorem with the `False` returned by the core.

No new number-theoretic reasoning occurs here. The theorem consists entirely of connecting the already constructed provider to the abstract consumer with the correct types.

## Lean-specific processing

### Eliminating two existentials with `rcases`

```lean
rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

removes both existential quantifiers in one step and retains the final structure proof as `hNF`.

### Structure projections

`hNF.pack.hy` retrieves $y>0$ from the original `CounterexamplePack` stored inside the normal form. The other four arguments are direct fields of `hNF`.

### Applying a curried proposition

Because `BranchBFifthPowerCore` is a chain of function types, its five proofs can be supplied by ordinary whitespace-separated application. Lean infers the implicit variables `{a b y}` from the argument types and from `hNF.GN_eq`.

### Transparency of `abbrev`

`BranchBFifthPowerCore` is an `abbrev`, so Lean unfolds it transparently as required. No explicit `unfold BranchBFifthPowerCore at hCore` is needed.

## Redundancy and duplication

The proof body is already close to minimal and contains no duplicated mathematical argument.

One design asymmetry remains: `hNF.pack.hy` is a nested projection, whereas the other four fields are direct projections. If later adapters repeatedly extract the same five components, a helper theorem or small packet could package the operation.

For a single use, however, direct projection is clearer and avoids unnecessary abstraction.

## Optimization candidates

### 1. A pure term proof

The current proof is already short. It could be rewritten with `Exists.elim`, but that would reduce readability. The present `rcases` form is preferable.

### 2. Extracting an adapter from the normal form

An unverified design option is:

```lean
theorem BranchBFifthPowerNormalForm.false_of_core
    (hNF : BranchBFifthPowerNormalForm x y z a b)
    (hCore : BranchBFifthPowerCore) : False :=
  hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq
```

The current theorem would then only eliminate the provider's existentials and invoke `hNF.false_of_core hCore`. At present this shortens only one site, so the extra API may not be justified.

### 3. Making the core consume the entire packet

One could define the core as

```lean
∀ {x y z a b}, BranchBFifthPowerNormalForm x y z a b → False
```

but this would reintroduce unnecessary data such as $x,z$, `x_eq`, `z_eq`, and the extra coprimality fields. The existing minimal boundary is better factored.

## Required Mathlib imports and import optimization

The verified standalone artifact uses `import Mathlib`. The theorem itself directly uses only existential elimination, structure projection, and function application; it calls no Mathlib arithmetic lemma.

At module granularity, the required local declarations come from the preceding Reduction/NormalForm construction. The exact minimal Mathlib import cannot be established from this article alone.

Unverified import-audit candidates are:

- this theorem introduces no additional arithmetic or tactic import beyond what the module already needs;
- a basic environment supporting `rcases`, plus the local modules defining the core and provider, is likely sufficient;
- the actual minimum should be checked in a separate branch or temporary file. No Lean build was run for this museum update.

## Comparator challenge suitability

This is a good beginner-level challenge.

### Challenge

```lean
theorem challenge
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  sorry
```

### Evaluation points

- discovering `exists_branchB_fifthPowerNormalForm`;
- eliminating the two existentials with `rcases`;
- selecting the five required fields in the correct order;
- closing the goal without using irrelevant fields of the normal form.

A Comparator version can reward preservation of the provider/consumer boundary rather than mere textual similarity.

## Verified facts and proposals

The declaration type, proof body, consumed fields, and its position at the end of `NormalForm.lean` were verified in the generated standalone Lean source in the repository.

The import minimization and helper-adapter designs are unverified proposals.

## Next declaration to read

The next declaration in source order is `DkMath.FLT.Five.Body5`.

The present theorem completes the adapter from the Branch B fifth-power normal form to its abstract core. The following `BranchB.lean` module returns to the exact gap-times-cyclotomic body and introduces `Body5 g y := g * GN5 g y` as its first declaration.

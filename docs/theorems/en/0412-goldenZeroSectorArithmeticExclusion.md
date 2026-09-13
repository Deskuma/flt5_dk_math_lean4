# 0412 `goldenZeroSectorArithmeticExclusion`

## Declaration kind

`theorem`

## Lean type

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

This theorem constructs the public zero-sector arithmetic exclusion contract

```lean
GoldenZeroSectorArithmeticExclusion
```

without assumptions.

The preceding declaration 0410 `goldenZeroSectorFactorExclusion` unconditionally rules out factor packets, and 0411 `goldenZeroSectorArithmeticExclusion_of_factorExclusion` lifts that factor-level exclusion to the public arithmetic contract. Declaration 0412 directly composes those two results and removes the last arithmetic assumption that remained in the zero-sector closure interface.

## Mathematical statement

`GoldenZeroSectorArithmeticExclusion` is the proposition excluding simultaneous satisfaction of the primitive, norm, product-identity, and tenth-power-splitting conditions that arise from the zero sector for integer coordinates `r, s` and positive natural numbers `a, b`.

In the canonical source it is defined as follows.

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

Thus the mathematical content of 0412 is that no quadruple `(r,s,a,b)` satisfying this full collection of zero-sector arithmetic constraints can exist.

At the level of proof architecture, 0411 provides

$$
\mathrm{GoldenZeroSectorFactorExclusion}
\Longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion},
$$

while 0410 proves the antecedent unconditionally. Therefore one obtains

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

## Role in the full proof

This declaration is the endpoint of the `SignedGoldenZeroSectorFinal` module.

The zero-sector route has the schematic form

$$
\text{zero-sector arithmetic data}
\longrightarrow
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}
\longrightarrow
\text{descent packet}
\longrightarrow
\bot.
$$

Declaration 0410 uses the downstream strict infinite descent to make the factor-packet receiver unconditional.

Declaration 0411 converts that receiver back into the source-level arithmetic receiver.

Declaration 0412 composes the two and supplies the exact proposition

```lean
GoldenZeroSectorArithmeticExclusion
```

that `SignedGoldenClosure` had previously accepted only as a conditional input.

From this point onward, the final FLT5 closure no longer needs zero-sector arithmetic exclusion as an external hypothesis.

## Direct dependencies

### `GoldenZeroSectorArithmeticExclusion`

An `abbrev : Prop` exported by `SignedGoldenClosure`.

It expresses the receiver contract asserting that all raw zero-sector arithmetic data of the certified form lead to contradiction.

It is exactly the return type of 0412.

### `goldenZeroSectorFactorExclusion`

```lean
theorem goldenZeroSectorFactorExclusion :
    GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

This is declaration 0410.

It applies the already-proved strict infinite-descent theorem

```lean
goldenZeroSectorCandidate_false
```

to the source candidate retained inside each factor packet as `packet.inversion.source`, thereby ruling out every factor packet without assumptions.

### `goldenZeroSectorArithmeticExclusion_of_factorExclusion`

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

This is declaration 0411.

It is the adapter that converts the factorization-layer exclusion receiver into the public arithmetic receiver exposed by the closure layer.

The proof of 0412 consists precisely of applying this theorem to the unconditional result from 0410.

## Proof or construction flow

The proof is a two-level pure term application.

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
```

Lean sees the following types:

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  : GoldenZeroSectorFactorExclusion →
      GoldenZeroSectorArithmeticExclusion
```

and

```lean
goldenZeroSectorFactorExclusion
  : GoldenZeroSectorFactorExclusion
```

so ordinary function application immediately yields

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
  : GoldenZeroSectorArithmeticExclusion
```

No new witnesses, case splits, rewrites, or arithmetic tactics are required.

## Lean-specific processing

### 1. Theorems are proof terms

In Lean, a theorem is a term inhabiting its declared type.

Therefore

```lean
goldenZeroSectorFactorExclusion
```

is not merely a theorem name: it is a proof term of type

```lean
GoldenZeroSectorFactorExclusion
```

and can be passed directly as an argument to another theorem.

Declaration 0412 is consequently a very direct Curry–Howard composition.

### 2. No tactic block is needed

The declaration closes with

```lean
:=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

alone.

No `exact`, `apply`, `simpa`, or `change` is necessary.

The equivalent tactic-style proof

```lean
by
  exact goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

would also work, but the current term-style version displays the dependency structure more clearly.

### 3. `abbrev` transparency has already been absorbed by 0411

Declaration 0412 does not unfold the internal structures of `GoldenZeroSectorFactorExclusion` or `GoldenZeroSectorArithmeticExclusion`.

The definitional compatibility between the factorization-layer contract and the public closure contract has already been handled when Lean type-checks 0411.

As a result, 0412 is fully insulated from the representation details at that module boundary.

## Redundancy and duplication

Viewed only by line count, 0412 is a simple composition of 0410 and 0411 and could be inlined.

For example, downstream code could directly use

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
```

and obtain the same proof term.

However, keeping the declaration separately named has substantial architectural value:

1. the unconditional implementation of `GoldenZeroSectorArithmeticExclusion` receives a stable public name;
2. downstream closure theorems need not know about descent or factorization internals;
3. the boundary between a conditional receiver and an unconditional provider becomes explicit;
4. auditing the proof-dependency graph becomes easier.

Thus this is better understood as API finalization rather than logical duplication.

## Optimization candidates

### 1. Preserve the current term-style proof

The present theorem is already essentially minimal:

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

Further shortening would provide almost no readability benefit.

### 2. Standardize provider naming

If the receiver/provider architecture is made more systematic in the future, the naming pattern between

```lean
...Exclusion_of_factorExclusion
```

and the unconditional provider

```lean
goldenZeroSectorArithmeticExclusion
```

could be mirrored across other closure boundaries.

This would be an API-consistency improvement rather than a proof-performance optimization.

### 3. Do not collapse 0410–0412 into one theorem merely to save lines

Such a merge would be mechanically possible, but it is not attractive architecturally.

Declaration 0410 is the descent result, 0411 is the interface adapter, and 0412 is the unconditional provider. The separation is useful both for theorem-level auditing and for Comparator challenge construction.

## Required Mathlib imports and import-optimization candidates

The standalone canonical source uses

```lean
import Mathlib
```

at the top level.

The proof term of 0412 itself invokes no new tactic or Mathlib theorem directly; it is only an application of previously established declarations.

Therefore 0412 adds essentially no direct import requirements of its own. Its real dependencies are the modules providing

```lean
GoldenZeroSectorArithmeticExclusion
goldenZeroSectorFactorExclusion
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

which come from the closure, factorization, descent, and finalization layers.

The exact minimal replacement for the umbrella `Mathlib` import has not been verified by a Lean build in this documentation pass, so any further import reduction remains unconfirmed.

## Suitability as a Comparator challenge

### Standalone challenge

It is possible, but the difficulty is very low.

If the environment already contains

```lean
goldenZeroSectorFactorExclusion
```

and

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

the solution is a single function application.

That makes 0412 by itself a weak test of Comparator reasoning ability.

### More useful challenge form

A stronger challenge would combine 0410–0412 and expose only the minimum lemmas needed to recover the final contract:

- a factor packet retains its candidate source;
- every candidate contradicts strict infinite descent;
- factor exclusion can be lifted to arithmetic exclusion.

The target would then be

```lean
GoldenZeroSectorArithmeticExclusion
```

and the task would test reconstruction of the proof graph rather than a new arithmetic calculation.

This is particularly suitable as a challenge about composing existing layers in the correct order to close a public contract.

## Next declaration to read

The next declaration is in `Valuation.lean`:

```lean
theorem padicValNat_lower_bound_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5) := by
  ...
```

With 0412 the unconditional zero-sector closure is complete. The development then moves into an independent valuation route. This theorem states that if a prime `q` divides a positive natural number `x`, then the `q`-adic valuation of the fifth power `x^5` is at least five.

Mathematically,

$$
q \mid x
\Longrightarrow
v_q(x) \ge 1
\Longrightarrow
v_q(x^5)=5v_q(x)\ge5.
$$

It supplies the lower valuation bound later used in the clean-channel contradiction.

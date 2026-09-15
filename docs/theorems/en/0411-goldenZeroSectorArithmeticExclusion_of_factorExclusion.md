# 0411 `goldenZeroSectorArithmeticExclusion_of_factorExclusion`

## Declaration kind

`theorem`

## Lean type

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

This theorem constructs the public zero-sector arithmetic exclusion contract

```lean
GoldenZeroSectorArithmeticExclusion
```

from the factorization-level exclusion receiver

```lean
GoldenZeroSectorFactorExclusion
```

The proof body is only a direct application of the existing theorem

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

to `hFactor`.

## Mathematical statement

`GoldenZeroSectorArithmeticExclusion` is the proposition excluding integer coordinates `r, s` and positive natural-number data `a, b` satisfying the primitive arithmetic conditions of the zero sector.

Its central shape is

```lean
∀ (r s : ℤ) (a b : ℕ),
  0 < a →
  0 < b →
  Nat.Coprime a b →
  ¬ 5 ∣ b →
  (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
    goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
  s * goldenFifthSndFactor r s =
    -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
  Nat.Coprime r.natAbs s.natAbs →
  ... →
  False
```

The final hypothesis is the certified tenth-power split. In the repository source, `GoldenZeroSectorFactorArithmeticExclusion` and `GoldenZeroSectorArithmeticExclusion` are deliberately designed to express the same raw arithmetic contract.

Thus mathematically the theorem is the implication

$$
\mathrm{GoldenZeroSectorFactorExclusion}
\Longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

If every certified factor packet is impossible, then the raw zero-sector arithmetic data from which such a packet is constructed are impossible as well.

## Role in the full proof

0410 `goldenZeroSectorFactorExclusion` supplied

```lean
GoldenZeroSectorFactorExclusion
```

unconditionally by using the already established infinite-descent contradiction.

0411 turns that result back into the public interface expected by the FLT5 closure layer:

```lean
GoldenZeroSectorArithmeticExclusion
```

The proof architecture is therefore

$$
\mathrm{GoldenZeroSectorCandidate}
\longrightarrow
\text{strict infinite descent}
\longrightarrow
\mathrm{GoldenZeroSectorFactorExclusion}
\longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

The important point is that 0411 does not perform a new descent or a new factorization.

The factorization module already knows how to build a factor packet from raw arithmetic input, and the generic lifting theorem

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

has already proved that excluding all factor packets excludes all raw arithmetic inputs. 0411 simply republishes that result under the public closure contract.

## Direct dependencies

### `GoldenZeroSectorFactorExclusion`

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

This is the receiver excluding every factor packet.

0411 receives it as the hypothesis `hFactor`.

### `GoldenZeroSectorFactorArithmeticExclusion`

This is the raw arithmetic receiver defined on the factorization side.

It takes `r, s, a, b`, positivity, coprimality, `5 ∤ b`, the golden-norm alternative, the zero-sector product identity, coprimality of the coordinates, and the tenth-power split, and returns `False`.

The contract is placed on the factorization side so that it can be used without reversing the acyclic dependency direction of the module graph.

### `GoldenZeroSectorArithmeticExclusion`

This is the public zero-sector arithmetic receiver exposed by the closure layer.

As stated by the source comments, it expresses the same arithmetic contract as `GoldenZeroSectorFactorArithmeticExclusion`.

Therefore 0411 does not need to construct any additional conversion data.

### `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

```lean
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  ...
```

This theorem contains the substantive lifting argument used by 0411.

It reconstructs a `GoldenZeroSectorCandidate`, an inversion packet, and a factor packet from the raw arithmetic data and then applies `hFactor` to obtain a contradiction.

Hence 0411 is a thin wrapper connecting that generic lifting theorem to the public result type.

## Proof / construction flow

The proof is a single term:

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

The type flow begins with

```lean
hFactor
  : GoldenZeroSectorFactorExclusion
```

and gives

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
  : GoldenZeroSectorFactorArithmeticExclusion
```

In the repository source, the factorization-side arithmetic contract and the public `GoldenZeroSectorArithmeticExclusion` are definitionally the same underlying function type. Lean can therefore use this term directly as the conclusion.

No explicit `change`, `simpa`, `exact`, or `rw` is required.

## Lean-specific processing

### 1. Definitional transparency of `abbrev`

The key reason this theorem can be written in one line is that the receiver propositions are defined with `abbrev`.

Lean may unfold reducible abbreviations when needed and see that the underlying function types of

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

and

```lean
GoldenZeroSectorArithmeticExclusion
```

coincide.

No cast or equality proof is needed.

### 2. Pure term proof

The declaration closes with

```lean
:=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

rather than a tactic block.

This accurately reflects the fact that the declaration is not carrying out a fresh argument; it is reusing an existing theorem result as the public interface.

### 3. Preservation of the dependency boundary

Giving the same arithmetic contract two names is not merely accidental duplication.

The factorization module cannot import the later closure layer without creating an undesirable dependency direction. It therefore owns a local receiver name, while 0411 connects that local receiver to the public name later in the graph.

This is an architectural device for preserving an acyclic Lean module dependency graph.

## Redundancy and duplication

At first sight,

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

and

```lean
GoldenZeroSectorArithmeticExclusion
```

look redundant because they repeat the same type.

However, the repository source explicitly explains that the factorization-side receiver is repeated to preserve the dependency direction. The duplication is therefore intentional interface duplication caused by module layering, not accidental repetition.

There is essentially no redundancy in the proof body of 0411 itself.

## Optimization candidates

### 1. Keep the present one-line proof

The current proof is already close to minimal.

One could write

```lean
by
  exact goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

but the current term-style form is shorter and makes the wrapper nature of the theorem clearer.

### 2. Be cautious about unifying the two receiver aliases

A shared definition could remove textual duplication between the two arithmetic exclusion contracts.

However, the location of that shared definition would affect the import graph and the dependency direction between factorization and closure modules.

Therefore a DRY refactor should not be performed merely to reduce duplicated type text.

### 3. Do not remove the theorem merely because it is definitionally trivial

Since the two contracts coincide definitionally, 0411 is technically a trivial wrapper.

Nevertheless the name

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

makes the intended architectural transition explicit: factor-level exclusion is lifted to the public arithmetic exclusion API.

That makes the theorem valuable as a documented interface boundary.

## Required Mathlib imports

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The proof body of 0411 does not directly call any Mathlib tactic or theorem.

Its direct requirements are FLT5-internal declarations:

- `GoldenZeroSectorFactorExclusion`
- `GoldenZeroSectorFactorArithmeticExclusion`
- `GoldenZeroSectorArithmeticExclusion`
- `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

### Import optimization candidate

For 0411 in isolation, `import Mathlib` is clearly much broader than necessary.

Conceptually, only the module providing the factorization receiver and its lifting theorem, plus the module defining the public arithmetic receiver, should be needed.

No Lean build is being run as part of this documentation task, so the exact minimal import set that compiles has not been verified and is not asserted here.

## Comparator challenge suitability

**Possible, but very low difficulty in isolation.**

It can be used to test whether a model understands that two receiver aliases are definitionally equal.

A reduced challenge could resemble

```lean
abbrev A : Prop := P
abbrev B : Prop := P
axiom lift : H → A
```

with a target

```lean
theorem bridge (h : H) : B := by
  ?_
```

This evaluates whether the solver can

- understand `abbrev` transparency,
- avoid unnecessary `simpa` or `change`,
- recognize the purpose of a wrapper at a module boundary.

For evaluating mathematical reasoning, however, the preceding theorem `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion` is a much stronger Comparator challenge because it contains the actual reconstruction of the factor packet and the contradiction.

## Next declaration to read

Next is 0412:

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

0410 supplies the unconditional

```lean
GoldenZeroSectorFactorExclusion
```

and 0411 supplies the bridge from that receiver to the public arithmetic receiver.

0412 actually composes the two and establishes

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

with no assumptions.

At that point the zero-sector arithmetic exclusion that earlier closure theorems accepted as a hypothesis is fully discharged, preparing the proof for the unconditional FLT5 endpoint.

# 0367 — `goldenUnitFifthClass_neg_one`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
  decide
```

## Lean type

Conceptually, its type is:

```lean
goldenUnitFifthClass_neg_one :
  GoldenUnitFifthClass (-goldenOne)
```

`GoldenUnitFifthClass` is defined in the preceding unit-class layer by

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Thus this theorem proves, with explicit witnesses, that the golden integer `-goldenOne` belongs to one of the five representative sectors.

## Mathematical statement

The witnesses chosen by the theorem are

$$
i=0,
\qquad
\delta=-1.
$$

Hence the statement is simply the identity

$$
-1
=\varphi^0(-1)^5
=1\cdot(-1)
=-1.
$$

Because the exponent 5 is odd, the minus sign need not remain as an independent unit representative: it can be absorbed into the fifth-power witness. Thus `-1` is the smallest concrete example of why the unit classes can be represented using only

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4.
$$

## Role in the whole proof

0356 `goldenUnit_measure_one_cases` classifies golden units of measure 1 into

$$
1,\;-1,\;\varphi,\;-\varphi.
$$

The later theorem `goldenUnitFifthClass_of_unit` uses strong induction on `goldenUnitMeasure` to classify every golden unit modulo fifth powers. To close the measure-one base part, the four possibilities are handled by the separate lemmas

- `goldenUnitFifthClass_one`
- `goldenUnitFifthClass_neg_one`
- `goldenUnitFifthClass_phi`
- `goldenUnitFifthClass_neg_phi`

This theorem closes the `-1` branch. In the Lean source, `goldenUnitFifthClass_of_unit` consumes it directly in the form

```lean
simpa [h] using goldenUnitFifthClass_neg_one
```

So although the theorem itself is tiny, it is one of the base proofs that closes the strong induction driven by the strict unit descent.

## Direct dependencies

The main project declarations directly involved are:

- `GoldenInt` — the type of golden integers.
- `goldenOne` — the explicit golden integer one.
- `goldenPhi` — the golden-ratio unit `φ`.
- `goldenMul` — multiplication of golden integers.
- `goldenPow` — powers of golden integers.
- `GoldenUnitFifthClass` — the five-sector predicate `x = φ^i δ^5` with `i : Fin 5`.

The proof body does not rewrite by another project theorem. It constructs the existential witnesses of `GoldenUnitFifthClass` directly and certifies the remaining closed equality by computation.

The later theorem that directly consumes this result is `goldenUnitFifthClass_of_unit`.

## Proof / construction flow

### 1. Choose sector zero

```lean
refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
```

This supplies both existential witnesses required by `GoldenUnitFifthClass (-goldenOne)`.

The first witness is

```lean
⟨0, by decide⟩ : Fin 5
```

and selects sector `0`. Constructing a value of `Fin 5` also requires a proof of `0 < 5`; because this is a closed numerical proposition, `decide` discharges it.

The second witness is

```lean
-goldenOne : GoldenInt.
```

The remaining goal is therefore conceptually just

$$
-1=\varphi^0(-1)^5.
$$

### 2. Close the concrete equality by computation

```lean
decide
```

closes the remaining equality.

Since `goldenOne`, `goldenPhi`, `goldenMul`, and `goldenPow` are given as concrete computable data, the closed equality can be decided by reduction together with decidable equality.

## Lean-specific processing

### Nested existential witness construction

`GoldenUnitFifthClass` has the form

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

so the constructor notation

```lean
⟨⟨0, by decide⟩, -goldenOne, ?_⟩
```

supplies the sector and fifth-power base at once.

### `Fin 5`

The theorem needs a value of `Fin 5`, not merely the natural number `0`, so the bound proof is part of the constructed value. Here `by decide` fills that proof field.

### Final `decide`

No `ring` or `norm_num` call is needed. The proof exploits decidability of a completely closed proposition. This is an exceptionally small proof made possible by the computational transparency of the project-specific algebraic wrappers.

## Redundancy and duplication

The preceding theorem `goldenUnitFifthClass_one` has the almost identical body

```lean
refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
decide
```

The only difference is whether the fifth-power witness is `goldenOne` or `-goldenOne`.

Likewise, `goldenUnitFifthClass_phi` and `goldenUnitFifthClass_neg_phi` are separate named lemmas for the remaining measure-one base cases.

This duplication can be factored mechanically. However, retaining four named base lemmas makes the base branch of `goldenUnitFifthClass_of_unit` easier to read and audit.

## Optimization candidates

### 1. Unify the `±1` base cases

One could introduce finite sign data and derive the `1` and `-1` cases from a common lemma. However, each current proof is only two lines long, so the abstraction may add more auxiliary machinery than it removes.

### 2. Shorter witness-oriented syntax

Depending on elaboration, there may be room to push more work into a `simpa [GoldenUnitFifthClass]` style proof. Whether this is actually shorter and stable with the present project definitions has not been verified, because no Lean build is performed in this documentation task.

### 3. A unified API for the four base units

A single lemma mapping the four outputs of `goldenUnit_measure_one_cases` directly into `GoldenUnitFifthClass` could localize the four branches of the strong-induction proof. This trades away some of the auditability supplied by individually named lemmas.

## Required Mathlib import and import optimization

The standalone source is confirmed to use

```lean
import Mathlib
```

as its umbrella import.

At the surface level, this theorem itself only needs `Fin 5`, existential constructors, negation, powers, decidable equality, `decide`, and the project declarations defining `GoldenInt` and the unit-class layer. Tactics such as `ring`, `omega`, `nlinarith`, and `fin_cases` do not occur in this proof body.

It is therefore very likely that the import set can be made much narrower than all of `Mathlib`. The exact minimal import set, including all instances required by the `GoldenInt` definitions, has not been verified because this task deliberately performs no Lean build. Accordingly, no exact minimal Mathlib module name is asserted here.

## Suitability as a Comparator challenge

**Yes, especially as a micro challenge.**

A challenge can present only the goal

```lean
GoldenUnitFifthClass (-goldenOne)
```

with the existing definitions, and test whether a model can

1. choose sector `0 : Fin 5`,
2. choose `-goldenOne` as the fifth-power witness,
3. close the remaining concrete equality by computation or elementary algebra.

Its mathematical difficulty is extremely low, so it is not suitable for comparing deep theorem-proving ability. It is, however, a clean small test of existential witness selection, `Fin` bound construction, reducibility of project-specific definitions, and effective use of `decide`.

## Next declaration to read

The next undocumented declaration immediately following it in the Lean source is

```lean
private theorem goldenUnitFifthClass_phi : GoldenUnitFifthClass goldenPhi := by
  refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
  decide
```

Therefore the next document should be **0368 `goldenUnitFifthClass_phi`**. Whereas the present `-1` case absorbs the sign into a fifth power, the `φ` case is the first base example in which the representative sector itself moves from `0` to `1`.
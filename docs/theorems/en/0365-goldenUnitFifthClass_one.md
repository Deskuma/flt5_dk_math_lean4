# 0365 — `goldenUnitFifthClass_one`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem goldenUnitFifthClass_one : GoldenUnitFifthClass goldenOne := by
  refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
  decide
```

It is the base lemma registering the multiplicative identity `goldenOne` in the five-sector classification represented by `GoldenUnitFifthClass`.

## Lean type

```lean
goldenUnitFifthClass_one :
  GoldenUnitFifthClass goldenOne
```

Because the declaration is private, its name is not intended as a public module API. It is an internal proof component used by the later unit-classification argument.

The definition of `GoldenUnitFifthClass` is

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

For `x = goldenOne`, this theorem chooses

```lean
i     = 0
delta = goldenOne
```

as the two witnesses.

## Mathematical statement

Mathematically, the theorem proves the immediate identity

$$
1 = \varphi^0 \cdot 1^5.
$$

Hence `goldenOne` belongs to sector `0` of the five-sector classification modulo fifth powers.

At the exponent level, this can be read as registering the trivial class

$$
0 \in \mathbf Z/5\mathbf Z
$$

as a concrete `Fin 5` witness.

## Role in the overall proof

0359 `goldenUnit_descent` reduces a golden unit of measure greater than `1` to a smaller golden unit. To close that descent by strong induction, the proof still needs to handle the minimal measure `1`.

0356 `goldenUnit_measure_one_cases` classifies a measure-one unit into

$$
\{1,-1,\varphi,-\varphi\}.
$$

The later theorem `goldenUnitFifthClass_of_unit` therefore needs fifth-class membership for each of these four concrete units. The present theorem handles the first case

$$
x=1.
$$

In the canonical source it is used directly in the strong-induction base branch in the form

```lean
simpa [h] using goldenUnitFifthClass_one
```

Thus the lemma is mathematically tiny, but it is a necessary leaf theorem that closes one of the finite base cases of the strict-descent argument.

## Direct dependencies

The main project-level objects directly related to this theorem are:

- `GoldenInt` — the type of golden integers.
- `goldenOne` — the multiplicative identity in the golden-integer structure.
- `goldenPhi` — the golden-ratio unit used as the sector generator.
- `goldenMul` — multiplication appearing in the definition of `GoldenUnitFifthClass`.
- `goldenPow` — exponentiation appearing in the definition of `GoldenUnitFifthClass`.
- `GoldenUnitFifthClass` — the predicate expressing `x = φ^i δ^5` with `i : Fin 5`.

No previously proved project theorem is invoked explicitly in the proof body. The theorem simply constructs existential witnesses and then certifies a closed concrete equality with `decide`.

On the Lean / Mathlib side, the proof mainly uses:

- `refine`
- `Fin 5`
- `decide`
- constructor notation `⟨...⟩` for existential witnesses

## Proof flow

### 1. Provide the sector witness and the fifth-power witness

The line

```lean
refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
```

provides both existential witnesses required by `GoldenUnitFifthClass goldenOne`.

The first witness

```lean
⟨0, by decide⟩ : Fin 5
```

is sector `0`. A value of type `Fin 5` contains both the natural number and a proof that it is smaller than `5`, so the closed arithmetic obligation `0 < 5` is discharged by `decide`.

The second witness is

```lean
goldenOne : GoldenInt
```

and serves as the fifth-power base `delta`.

After these choices, the remaining goal is essentially the concrete equality

$$
1 = \varphi^0 1^5.
$$

### 2. Close the concrete equality computationally

The final line

```lean
decide
```

closes that equality.

No variables or hypotheses remain. Lean can therefore use the decidable equality of the concrete `GoldenInt` values and produce a kernel-checkable proof by computation.

## Lean-specific processing

### `⟨0, by decide⟩ : Fin 5`

In ordinary mathematics one simply writes “exponent `0`.” In Lean, `Fin 5` is a bounded type, so the value must be accompanied by a proof of the bound.

Conceptually the construction is

```lean
⟨0, proof that 0 < 5⟩
```

and `by decide` is a concise way to solve that closed proposition.

### The final `decide`

The proof does not use `simp`, `ring`, or `norm_num`. Once the witnesses have been fully instantiated, the remaining equality is a completely concrete decidable proposition.

This is similar in spirit to 0361 `golden_phi_four_mul_inv_five`, where a fully concrete identity can also be certified by computation.

## Redundancy and repetition

There is essentially no local redundancy inside this theorem. The proof is already only two lines and constructs exactly the required witnesses.

There is, however, structural repetition in the surrounding source: the four measure-one units

$$
1,-1,\varphi,-\varphi
$$

receive separate private membership lemmas.

That repetition has a useful property: each base unit is assigned an explicit sector and an explicit fifth-power witness, making the strong-induction base cases easy to audit.

## Optimization candidates

1. **Keep the current proof** — it is already close to minimal and very readable.
2. **A `simp`-based formulation** — if `GoldenUnitFifthClass`, `goldenOne`, and the power operations have suitable simp lemmas, a proof close to `simp [GoldenUnitFifthClass]` may be possible. This has not been verified because no Lean build is being run.
3. **Combine the four base lemmas** — the memberships of `1,-1,φ,-φ` could be packaged into one finite classification theorem. The current separate lemmas, however, connect very cleanly to later branches of the form `simpa [h] using ...`.
4. **Keep it private** — this theorem is naturally an internal base-case certificate. There is no clear reason, from the current source, to promote it to a public API.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The Mathlib functionality directly visible in this theorem is very small, mainly:

- `Fin`
- `Decidable`
- `decide`
- basic existential construction

However, the definitions of `GoldenInt`, `goldenOne`, `goldenPow`, and `GoldenUnitFifthClass` bring their own dependencies. Therefore the exact minimal import set for the containing module cannot be inferred from these two proof lines alone.

Because Lean builds are explicitly out of scope for this task, the exact minimal import set remains unverified.

## Comparator challenge suitability

**Yes. It is suitable as a very easy micro challenge.**

A challenge could be reduced to

```lean
example : GoldenUnitFifthClass goldenOne := by
  -- fill proof
```

The required ideas are only:

1. choose sector `0 : Fin 5`;
2. choose `goldenOne` as the fifth-power witness.

The remaining equality is concrete computation.

This makes the lemma useful as a small Comparator test for existential-witness construction, bounded `Fin` values, and decidable concrete equality. It is too easy, however, to serve as a serious test of mathematical reasoning.

## Next declaration to read

The next declaration is **0366 `goldenUnitFifthClass_neg_one`**, a **`private theorem`**.

The canonical source continues with

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  ...
```

It registers the second measure-one base unit, `-1`, in the same five-sector representation. The sequence 0365–0368 supplies the four base cases `1,-1,φ,-φ`, which are then consumed by the strong-induction proof of `goldenUnitFifthClass_of_unit`.

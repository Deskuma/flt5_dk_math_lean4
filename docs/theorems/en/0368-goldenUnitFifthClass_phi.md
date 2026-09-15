# 0368 — `goldenUnitFifthClass_phi`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem goldenUnitFifthClass_phi : GoldenUnitFifthClass goldenPhi := by
  refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
  decide
```

## Lean type

Its conceptual type is:

```lean
goldenUnitFifthClass_phi :
  GoldenUnitFifthClass goldenPhi
```

`GoldenUnitFifthClass` is defined by

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

Thus this theorem states, with explicit witnesses, that the golden-ratio unit `goldenPhi` itself belongs to one of the five sectors modulo fifth powers.

## Mathematical statement

The witnesses chosen by the theorem are

$$
i=1,
\qquad
\delta=1.
$$

Hence its mathematical content is the elementary representative identity

$$
\varphi
=\varphi^1 1^5
=\varphi.
$$

Whereas the preceding `goldenUnitFifthClass_one` and `goldenUnitFifthClass_neg_one` concretize sector `0`, this theorem is the first base case whose exponent representative is `1`. In the fivefold classification

$$
\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\},
$$

it fixes `goldenPhi` as the standard representative of sector `1`.

## Role in the full proof

0356 `goldenUnit_measure_one_cases` classifies a golden unit of measure one into the four possibilities

$$
1,\;-1,\;\varphi,\;-\varphi.
$$

The later theorem `goldenUnitFifthClass_of_unit` uses strong induction on `goldenUnitMeasure` to classify every golden unit into `GoldenUnitFifthClass`. Its base part therefore has to place each of those four measure-one units into a fifth-power class.

The present theorem closes the branch `x = goldenPhi`. Once strict descent reaches measure one, it guarantees that the terminal unit `φ` lands in sector `1`.

For measure larger than one, the induction step uses `goldenUnit_descent` to descend to a smaller unit and then transports the class back by `goldenUnitFifthClass_mul_phi` or `goldenUnitFifthClass_mul_phiInv`. This theorem is one of the four concrete endpoints at the bottom of that recursion.

## Direct definitions and lemmas used

The principal project declarations directly relevant here are:

- `GoldenInt` — the type representing golden integers.
- `goldenOne` — the explicit golden integer `1`.
- `goldenPhi` — the golden-ratio unit `φ`.
- `goldenMul` — multiplication on golden integers.
- `goldenPow` — powers of golden integers.
- `GoldenUnitFifthClass` — the five-sector predicate `x = φ^i δ^5` with `i : Fin 5`.

The proof body does not rewrite with or invoke another project theorem through `rw` or `exact`. It directly constructs the existential witnesses required by `GoldenUnitFifthClass` and certifies the remaining closed equality with `decide`.

In the surrounding proof architecture, `goldenUnit_measure_one_cases` supplies the case in which this theorem is needed, while the subsequent `goldenUnitFifthClass_of_unit` consumes this theorem.

## Proof / construction flow

### 1. Choose sector `1`

```lean
refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
```

This provides the two existential witnesses of `GoldenUnitFifthClass goldenPhi` at once.

The first witness is

```lean
⟨1, by decide⟩ : Fin 5
```

and selects sector `1`. Constructing an element of `Fin 5` requires a proof of `1 < 5`; since this is a closed numerical proposition, `decide` proves it directly.

The second witness is

```lean
goldenOne : GoldenInt
```

so the remaining equality is conceptually

$$
\varphi=\varphi^1\cdot1^5.
$$

### 2. Close the concrete equality by computation

```lean
decide
```

closes the remaining proposition.

Because `goldenPhi`, `goldenOne`, `goldenPow`, and `goldenMul` are implemented as explicit computable data and equality of golden integers is decidable, this fully closed equality can be certified by reduction.

## Lean-specific processing

### Constructor notation for nested existentials

`GoldenUnitFifthClass` has the shape

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

so

```lean
⟨⟨1, by decide⟩, goldenOne, ?_⟩
```

supplies `i` and `delta` in a single constructor expression. The final `?_` is the remaining equality-proof hole.

### Finite sectors through `Fin 5`

The witness is not merely the natural number `1`; it is an element of `Fin 5`. This forces the sector exponent to be one of `0,1,2,3,4` at the type level. The inner `by decide` discharges only the subtype bound `1 < 5`.

### The final `decide`

The proof uses neither `ring`, `norm_num`, nor `simp`; it delegates the closed equality to decidability. The proof term is therefore extremely small. Mathematically, however, the content is simply `φ = φ^1 · 1^5`; `decide` only checks its concrete implementation computationally.

## Redundancy and duplication

There is strong syntactic duplication with the neighboring measure-one base lemmas.

`goldenUnitFifthClass_one` chooses sector `0` with witness `goldenOne`; `goldenUnitFifthClass_neg_one` chooses sector `0` with witness `-goldenOne`; this theorem chooses sector `1` with witness `goldenOne`; and the following `goldenUnitFifthClass_neg_phi` chooses sector `1` with witness `-goldenOne`.

Thus the four lemmas are essentially the four entries of the small $2\times2$ table

$$
(\pm1)=\varphi^0(\pm1)^5,
\qquad
(\pm\varphi)=\varphi^1(\pm1)^5.
$$

This duplication could be abstracted, but keeping four named theorems mirrors the four terminal branches of the strong induction and improves readability and auditability of the later proof.

## Optimization candidates

### 1. Derive it from `goldenUnitFifthClass_one`

Since

```lean
goldenUnitFifthClass_mul_phi
```

is already available, one could potentially obtain the class of `goldenOne * goldenPhi` from `GoldenUnitFifthClass goldenOne`, then simplify `goldenOne * goldenPhi = goldenPhi`.

That route, however, introduces more dependencies than the present two-line proof and loses the locality of a concrete base case. The current implementation is therefore preferable in code size and dependency footprint.

### 2. Unify the four measure-one base cases

A helper lemma parameterized by sign and sector `0/1` could remove duplication among the four theorems. But the abstraction data could easily become more complicated than these two-line concrete proofs.

### 3. Replace `decide` by explicit algebraic rewriting

One could try a proof using `golden_pow_eq`, multiplicative-identity lemmas, or `simp` rather than relying on reducibility. That could be useful if a less computation-sensitive proof is desired. Whether it is shorter or more stable under the current project definitions is unverified because no Lean build is performed in this run.

## Required Mathlib imports and import optimization

The standalone source is confirmed to use

```lean
import Mathlib
```

The theorem body itself visibly needs only the facilities supporting `Fin 5`, existential constructors, the project definitions involving multiplication and powers, decidable equality, and `decide`. It does not use tactics such as `ring`, `omega`, `nlinarith`, or `fin_cases` in its body.

Accordingly, an isolated challenge containing this theorem could probably use a much narrower import set than all of `Mathlib`. However, the exact minimal module set must also cover the dependencies of `GoldenInt`, `goldenPow`, `goldenMul`, and their instances. Since this run deliberately performs no Lean build, the exact minimal imports are unverified and no specific minimal module names are asserted.

## Comparator challenge suitability

**Yes. It is well suited as a micro challenge.**

With the challenge goal

```lean
GoldenUnitFifthClass goldenPhi
```

and the relevant definitions supplied, a model can be tested on whether it can

1. choose `1` as the `Fin 5` sector witness,
2. choose `goldenOne` as the fifth-power base,
3. close `φ = φ^1 · 1^5` by computation or elementary algebra.

On its own the mathematics is too easy to measure large search ability. A stronger Comparator task would group 0365, 0367, 0368, and the following `goldenUnitFifthClass_neg_phi` and ask for all four measure-one terminal units to be classified with minimal dependencies. That would test project-specific finite-witness construction and algebraic normalization more meaningfully.

## Next declaration to read

The next unexplained declaration immediately following this theorem in the Lean source is

```lean
private theorem goldenUnitFifthClass_neg_phi :
    GoldenUnitFifthClass (-goldenPhi) := by
  refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
  decide
```

Therefore the next item should be **0369 `goldenUnitFifthClass_neg_phi`**. Whereas the present theorem registers `φ = φ^1 · 1^5` as the positive base element of sector `1`, the next theorem uses

$$
-\varphi=\varphi^1(-1)^5
$$

to absorb the minus sign into the fifth-power witness, completing the four measure-one base cases.
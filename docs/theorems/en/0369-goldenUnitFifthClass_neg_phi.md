# 0369 `goldenUnitFifthClass_neg_phi`

## Declaration kind

`private theorem`

## Lean code

```lean
private theorem goldenUnitFifthClass_neg_phi :
    GoldenUnitFifthClass (-goldenPhi) := by
  refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
  decide
```

## Lean type

```lean
goldenUnitFifthClass_neg_phi : GoldenUnitFifthClass (-goldenPhi)
```

This is a closed proposition with no arguments. It proves that the golden integer `-goldenPhi` belongs to `GoldenUnitFifthClass`.

Because it is a `private theorem`, its name is not intended to be part of the external API of the module. Its local role is to close the measure-one base case inside `goldenUnitFifthClass_of_unit`.

## Mathematical statement

`GoldenUnitFifthClass x` states that there exist `i : Fin 5` and `delta : GoldenInt` such that

$$
x = \varphi^i\delta^5.
$$

For `x=-\varphi`, this theorem uses the explicit witness

$$
-\varphi = \varphi^1(-1)^5.
$$

Since 5 is odd,

$$
(-1)^5=-1,
$$

and therefore

$$
\varphi(-1)=-\varphi.
$$

Hence `-goldenPhi` lies in sector `1` of the fifth-power classification.

## Role in the whole proof

This theorem is one of the base cases in the classification of golden units modulo fifth powers in `GoldenUnitClassification.lean`.

Immediately before this stage, the development has shown that a golden unit of measure 1 must be one of

$$
1,\quad -1,\quad \varphi,\quad -\varphi.
$$

The four corresponding lemmas

- `goldenUnitFifthClass_one`
- `goldenUnitFifthClass_neg_one`
- `goldenUnitFifthClass_phi`
- `goldenUnitFifthClass_neg_phi`

provide explicit fifth-power-class witnesses for these four terminal units.

The present theorem is the last of these four base lemmas. In the subsequent strong-induction theorem `goldenUnitFifthClass_of_unit`, it directly closes the branch `x=-\varphi`.

Thus the theorem itself contains no descent argument, but it is an indispensable finite base case linking the previously established measure-one classification to the general unit-classification theorem.

## Direct dependencies

### `GoldenUnitFifthClass`

This is the proposition proved by the theorem.

Conceptually it has the form

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

and expresses membership in one of five sectors modulo fifth powers.

### `goldenPhi`

The concrete golden integer representing $\varphi$.

The element classified here is `-goldenPhi`.

### `goldenOne`

The multiplicative identity $1$ of the golden integer ring.

The theorem uses `-goldenOne`, namely $-1$, as the fifth-power witness.

### `Fin 5`

The finite type restricting sector indices to `0,1,2,3,4`.

Here the witness

```lean
⟨1, by decide⟩
```

selects sector `1`.

### Negation, powers, and multiplication on the golden ring

These are needed to evaluate `-goldenOne`, `(-goldenOne)^5`, and `goldenPhi^1 * (-goldenOne)^5`.

## Proof construction

The proof has only two stages.

### 1. Build the existential witnesses

```lean
refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
```

This fills the two existential quantifiers of `GoldenUnitFifthClass (-goldenPhi)` with

```lean
i     := ⟨1, by decide⟩ : Fin 5
delta := -goldenOne
```

Mathematically,

$$
i=1,
\qquad
\delta=-1.
$$

The inner `by decide` proves the bound `1 < 5` required to construct the `Fin 5` value.

### 2. Close the remaining concrete equality

The remaining goal is conceptually

$$
-\varphi
=
\varphi^1(-1)^5.
$$

The Lean proof closes this with

```lean
decide
```

alone.

`GoldenInt` is a concrete integer-coordinate structure deriving `DecidableEq`, so this closed equality is computable. No symbolic ring normalization or explicit rewriting lemma is needed: the kernel can verify the decision procedure after evaluation.

## Lean-specific processing

### Constructing a `Fin 5` value

A value of `Fin 5` contains both a natural number and a proof that it lies below 5. Therefore the proof constructs sector 1 as

```lean
⟨1, by decide⟩
```

rather than merely writing a bare natural number in the underlying witness structure.

The `decide` here is Lean bookkeeping for the proposition `1 < 5`; it is not part of the mathematical substance.

### `refine` for nested existentials

Since `GoldenUnitFifthClass` contains two nested existential quantifiers,

```lean
refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
```

fills both the sector and fifth-power-base witnesses at once and leaves only the final equality as a metavariable goal.

### `decide` on a closed equality

The second `decide` proves a fully concrete equality in `GoldenInt`.

This is extremely concise and exploits the fact that there are no variables. From an explanatory perspective, however, it exposes less mathematical structure than a proof using explicit unfolding, `norm_num`, or ring normalization.

## Redundancy and repetition

The theorem itself is only two lines long, so there is essentially no local redundancy.

There is, however, strong repetition among the four surrounding base lemmas:

```lean
goldenUnitFifthClass_one
goldenUnitFifthClass_neg_one
goldenUnitFifthClass_phi
goldenUnitFifthClass_neg_phi
```

They all follow the same pattern:

1. choose a concrete `Fin 5` sector;
2. choose `goldenOne` or `-goldenOne` as the fifth-power base;
3. discharge a closed equality with `decide`.

Mathematically they form the symmetric 2×2 family

$$
1=\varphi^0 1^5,
\qquad
-1=\varphi^0(-1)^5,
$$

$$
\varphi=\varphi^1 1^5,
\qquad
-\varphi=\varphi^1(-1)^5.
$$

## Optimization candidates

### 1. A general negation-absorption lemma

Because the exponent 5 is odd, one could potentially prove a general statement of the form

```lean
GoldenUnitFifthClass x → GoldenUnitFifthClass (-x)
```

by replacing the witness `delta` with `-delta`.

Then `goldenUnitFifthClass_neg_one` and `goldenUnitFifthClass_neg_phi` could be derived from their positive counterparts.

Whether this actually reduces total Lean code depends on the cost of proving and using the general odd-power negation identity, so this remains an optimization candidate rather than a verified improvement.

### 2. Combine the four measure-one base lemmas

Instead of four separate private theorems, one could combine the measure-one classification with the fifth-class witnesses into a single finite-classification theorem.

The current design, however, has a readability advantage: each branch of `goldenUnitFifthClass_of_unit` can close using a clearly named theorem corresponding exactly to its terminal unit.

### 3. Replace `decide` with a structural proof

The current `decide` proof is minimal and robust.

For pedagogical or museum purposes, one could expose

$$
(-1)^5=-1
$$

explicitly and prove the target using `pow_succ`, ring laws, or definition unfolding. This would make the mathematics more visible but would not make the proof smaller.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

The theorem directly relies only on relatively basic facilities:

- `Fin`;
- `DecidableEq`;
- `decide`;
- the integer-based `GoldenInt` definitions already established in the development;
- existing `Neg`, `Mul`, and natural-power instances.

However, `GoldenInt`, `GoldenUnitFifthClass`, `goldenPhi`, and the relevant algebraic instances are local declarations in the FLT5 development. The exact minimal Mathlib import set cannot be determined safely from the standalone file alone.

It is likely possible to replace broad `import Mathlib` with narrower modules supplying finite types, integers, basic algebraic structures, and decidable equality. Because no Lean build is performed in this task, the exact minimal import set is unverified and should be treated as a hypothesis rather than a confirmed optimization.

## Comparator challenge suitability

**Yes. It is especially suitable as a micro challenge.**

A compact challenge can provide only:

- the minimal `GoldenInt` definition;
- `goldenOne`;
- `goldenPhi`;
- the required ring/power instances;
- `GoldenUnitFifthClass`;

with target

```lean
GoldenUnitFifthClass (-goldenPhi)
```

This is easy mathematically, but still tests whether a prover can

- construct nested existential witnesses correctly;
- handle the bound proof for `Fin 5`;
- recognize that the minus sign can be absorbed into an odd fifth power;
- choose an efficient method such as `decide`, `norm_num`, or explicit unfolding for the concrete equality.

A stronger Comparator challenge would provide `goldenUnitFifthClass_phi` and ask the prover first to derive a general negation-preservation lemma, then obtain `goldenUnitFifthClass_neg_phi` as a corollary.

## Technical meaning

The essential point is that **sign does not create a new sector modulo fifth powers**.

Because 5 is odd,

$$
-1=(-1)^5
$$

can be absorbed completely into the fifth-power factor. Consequently

$$
\varphi
\quad\text{and}\quad
-\varphi
$$

belong to the same sector `1`.

Likewise,

$$
1
\quad\text{and}\quad
-1
$$

both belong to sector `0`.

Thus the four measure-one units collapse, after fifth-power equivalence, to the two sectors `0` and `1`. The remaining sector movement is generated by `goldenUnitFifthClass_mul_phi` and `goldenUnitFifthClass_mul_phiInv`. Combined with strict descent, this finite sector structure allows the proof to classify every golden unit.

## Next declaration to read

The next declaration is

```lean
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := by
  ...
```

It is the central theorem of `GoldenUnitClassification.lean`.

It combines the four measure-one base lemmas completed here with the previously established strict descent

```lean
goldenUnit_descent
```

and the sector-preservation lemmas

```lean
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

using `Nat.strong_induction_on`. The result is that every golden unit belongs to one of the five classes modulo fifth powers.

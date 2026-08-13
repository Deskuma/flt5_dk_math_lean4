# 0120 — `goldenOne`

## Lean type

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

`goldenOne` is the element of `GoldenInt`, introduced in 0118, whose first coordinate is the integer $1$ and whose second coordinate is the integer $0$.

$$
goldenOne=(1,0).
$$

Reading `GoldenInt` as the coordinate model $a+b\varphi$, this corresponds to

$$
1+0\varphi=1.
$$

## Mathematical statement

This declaration is a definition rather than a theorem. It gives the concrete candidate for the multiplicative identity in golden-integer coordinates.

At this point the Lean typeclass `[One GoldenInt]` has not yet been introduced. Later in the source one finds

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

and only there does the ordinary notation `(1 : GoldenInt)` become connected to `goldenOne`.

Thus 0120 is the layer that fixes the coordinate value of the multiplicative identity, intentionally separated from the layer that exposes it through the typeclass interface.

## Role in the overall proof

`GoldenOrder.lean` develops `GoldenInt` into a direct coordinate model of the ring $\mathbb Z[\varphi]$. Declaration 0118 fixes the carrier, 0119 fixes the candidate zero element, and 0120 fixes the candidate multiplicative identity.

Immediately afterward come `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`; these are then connected to the `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` instances. Coordinate simplification lemmas and the ring laws are built later. Hence `goldenOne` is the minimal component that fixes the multiplicative identity of the golden-integer ring as concrete coordinates.

It is also used directly as the base case of `goldenPow`:

```lean
| 0 => goldenOne
```

so it is not merely a notation-oriented definition. It is the computational anchor of the recursive natural-power API.

This declaration does not itself process FLT5-specific five-adic data or square-golden packets, but it belongs to the algebraic infrastructure supporting the later golden-integer divisibility theory, norm, Euclidean-domain structure, unit classification, and extraction of fifth-power factors.

## Direct dependencies

The direct dependency is essentially only 0118 `GoldenInt`.

- `GoldenInt` — the target type being constructed.
- Integer literals `1 : ℤ` and `0 : ℤ` — the values of `fst` and `snd`.
- Structure-constructor notation `⟨1, 0⟩` — shorthand for `GoldenInt.mk 1 0`.

No logical lemma or tactic is needed. There is no direct dependency on the FLT5 equation, five-adic packets, or square-golden exceptional packets.

The main immediate downstream uses are the zero-exponent case of `goldenPow` and the `One GoldenInt` instance.

## Proof / construction flow

There is no proof script. The definition body itself is a structure-constructor application:

```lean
⟨1, 0⟩
```

From the expected type `GoldenInt`, Lean interprets this conceptually as

```lean
GoldenInt.mk 1 0
```

so after unfolding,

```lean
goldenOne.fst = 1
goldenOne.snd = 0
```

follow by definitional reduction.

After the later declaration

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

the expressions

```lean
(1 : GoldenInt).fst = 1
(1 : GoldenInt).snd = 0
```

also become `rfl`-based simplification facts. The source indeed provides `golden_fst_one` and `golden_snd_one` as `[simp]` theorems.

## Lean-specific processing

### Constructor inference from the expected type

The expression `⟨1, 0⟩` does not explicitly mention `GoldenInt.mk`; Lean infers the constructor from the declared result type `GoldenInt`.

### Elaboration of numeric literals

The literals `1` and `0` elaborate as integers because the fields `GoldenInt.fst` and `GoldenInt.snd` have type `ℤ`. In particular, the `1` here does not require a `One GoldenInt` instance: it uses the `OfNat` structure of the coordinate type `ℤ`.

### Definitional equality

The coordinates of `goldenOne` are not established by a theorem but fixed by the definition itself. Consequently `rfl`, `simp [goldenOne]`, or `dsimp [goldenOne]` can expose them directly.

### Separation of raw definition and typeclass instance

The later

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

introduces ordinary `1` notation for `GoldenInt`. This separation between concrete implementation and typeclass registration is paired with 0119 `goldenZero`.

### Base case of exponentiation

The later `goldenPow` is defined as

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

Thus `goldenOne` is also the recursion anchor corresponding to $x^0=1$.

## Redundancy and duplication

The declaration body itself is minimal and contains no internal redundancy.

At the design level it mirrors 0119 `goldenZero` almost exactly:

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
def goldenOne  : GoldenInt := ⟨1, 0⟩
```

This duplication is naturally read as intentional symmetry in the primitive API. The concrete coordinates of zero and one are given names before being connected to typeclass instances, allowing the raw operations to be referenced before the ring structure is established.

It would be possible to inline the value directly into the `One GoldenInt` instance:

```lean
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
```

and eliminate the name `goldenOne`. Doing so, however, would remove a named concrete unit from the API, including the value used in the base case of `goldenPow` and in later proofs.

## Optimization candidates

### 1. Inline into the `One` instance

If minimizing lines of code were the only objective, `goldenOne` could be removed and `⟨1,0⟩` placed directly in the `One GoldenInt` instance. This would, however, make `goldenPow` and other primitive code depend more directly on the typeclass layer, weakening the current separation between the coordinate implementation and algebraic registration.

### 2. Define `goldenPow` only after standard `Pow`

The current explicit API uses `goldenOne` in the zero-exponent branch of `goldenPow`. If `One` and `Mul` were established first, one could potentially rely more directly on standard exponentiation. Such a reordering may change definitional behavior in downstream proofs, so it is not necessarily a drop-in replacement.

### 3. Factor zero and one through a common integer embedding

One could introduce

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

and define `goldenZero := goldenOfInt 0` and `goldenOne := goldenOfInt 1`. This may become useful if an explicit integer-embedding API is desired later, but for only these two declarations it may add more abstraction than it removes.

### 4. Keep the simp API centralized

The source already provides

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

after the instance is introduced. Separate simp lemmas for `goldenOne.fst` and `.snd` therefore appear unnecessary unless a specific raw-API use case emerges.

## Required Mathlib imports and import-optimization candidates

The standalone source begins with

```lean
import Mathlib
```

as a single aggregate import.

For `goldenOne` by itself, once `GoldenInt` and the integer type are available, no new Mathlib theorem is required. The declaration only needs a structure constructor and integer literals, so importing all of `Mathlib` solely for this definition would be unnecessary.

At the `GoldenOrder.lean` module level, however, the later development includes the ring structure, integer polynomial calculations, conjugation and norm, a map into `Zsqrtd 5`, zero-divisor elimination, and proofs using `simp` and `ring`; the true minimal import set for the whole module is therefore larger.

No Lean build is run for this museum entry, so the exact minimal import set is unverified. Import reduction is therefore recorded only as an optimization candidate.

## Comparator challenge suitability

As a one-line definition, `goldenOne` is too small to make a meaningful standalone challenge. It is useful, however, as part of a Comparator challenge about the design of the primitive `GoldenInt` API.

Possible designs to compare are: (a) the current raw definition plus `One` instance, (b) direct inlining into the `One` instance, (c) introducing an integer embedding such as `goldenOfInt` first, and (d) constructing the standard ring structure early and using only `(1 : GoldenInt)` afterward.

Useful evaluation criteria are transparency under definitional reduction, naturalness of `goldenPow`, dependency on typeclass infrastructure, stability of `simp`, brevity of downstream ring-law proofs, and auditability.

## Sources and scope of inference

The formal source is the `DkMath/FLT/Five/GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. There `goldenOne` appears immediately after `GoldenInt` and `goldenZero`, followed by `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`.

The target branch contains both the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. In this run the GitHub connector did not provide direct inspection of the PDF page corresponding to `goldenOne`, so no page number, section number, or PDF-specific wording is inferred.

`goldenOfInt`, import minimization, and integration with standard exponentiation are optimization proposals, not claims about the current source.

## Next declaration to read

The next declaration in dependency order is

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

With 0119 and 0120, the distinguished elements zero and one are in place. The development now moves to the first binary operation: coordinatewise addition of two golden integers. Therefore `goldenAdd` is the natural subject of the next entry.
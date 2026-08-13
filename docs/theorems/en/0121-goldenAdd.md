# 0121 — `goldenAdd`

## Lean type

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

`goldenAdd` is the binary operation that adds the two coordinates of the `GoldenInt` introduced in 0118 componentwise.

Reading `GoldenInt` in coordinates as

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

the definition corresponds to

$$
goldenAdd(x,y)=(a+c)+(b+d)\varphi.
$$

## Mathematical statement

This declaration is a definition rather than a theorem. It defines addition in the golden-integer coordinate system as ordinary integer addition in each coordinate:

$$
(a,b)+(c,d)=(a+c,b+d).
$$

At this point the Lean typeclass `[Add GoldenInt]` has not yet been introduced. Later in the source one finds

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

which makes the standard notation `x + y` refer to `goldenAdd x y`.

Thus 0121 is the primitive API that fixes addition in the golden order as a concrete coordinate operation.

## Role in the full proof

`GoldenOrder.lean` grows `GoldenInt` from a bare integer pair into the commutative ring used by the later FLT5 argument. Declaration 0118 provides the carrier, 0119 `goldenZero` provides the zero candidate, 0120 `goldenOne` provides the multiplicative identity candidate, and 0121 `goldenAdd` introduces the first binary operation.

Immediately afterward the source defines

```lean
def goldenNeg ...
def goldenSub ...
def goldenMul ...
def goldenPow ...
```

and then registers `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` instances before constructing `AddCommGroup` and `CommRing` instances.

In particular, the later declaration

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

uses `goldenAdd` as the actual addition, reducing associativity, zero laws, inverse laws, and commutativity to integer arithmetic on the two coordinates. Therefore 0121 is not merely a convenience wrapper; it fixes the additive structure of the golden order itself.

It does not directly manipulate FLT5-specific five-adic packets or descent data, but all later conjugation, norm, divisibility, Euclidean-domain structure, unit classification, and fifth-power factor extraction rely on the resulting ring structure.

## Direct dependencies

The direct dependency set is very small.

- `GoldenInt` — the input and output type.
- `GoldenInt.fst`, `GoldenInt.snd` — projections to the two integer coordinates.
- integer addition on `ℤ` — addition in each coordinate.
- the `GoldenInt` structure constructor — the result is built with `⟨..., ...⟩`.

No logical theorem, FLT5 equation, five-adic lemma, or golden-norm lemma is directly required.

The main direct downstream users are the `Add GoldenInt` instance, `goldenSub`, `goldenAddCommGroup`, and the coordinate simp theorems `golden_fst_add` and `golden_snd_add`.

## Proof / construction flow

There is no proof script. The body of the definition is itself the computation rule.

1. Add `x.fst` and `y.fst` as integers.
2. Add `x.snd` and `y.snd` as integers.
3. Pass the resulting two integers to the `GoldenInt` constructor.

Thus unfolding

```lean
goldenAdd x y
```

yields

```lean
⟨x.fst + y.fst, x.snd + y.snd⟩.
```

After the `Add GoldenInt` instance is installed, the source proves

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

by `rfl`. Hence there is no proof-level gap between standard addition notation and the raw coordinate definition.

## Lean-specific processing

### Coordinate operations through projections

`x.fst` and `x.snd` are structure projections. The operation extracts the explicit coordinates and computes there; no quotient, coercion, or abstract ring layer is involved.

### Constructor inference from the expected type

Because the return type is known to be `GoldenInt`, Lean elaborates

```lean
⟨x.fst + y.fst, x.snd + y.snd⟩
```

as an application of `GoldenInt.mk`.

### Definitional equality

`goldenAdd` is a definition rather than an opaque theorem, so coordinate equations follow by unfolding and `rfl`. This is what makes the later `[simp]` coordinate lemmas and ring-law proofs lightweight.

### Separation of raw operation and typeclass operation

The source first defines `goldenAdd` and only later registers

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩.
```

This permits the raw operation to be referenced before the typeclass hierarchy is assembled and keeps the same explicit-API design used for `goldenSub`, `goldenMul`, and the other primitive operations.

### Interaction with `simp`

After the `Add` instance is installed, `golden_fst_add` and `golden_snd_add` are `[simp]` theorems proved by `rfl`. Later proofs can therefore reduce GoldenInt addition automatically to integer coordinate addition.

## Redundancy and duplication

The definition itself is minimal and contains no internal redundancy.

At the API level, however, the later declaration

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

means that `goldenAdd` and standard `x + y` ultimately name the same operation. Still later, the source also provides

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) : goldenAdd x y = x + y := rfl.
```

This is not logical duplication so much as an intentional two-layer design connecting an explicit coordinate API to the Mathlib typeclass API.

There is also a related pattern with `goldenNeg`; `goldenSub` is defined as

```lean
goldenAdd x (goldenNeg y).
```

By fixing addition as a primitive once, subtraction does not need to re-expand both coordinates independently.

## Optimization candidates

### 1. Inline directly into the `Add` instance

If minimizing lines of code were the only goal, one could write

```lean
instance : Add GoldenInt :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩.
```

This would remove the named raw operation, but it would make `goldenSub` and other explicit APIs more dependent on typeclass elaboration and reduce auditability of the primitive coordinate layer.

### 2. Implement the carrier as `ℤ × ℤ`

Using a product type might allow reuse of its existing componentwise addition. The tradeoff is that the domain-specific meaning of the two coordinates would no longer be expressed by a dedicated structure, weakening readability and namespace organization in the golden-order API.

### 3. Build `AddCommGroup` first

One could construct `AddCommGroup GoldenInt` directly and obtain primitive additive instances from that bundle. The current order instead exposes the coordinate operations first, making their computation rules explicit and preserving simple `rfl`-based simp lemmas.

### 4. Generalize a coordinatewise-operation helper

A generic helper applying a binary integer operation to both coordinates is possible. But `goldenMul` mixes coordinates, so such an abstraction would not cover the full primitive API. For `goldenAdd` alone the abstraction cost would likely exceed the benefit.

## Required Mathlib imports and import-optimization candidates

The standalone source begins with

```lean
import Mathlib
```

as a single broad import.

`goldenAdd` itself only requires that `GoldenInt` and integer addition already be available. It does not use `ring`, `simp`, `omega`, number-field APIs, or Euclidean-domain APIs.

Therefore importing all of `Mathlib` solely for this declaration would clearly be excessive; a very small import supplying the integer type and its addition should suffice once `GoldenInt` is available.

However, `GoldenOrder.lean` as a whole later needs `AddCommGroup`, `CommRing`, `Zsqrtd 5`, `NoZeroDivisors`, `IsDomain`, and tactics such as `ring`, `omega`, and `norm_num`. The exact minimal import set for the complete module has not been verified because no Lean build is performed in this museum run, so import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

`goldenAdd` by itself is only a one-line definition, so it is too small for a proof-search challenge. It is, however, a useful data-model / API-design Comparator challenge.

Possible implementations to compare are:

- current design: define raw `goldenAdd`, then register it as the `Add` instance;
- typeclass-first design: define `Add GoldenInt` directly, then define `goldenAdd := (· + ·)` if a named operation is still wanted;
- bundled algebra design: construct `AddCommGroup` directly and derive primitive instances from it;
- represent the carrier as `ℤ × ℤ` and reuse product addition.

Useful evaluation axes are strength of definitional equality, stability of `rfl` / `simp`, naturalness of the later `goldenSub`, brevity of the ring-structure construction, source auditability, and amount of Mathlib typeclass dependency.

## Source basis and scope of inference

The formal source is the `DkMath/FLT/Five/GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch. There `goldenAdd` appears immediately after `goldenOne` and is followed by `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`.

The branch also contains the existing Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The page corresponding specifically to `goldenAdd` was not directly inspected in this run, so no PDF page number, section number, or PDF-specific narrative claim is inferred.

The standalone source is itself marked as a generated artifact and lists `DkMath/FLT/Five/GoldenOrder.lean` as the originating source module. This provenance statement is taken from the source header.

## Next declaration to read

The next unexplained declaration in dependency order is

```lean
def goldenNeg (x : GoldenInt) : GoldenInt := ⟨-x.fst, -x.snd⟩
```

Where `goldenAdd` introduces additive composition, `goldenNeg` negates each coordinate and supplies additive inverses. Once both are available, the following `goldenSub` can be defined as

```lean
goldenAdd x (goldenNeg y),
```

so 0122 should naturally examine the additive inverse operation in the golden integers.

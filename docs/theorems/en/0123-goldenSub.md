# 0123 — `goldenSub`

## Lean type

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

`goldenSub` defines subtraction on `GoldenInt` as the composition of the already introduced addition `goldenAdd` and additive inverse `goldenNeg`.

## Mathematical statement

Read `GoldenInt` as the coordinate representation of golden integers

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

with

$$
\varphi^2=\varphi+1.
$$

Then

$$
x-y=(a-c)+(b-d)\varphi.
$$

Rather than writing this coordinate formula again, the Lean definition directly adopts the standard additive-group identity

$$
x-y=x+(-y).
$$

Thus computationally,

```text
goldenSub ⟨a,b⟩ ⟨c,d⟩
  = goldenAdd ⟨a,b⟩ (goldenNeg ⟨c,d⟩)
  = goldenAdd ⟨a,b⟩ ⟨-c,-d⟩
  = ⟨a-c,b-d⟩
```

## Role in the overall proof

This declaration is not itself a number-theoretic lemma closing any part of FLT5. It belongs to the foundational layer constructing the basic operation API for the later golden integer ring `GoldenInt`.

After 0118 introduces the carrier `GoldenInt`, 0119 `goldenZero`, 0120 `goldenOne`, 0121 `goldenAdd`, and 0122 `goldenNeg`, the present declaration supplies subtraction. It is followed by `goldenMul` and `goldenPow`, and later the standard instance

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

registers this raw operation as Lean's ordinary subtraction on `GoldenInt`.

Accordingly, `goldenSub` is an intermediate layer between the explicit coordinate API and standard algebraic notation used by the later ring, norm, divisibility, and Euclidean-domain developments.

## Direct dependencies

The direct dependencies are:

1. `GoldenInt`
2. `goldenAdd`
3. `goldenNeg`

There is no dependency on a proved theorem. `goldenSub` is a `def`, hence a computational definition rather than a proof term.

The dependency graph is

```text
GoldenInt
  ├─ goldenAdd
  └─ goldenNeg
       ↓
   goldenSub
```

## Definition flow

There is no tactic proof. The right-hand side can simply be evaluated in two stages.

1. `goldenNeg y` negates both coordinates of `y`.
2. `goldenAdd x (...)` adds the result coordinatewise to `x`.
3. Hence the result is mathematically `x + (-y)`, i.e. `x-y`.

The important design choice is that the coordinate formula

$$
\langle a-c,b-d\rangle
$$

is not duplicated as a second implementation. The existing addition and negation operations are reused directly.

## Lean-specific processing

### 1. Composition of raw operations

At this stage the `Sub GoldenInt` instance is not yet used. The definition explicitly calls `goldenAdd` and `goldenNeg`, so its dependencies remain visible and it does not rely on typeclass inference.

### 2. Definitional reduction

Because `goldenSub` is a one-line definition, unfolding it reduces subtraction to the coordinate computations of `goldenAdd` and `goldenNeg`. Later coordinate `simp` lemmas can therefore be very short and may rely substantially on definitional transparency.

### 3. Separation from notation

Only later does

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

make standard `x - y` notation available for `GoldenInt`. This raw-definition → typeclass-instance layering matches the design already used for `goldenAdd` and `goldenNeg`.

## Redundancy and duplication

Mathematically one could instead write

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst - y.fst, x.snd - y.snd⟩
```

so the current definition is one level more indirect.

This is better understood as intentional reuse than as needless duplication. In an additive group, subtraction is conventionally derived from addition and negation, and the present definition avoids maintaining a second coordinate formula independently.

## Optimization candidates

### Candidate A — Keep the current definition

This is the clearest option if the goal is to keep the primitive operation set small: `goldenAdd` and `goldenNeg` are primitive, while `goldenSub` is derived by composition.

### Candidate B — Define the `Sub` instance directly

If the raw name `goldenSub` is never needed downstream, it could be inlined as

```lean
instance : Sub GoldenInt :=
  ⟨fun x y => goldenAdd x (goldenNeg y)⟩
```

This removes one declaration but weakens naming, debugging visibility, and theorem-museum traceability.

### Candidate C — Write coordinate subtraction directly

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst - y.fst, x.snd - y.snd⟩
```

is syntactically direct, but then agreement with `goldenAdd` and `goldenNeg` becomes a separate fact to maintain. The current compositional version better exposes the intended additive hierarchy.

## Required Mathlib import and import optimization

On the target branch, the formal source available in the repository is `Flt5DkMath/FLT5StandAlone.lean`, whose standalone development uses `Mathlib`. The `Flt5DkMath` tree currently contains only `Basic.lean` and `FLT5StandAlone.lean`; there is no separately stored `GoldenOrder.lean` module.

The declaration `goldenSub` itself needs very little: `GoldenInt`, integers `ℤ`, addition, negation, and the earlier definitions `goldenAdd` / `goldenNeg`. Therefore importing all of `Mathlib` solely for this declaration is theoretically unnecessary.

However, this run does not perform a Lean build, so the exact minimal import set is unverified and no specific minimal module list is asserted.

## Comparator challenge suitability

**Suitable.** It is small, but the design alternatives are cleanly separated.

A Comparator challenge can compare:

1. composition via `goldenAdd x (goldenNeg y)`,
2. direct coordinate subtraction,
3. inlining the implementation into the `Sub GoldenInt` instance.

Useful evaluation criteria are duplication, downstream `simp` behavior, fit with the algebraic hierarchy, readability, and usefulness of definitional equality.

The current design is strong under the criterion of keeping the primitive operation set small.

## Relation to existing materials

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

In this run, the corresponding `goldenSub` page could not be extracted directly from the PDFs through GitHub, so no PDF page number, section number, or wording is guessed. The formal content is grounded in the `GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

This is the first nontrivial operation on `GoldenInt` whose coordinates genuinely use the relation

$$
\varphi^2=\varphi+1.
$$

Up through `goldenSub`, the additive structure is essentially coordinate arithmetic on `ℤ^2`. With `goldenMul`, the defining quadratic relation of the golden order enters the computation for the first time. Therefore 0124 should naturally cover `goldenMul` next.

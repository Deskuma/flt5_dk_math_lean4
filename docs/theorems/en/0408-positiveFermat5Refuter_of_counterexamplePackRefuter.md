# 0408 `positiveFermat5Refuter_of_counterexamplePackRefuter`

## Declaration kind

`theorem`

## Lean type

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

Expanding only the types, the input is a proof that every primitive counterexample is impossible,

```lean
hPrimitive : CounterexamplePackRefuter
```

and the output is a proof that every positive-natural-number FLT5 solution is impossible,

```lean
PositiveFermat5Refuter
```

Expanding the `abbrev`s from 0403 and 0407, this theorem is conceptually of the form

```lean
(∀ {x y z : ℕ}, CounterexamplePack x y z → False) →
  (∀ x y z : ℕ,
    0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z)
```

## Mathematical statement

The mathematical content is the closure of primitive reduction: **if all primitive FLT5 candidates can be excluded, then every positive-integer FLT5 solution can be excluded**.

Assume positive integers $x,y,z$ satisfy

$$
x^5+y^5=z^5.
$$

By 0406 `exists_counterexamplePack_of_positive_fermat5`, one obtains positive integers $x',y',z'$ such that

$$
\gcd(x',y')=1,
\qquad
{x'}^5+{y'}^5={z'}^5,
$$

packaged as

$$
\mathrm{CounterexamplePack}(x',y',z').
$$

But `hPrimitive : CounterexamplePackRefuter` turns every such packet into `False`. Hence the assumed positive solution is impossible.

The logical route is

$$
\text{positive FLT5 solution}
\longrightarrow
\text{primitive normalization}
\longrightarrow
\mathrm{CounterexamplePack}
\longrightarrow
\bot.
$$

## Role in the whole proof

By 0406 the development has separated into two layers.

1. On the `CounterexamplePackRefuter` side, the local number theory for primitive packets—golden integers, unit classes, the zero sector, and infinite descent—is closed behind a refuter interface.
2. On the `exists_counterexamplePack_of_positive_fermat5` side, an arbitrary positive solution is normalized by a gcd reduction to a primitive packet.

0408 connects these two layers.

Crucially, this theorem itself knows nothing about the internal golden-integer, five-adic, unit-class, or descent arguments. All primitive arithmetic is hidden behind

```lean
CounterexamplePackRefuter
```

as an interface.

Architecturally, 0408 is therefore the **normalization-to-refutation bridge**

$$
\text{primitive core}
\Longrightarrow
\text{full positive FLT5 target}.
$$

## Direct dependencies

### `CounterexamplePackRefuter`

The `abbrev` from 0403:

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

This is the type of the hypothesis `hPrimitive` and is used directly in

```lean
exact hPrimitive p
```

at the end of the proof.

### `PositiveFermat5Refuter`

The `abbrev` from 0407:

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

This is the conclusion type of 0408.

### `exists_counterexamplePack_of_positive_fermat5`

The theorem from 0406:

```lean
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

It is the normalization theorem converting a positive FLT5 solution into a primitive packet and is the only substantive mathematical transformation performed by 0408.

### `CounterexamplePack`

0408 does not inspect any field of this structure. It is only the intermediate data type produced by 0406 and consumed by `hPrimitive`.

Thus 0408 is also independent of the internal representation of `CounterexamplePack` beyond its type.

## Proof flow

### 1. Introduce the arguments of `PositiveFermat5Refuter`

```lean
intro x y z hx hy hz hEq
```

Because `PositiveFermat5Refuter` is an `abbrev`, Lean transparently sees the target as

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z →
  Fermat5Equation x y z → False
```

and introduces

- `x y z : ℕ`,
- `hx : 0 < x`,
- `hy : 0 < y`,
- `hz : 0 < z`,
- `hEq : Fermat5Equation x y z`.

### 2. Normalize the positive solution to a primitive packet

```lean
rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
  ⟨x', y', z', p⟩
```

0406 yields

```lean
∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

so `rcases` extracts

```lean
x' y' z' : ℕ
p : CounterexamplePack x' y' z'
```

as witnesses.

### 3. Feed the packet to the primitive refuter

```lean
exact hPrimitive p
```

Since `hPrimitive` has type

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

Lean infers the dependent indices `x' y' z'` from the type of `p`, and the result is `False`.

This contradicts the originally assumed equation `hEq`.

## Lean-specific processing

### Transparent unfolding of `abbrev`

The target is the named proposition

```lean
PositiveFermat5Refuter
```

but the proof does not need

```lean
unfold PositiveFermat5Refuter
```

because `abbrev` is reducible and `intro` can see its function type.

Likewise, `hPrimitive` can be applied as a function through the transparent expansion of `CounterexamplePackRefuter`.

### `¬ P` is `P → False`

In Lean,

```lean
¬ P
```

is definitionally

```lean
P → False
```

which is why the final equation hypothesis `hEq` can be introduced by the same `intro` command.

### Dependent existential elimination with `rcases`

The conclusion of 0406 contains three witnesses together with a packet whose type depends on all three:

```lean
∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

The command

```lean
rcases ... with ⟨x', y', z', p⟩
```

eliminates this dependent existential in one step. It is not merely destructuring an ordinary four-component tuple.

### Inference of implicit indices

The binders of `CounterexamplePackRefuter` are implicit:

```lean
∀ {x y z : ℕ}, ...
```

Therefore

```lean
hPrimitive p
```

is enough: Lean reconstructs `x'`, `y'`, and `z'` from

```lean
p : CounterexamplePack x' y' z'.
```

## Redundancy and duplication

The proof is already extremely short and contains no duplicated number-theoretic argument.

However, in

```lean
⟨x', y', z', p⟩
```

the names `x'`, `y'`, and `z'` are not explicitly used later in the source. Lean could therefore accept a style such as

```lean
rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
  ⟨_, _, _, p⟩
exact hPrimitive p
```

in which the witness names are discarded.

The current names are nevertheless explanatory: they make it visually clear that normalization has produced a new primitive triple.

0408 is also used by the following theorem

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

as a thin composition component. Having several small bridge theorems is not merely accidental duplication; it exposes meaningful dependency boundaries in the proof architecture.

## Optimization candidates

### 1. Omit unused witness names

If minimizing source size is the priority, one could write

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  obtain ⟨_, _, _, p⟩ :=
    exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq
  exact hPrimitive p
```

The change is only stylistic; it does not improve the dependency graph or proof complexity.

### 2. A generic normalization/refuter lifting lemma

Abstractly, 0408 has the logical shape

$$
(A\to\exists b,B(b))
\to
(\forall b,B(b)\to\bot)
\to
(A\to\bot).
$$

If many identical bridges existed, this could be factored into a generic helper. Here the concrete proof is only a few lines and directly communicates the FLT5 normalization path, so further abstraction would likely reduce readability.

For that reason, **keeping the current implementation is the more natural choice**.

### 3. Shortening to term-style composition

Unlike 0405, this theorem must eliminate an existential witness before applying the next function. A `by` proof block therefore expresses the control flow more clearly than attempting to force the theorem into a one-line composition term.

## Required Mathlib imports

The standalone source of record, `Flt5DkMath/FLT5StandAlone.lean`, uses

```lean
import Mathlib
```

The proof body of 0408 directly uses only lightweight Lean/Mathlib mechanisms:

- `intro`,
- `rcases`,
- existential elimination,
- `exact`,
- the preceding declaration `CounterexamplePackRefuter`,
- the preceding declaration `PositiveFermat5Refuter`,
- the preceding theorem `exists_counterexamplePack_of_positive_fermat5`.

It does not directly call ring, gcd, divisibility, valuation, or golden-integer APIs.

### Import optimization candidate

The exact minimal import for the original split module `SignedGoldenClosure.lean` depends on the imports required by all preceding FLT5 declarations in that module graph. Determining the exact minimum would require a Lean build, which is outside the present task.

What can be established without that build is:

- the standalone source uses `import Mathlib`;
- the proof body of 0408 itself has no direct dependency on advanced Mathlib number-theory theorems;
- once `rcases` and the preceding FLT5 declarations are available, the proof is lightweight.

A specific minimal Mathlib module name is therefore not claimed here.

## Comparator challenge viability

**Yes. It is suitable as a small Lean-interface challenge.**

It is more meaningful than challenging the 0407 `abbrev` alone.

A challenge can provide the context

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False

abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z

axiom exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

and ask the model to fill the proof of 0408.

This tests

- handling of reducible `abbrev`s,
- understanding `¬ P` as a function type,
- unpacking a dependent existential,
- implicit-parameter inference,
- application of the primitive refuter.

The mathematical difficulty is low, but it is a useful challenge for Lean proposition plumbing. It is not a strong challenge for the number theory of FLT5 itself, because all difficult arithmetic has already been hidden behind the primitive layer.

## Next declaration to read

The next declaration is 0409:

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

Where 0408 establishes

$$
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter},
$$

0409 starts further upstream with

$$
\mathrm{GoldenUnitClassesModFifth}
$$

and

$$
\mathrm{GoldenZeroSectorArithmeticExclusion},
$$

builds the primitive refuter, and passes it into 0408.

The dependency chain therefore becomes

$$
\text{unit classes + zero-sector arithmetic}
\longrightarrow
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter}.
$$
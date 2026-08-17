# 0146 — `goldenAddGroupWithOne`

## Lean type

```lean
instance goldenAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { goldenAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }
```

This is not a theorem but a named `instance`. It extends the `AddCommGroup GoldenInt` structure constructed in 0145 by adding the standard casts from natural numbers and integers, thereby providing `AddGroupWithOne GoldenInt`.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents $a+b\varphi$ by the integral coordinate pair `(a,b)`. A natural number $n$ and an integer $z$ are embedded into the golden integers as

$$
n \longmapsto n+0\varphi,
$$

$$
z \longmapsto z+0\varphi.
$$

The fields

```lean
natCast := fun n => ⟨n, 0⟩
intCast := fun z => ⟨z, 0⟩
```

implement exactly this standard embedding along the basis direction `1`.

Mathematically, the declaration introduces no new operation on the golden integers. It equips the commutative additive group already established in 0145 with the standard interpretation of ordinary natural and integer constants as elements of `GoldenInt`.

## Role in the overall proof

After 0145 `goldenAddCommGroup`, `GoldenInt` already participates in Mathlib's algebra hierarchy as a commutative additive group. At that stage, however, the standard connection between natural/integer casts and the additive structure has not yet been packaged as `AddGroupWithOne`.

The present declaration builds the bridge

$$
\texttt{AddCommGroup GoldenInt}
\longrightarrow
\texttt{AddGroupWithOne GoldenInt}.
$$

This bridge is important because the immediately following 0147 `goldenCommRing` reuses `goldenAddGroupWithOne` as its base structure while adding multiplication and power laws. Thus 0146 closes the cast / numeral layer between the additive group and the complete ring structure.

In the full FLT5 development, ordinary notation for `0`, `1`, natural numbers, and integer coefficients inside `GoldenInt` is essential for norm identities, conjugation, divisibility, Euclidean-domain arguments, and fifth-power factorizations.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0145 `goldenAddCommGroup`
- `AddGroupWithOne`
- the coercion from natural numbers to integers
- the `GoldenInt` constructor `⟨_, _⟩`

There is almost no theorem-level dependency. The declaration reuses the additive-group structure from 0145 and supplies only the concrete implementations of `natCast` and `intCast`.

Conceptually the dependency chain is

$$
\texttt{goldenAddCommGroup}
\longrightarrow
\texttt{goldenAddGroupWithOne}
\longrightarrow
\texttt{goldenCommRing}.
$$

## Proof / construction flow

There is no tactic proof. The declaration uses the structure-update syntax

```lean
{ goldenAddCommGroup with
  natCast := fun n => ⟨n, 0⟩
  intCast := fun z => ⟨z, 0⟩ }
```

to reuse the additive structure provided by 0145 and add the cast implementations required for `AddGroupWithOne`.

For a natural number `n`, the first coordinate receives `n` coerced to an integer and the second coordinate is fixed to `0`. For an integer `z`, the first coordinate receives `z` directly and the second coordinate is again `0`.

Thus the standard cast machinery can represent

$$
(n : \texttt{GoldenInt})=(n,0),
$$

and

$$
(z : \texttt{GoldenInt})=(z,0).
$$

## Lean-specific processing

The key Lean feature is the structure update

```lean
{ goldenAddCommGroup with ... }
```

which reuses the fields of the additive-group structure explicitly constructed in 0145 while supplying the additional fields needed at the higher algebra level.

In

```lean
natCast := fun n => ⟨n, 0⟩
```

the variable `n : ℕ` is placed in a coordinate whose type is `ℤ`, so Lean inserts the corresponding coercion. In

```lean
intCast := fun z => ⟨z, 0⟩
```

the integer `z : ℤ` can be used directly as the first coordinate.

There is no tactic proof here: the concrete representation of casts is fixed at the definition level. This keeps later unfolding of numerals and integer casts transparent, making them reduce naturally to coordinates of the form `(z,0)`.

The exact internal inheritance fields and default implementations of `AddGroupWithOne` can depend on the Mathlib version. This document therefore relies on the source-level fact that this structure update is the implementation used here and does not infer unverified details of the internal hierarchy.

## Redundancy and duplication

The `natCast` and `intCast` implementations are mathematically almost identical:

$$
n \mapsto (n,0),\qquad z \mapsto (z,0).
$$

This creates a small amount of duplication. Since `GoldenInt` is fundamentally an integral coordinate pair, one could instead define a shared helper such as an embedding of integers into the constant coordinate and reuse it from both casts.

The current implementation nevertheless has the advantage that each Mathlib field directly displays the concrete representation of its cast, making the interface easy to audit.

## Optimization candidates

Several alternatives are worth comparing:

1. retain the direct `natCast` / `intCast` definitions;
2. introduce a helper such as `goldenOfInt : ℤ → GoldenInt := fun z => ⟨z,0⟩` and reuse it from both casts;
3. transport the cast structure through an isomorphism with an existing quadratic-order representation;
4. construct `CommRing` directly and omit the explicit intermediate `AddGroupWithOne` instance.

Option 4 may reduce source length, but it also hides the bootstrap stages additive group → cast layer → commutative ring. For an auditable development, keeping 0146 explicit has a clear design value.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This declaration itself needs `AddGroupWithOne`, natural/integer casts, the upstream `goldenAddCommGroup`, and the `GoldenInt` constructor. It uses no advanced number-theory theorem.

Therefore the full `Mathlib` umbrella import is unlikely to be required solely for this declaration. The exact minimal import, however, depends on the upstream `GoldenOrder` definitions and version-specific details of Mathlib's algebra hierarchy, and would need to be verified by a Lean build. No Lean build is performed in this museum pass, so no exact minimal import module is claimed.

## Suitability as a Comparator challenge

Yes. In particular, the following implementation styles can be compared:

- the current staged structure update from `AddCommGroup` to `AddGroupWithOne`;
- an implementation using a shared cast helper;
- a direct `CommRing` construction that removes the intermediate instance.

Useful evaluation criteria include definitional transparency, stability of instance search, cast simplification behavior, simplicity of the downstream `goldenCommRing`, resilience under representation changes, and ease of auditing the source.

Although small, this declaration is a good Comparator challenge for studying staged algebra-hierarchy construction versus one-shot structure construction in Lean.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`. There, 0145 `goldenAddCommGroup` is followed immediately by this `goldenAddGroupWithOne`, which is in turn followed by `goldenCommRing`.

The concrete PDF page or section corresponding to this small algebra-interface instance was not directly identified in this pass, so no PDF location is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
instance goldenCommRing : CommRing GoldenInt := by
  refine
    { goldenAddGroupWithOne with
      npow := fun n x => goldenPow x n
      npow_zero := by intro x; rfl
      npow_succ := by
        intro n x
        change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
        rfl
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
    simp <;> ring
```

By 0145 the commutative additive group is complete, and 0146 adds the standard natural/integer cast layer through `AddGroupWithOne`. The next declaration, 0147, proves the multiplicative laws involving `goldenMul` and `goldenPow` and finally registers `GoldenInt` as a complete `CommRing` in Mathlib's ring-theoretic API.
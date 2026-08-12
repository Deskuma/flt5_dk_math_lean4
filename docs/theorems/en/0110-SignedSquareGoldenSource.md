# 0110 — `SignedSquareGoldenSource`

## Lean type

```lean
/-- Provenance of the square-golden coordinates in the two signed orientations. -/
inductive SignedSquareGoldenSource
    (u v w : ℕ) (M N delta : ℤ) : Prop
  | difference :
      M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = (w : ℤ) * (v : ℤ) →
      delta = (w : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
  | sum :
      M = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = -((u : ℤ) * (v : ℤ)) →
      delta = (u : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
```

## Mathematical statement

`SignedSquareGoldenSource u v w M N delta` is a proposition-valued provenance type recording from which of the two signed square-golden orientations the integer coordinates $(M,N,\delta)$ arise.

The `difference` constructor records

$$
M=w^2+v^2,\qquad N=wv,\qquad \delta=w^2-v^2.
$$

The `sum` constructor records

$$
M=u^2+v^2,\qquad N=-uv,\qquad \delta=u^2-v^2.
$$

Thus this declaration is not itself a theorem proving a new number-theoretic identity. Instead, it stores provenance at the type level so downstream proofs can handle the difference and sum orientations through one interface.

## Role in the whole proof

The preceding 0108 `sumGN5_eq_goldenNorm_signed` and 0109 `signed_endpoint_square_discriminant` established that, in the sum orientation, choosing the negative cross-coordinate $N=-uv$ makes both the golden norm and the square discriminant natural integer identities.

On the existing square-golden difference side, the positive product $N=wv$ is used. The following `SignedSquareGoldenExceptionalPacket` stores the two branches through the same coordinate fields

$$
(M,N,\delta)
$$

and delegates only their origin to `source : SignedSquareGoldenSource ...`. This declaration is therefore the provenance layer that prevents the packet itself from hard-coding branch-specific coordinate formulas.

In particular, a downstream proof can split `source` by cases and recover the concrete formulas for $M,N,\delta$ in the difference or sum branch. The design separates common invariants from the distinction in origin.

## Direct dependencies

The direct dependencies are very small:

- `ℕ`, `ℤ`
- coercions from natural numbers to integers such as `(u : ℤ)`
- integer addition, subtraction, multiplication, and powers
- Lean's `inductive` declaration mechanism

The type does not directly refer to 0108 or 0109. Architecturally, however, those results justify that the coordinates selected by the `sum` constructor,

$$
M=u^2+v^2,\qquad N=-uv,\qquad \delta=u^2-v^2,
$$

are compatible with the golden norm and square discriminant used downstream.

## Proof flow

Because this is an `inductive` declaration, there is no theorem proof script. Instead, its two constructors specify the two ways the proposition can be inhabited.

1. `difference` accepts three coordinate equalities and constructs difference provenance.
2. `sum` accepts three coordinate equalities and constructs sum provenance.
3. A consumer can use `cases hSource` or `rcases hSource` to split on the two orientations and then use the corresponding equalities.

It is naturally viewed as a proposition-valued tagged union.

## Lean-specific processing

A notable design choice is that the constructors do not themselves compute $M,N,\delta$. They take externally supplied coordinates and proofs that those coordinates equal the required formulas.

For example, `difference` receives

```lean
M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2
```

as an assumption. This allows a downstream packet to keep $M,N,\delta$ as independent fields while proving their provenance separately.

The coercions from the natural parameters $u,v,w$ to integer coordinates are explicit in the constructor types. Consequently, consumers work with signed differences such as $u^2-v^2$ and $w^2-v^2$ directly, without the truncation behavior of `Nat.sub`.

## Redundancy and overlap

The `difference` and `sum` constructors are structurally very similar. Both have

$$
M=A^2+v^2,\qquad \delta=A^2-v^2,
$$

and differ only in whether the first base is $w$ or $u$, and whether

$$
N=Av
$$

or

$$
N=-Av.
$$

At the data-model level, this suggests a possible generalization using an orientation sign and a selected base. However, the current two-constructor representation makes the two number-theoretic origins explicit at the type level, so the duplication can also be read as an intentional readability cost.

The declaration is conceptually close to existing types such as `SignedBranchAOrientation` that also represent two signed orientations. The Lean source does not directly prove an exact equivalence here, so any unification remains an optimization hypothesis rather than an established fact.

## Optimization candidates

There are three natural candidates.

First, factor the common coordinate data into a helper structure, conceptually such as

```lean
structure SquareGoldenCoordinates where
  M : ℤ
  N : ℤ
  delta : ℤ
```

and keep only provenance inductive. This could improve coordinate-field reuse across packets.

Second, use an explicit orientation tag and a single constructor. Because the sign and base selection are dependent on the tag, this is not guaranteed to produce shorter Lean code than the current two-constructor design.

Third, compare the current equality direction with an API that generates coordinates via helper definitions or `let` bindings. The current orientation `M = ...` is convenient for `rw` and `subst`, so any change should be evaluated against downstream proof scripts rather than by surface brevity alone.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but this declaration alone uses no advanced Mathlib theorem or tactic.

It requires only the basic support for naturals, integers, coercions, ring operations, powers, and inductive declarations. Therefore `import Mathlib` is much broader than necessary for this declaration in isolation.

The actual file `SignedSquareGoldenExceptional.lean`, however, also contains preceding theorems using `ring`, `push_cast`, `Nat.cast_sub`, and downstream packet construction. Since no Lean build was run in this pass, the exact minimal file-level import set is left as a candidate rather than asserted.

## Comparator challenge suitability

It is well suited.

Useful comparison targets include:

- the explicit two-constructor provenance type
- a single-constructor type with a sign/orientation tag
- a design separating a coordinate structure from provenance
- storing `M,N,delta` externally versus computing them from the source

Evaluation criteria could include the construction code for `SignedSquareGoldenExceptionalPacket`, the number of rewrites after `cases`, coercion overhead, and how clearly theorem and field names expose the mathematics.

This is more naturally a proof-oriented data-modeling Comparator challenge than a proof-search challenge.

## Relation to existing materials

The formal source of truth is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The exact page or section locations in the existing Japanese and English PDFs could not be established through the GitHub connector in this pass, so no PDF location is supplied by inference.

## Next declaration to read

The next declaration in dependency order is

```lean
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  source : SignedSquareGoldenSource u v w M N delta
  golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
  tenth_boundary : M - 2 * N = (5 : ℤ) ^ 8 * (powerSplit.a : ℤ) ^ 10
  square_discriminant : M ^ 2 - 4 * N ^ 2 = delta ^ 2
  discriminant_five_eq :
    (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (powerSplit.b : ℤ) ^ 5
```

Where 0110 records which orientation generated the coordinates, the next declaration packages that provenance together with four square-golden invariants. At that point the main data structure of the signed exceptional route is assembled.
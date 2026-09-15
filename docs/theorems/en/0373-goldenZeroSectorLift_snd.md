# 0373 `goldenZeroSectorLift_snd`

## Declaration kind

`theorem`

## Lean code

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

## Lean type

```lean
goldenZeroSectorLift_snd :
  (x : GoldenInt) → (goldenZeroSectorLift x).snd = x.snd ^ 2
```

For every `x : GoldenInt`, the theorem states that the second coordinate of 0372 `goldenZeroSectorLift` is the square of the original second coordinate.

Writing mathematically $x=(r,s)$ and

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr),
$$

this theorem is simply

$$
\operatorname{snd}(T(r,s))=s^2.
$$

## Mathematical meaning

This is the projection lemma that exposes the second component of the quadratic re-entry map defined in 0372:

$$
T(r,s)=\bigl(r^2+rs+s^2,s^2\bigr).
$$

Mathematically, the statement is just an unfolding of the definition and proves no new arithmetic fact. In the zero-sector descent, however, the fact that the second coordinate is a square is important. Later proofs use it as a stable rewrite API to transfer divisibility of the original coordinate $s$ to

$$
5\mid s^2.
$$

## Role in the whole proof

`SignedGoldenZeroSectorDescent.lean` re-enters the quartic zero-sector condition into a golden-integer norm/fifth-power problem and then constructs a strict descent.

0372 `goldenZeroSectorLift` defines the re-entry map itself. The present theorem fixes its “visible coordinate” as a public logical fact.

It is used explicitly later in `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`:

```lean
have hFiveAlpha : (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd := by
  rw [goldenZeroSectorLift_snd]
  ...
```

From the packet field `snd_eq`, one has

$$
p.base.snd=\pm 5t^5.
$$

After squaring, the proof obtains divisibility by 5 of the lift's second coordinate. That divisibility is then passed to the elimination of nonzero unit sectors.

Thus the relevant flow is

$$
p.base.snd=\pm5t^5
\Longrightarrow
5\mid p.base.snd^2
\Longrightarrow
5\mid \operatorname{snd}(T(p.base)).
$$

The present theorem supplies the last identification.

## Direct dependencies

### `goldenZeroSectorLift`

This is the only direct FLT5-specific dependency.

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

Its second component is literally `x.snd ^ 2`, so the theorem holds by definitional equality.

### `GoldenInt.snd`

This is the second-coordinate projection of `GoldenInt`. After unfolding the definition, Lean reduces the projection of the constructor to its second argument.

### `rfl`

This is not an auxiliary lemma but Lean's reflexivity proof term. Once the left-hand side is reduced by definitional unfolding and projection computation, it is definitionally identical to the right-hand side.

## Proof flow

The entire proof is one token:

```lean
:= rfl
```

Conceptually, Lean reduces

```lean
(goldenZeroSectorLift x).snd
```

by unfolding `goldenZeroSectorLift` to

```lean
(⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2,
   x.snd ^ 2⟩ : GoldenInt).snd
```

and then applies the structure projection computation rule, obtaining

```lean
x.snd ^ 2
```

so the goal becomes

```lean
x.snd ^ 2 = x.snd ^ 2
```

and closes by `rfl`.

## Lean-specific processing

### Definitional equality

The central Lean feature is definitional equality rather than proposition-level algebra.

Later code may use `rw [goldenZeroSectorLift_snd]`, while the proof of the theorem itself needs neither `unfold` nor an algebra tactic because kernel reduction is sufficient.

### Projection reduction

Applying `.snd` to a value built by the corresponding constructor computes directly to the second constructor argument. This is a computation rule, not a rewrite theorem invoked by the proof.

### A named rewrite lemma as API

In principle, later code could repeatedly write something such as

```lean
simp [goldenZeroSectorLift]
```

and obtain the same result. Keeping a named theorem allows downstream proofs to rewrite only the second coordinate without exposing the implementation of the first coordinate.

That is a useful proof-maintenance abstraction boundary.

## Redundancy and duplication

Mathematically this theorem duplicates information already present in the definition from 0372.

The duplication is nevertheless intentional API duplication: downstream proofs can use the second-coordinate equation without unfolding the entire transformation.

There is no tactic-level redundancy to remove from the current one-line proof.

## Optimization candidates

### 1. A `[simp]` attribute

One possible change would be

```lean
@[simp] theorem goldenZeroSectorLift_snd ... := rfl
```

so that `simp` automatically reduces the second coordinate of the lift to `x.snd ^ 2`.

The current downstream proof deliberately writes `rw [goldenZeroSectorLift_snd]`, which is already explicit and readable. Whether this theorem belongs in the global simp set should therefore be decided from repository-wide usage; this remains only a candidate.

### 2. Removing the theorem and unfolding the definition

This is possible but not especially attractive. It would make downstream proofs depend directly on the coordinate implementation of `goldenZeroSectorLift` and weaken the abstraction boundary.

### 3. A symmetric first-coordinate projection lemma

If the first coordinate is frequently needed in isolation, a `goldenZeroSectorLift_fst` lemma could be added. The checked source instead immediately packages the first-coordinate algebra into the norm identity, so there is no evidence that a mechanically symmetric API is currently necessary.

## Required Mathlib imports and import optimization

The standalone source currently uses

```lean
import Mathlib
```

for the complete generated development.

This theorem by itself needs only

- `GoldenInt`,
- `goldenZeroSectorLift`,
- structure projection,
- natural-number exponentiation for the square,
- equality and `rfl`.

It uses no additional tactic. Therefore `import Mathlib` is far broader than what this single declaration needs.

The actual `SignedGoldenZeroSectorDescent.lean` module, however, uses many later facilities such as `ring`, `norm_num`, `omega`, divisibility, and coprimality. The precise minimal Mathlib import should therefore be determined at module granularity and verified by Lean builds. No Lean build is performed in this documentation task, so the exact minimal import remains unverified.

## Comparator challenge feasibility

**Yes, but by itself it is an extremely small challenge.**

For example:

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩

example (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := by
  ?_
```

The intended solution is `rfl`.

This can test whether a Comparator candidate recognizes definitional equality instead of starting unnecessary tactic search.

A more informative challenge would combine 0372–0374:

1. define the lift,
2. prove the `snd` projection by `rfl`,
3. prove the norm identity by `ring`.

That would test structure construction, definitional equality, unfolding, and polynomial normalization in one compact unit.

## Technical meaning

This theorem promotes the design fact “the visible coordinate is a square” from the implementation of 0372 into a logical API usable by later proofs.

The zero-sector descent needs arithmetic information not only about the norm of the lift but also about its second coordinate. In particular, transporting

$$
s=\pm5t^5
$$

to the lift gives

$$
\operatorname{snd}(T(r,s))=s^2,
$$

so divisibility by 5 is automatically retained.

This visible-coordinate divisibility combines with the next theorem's norm re-entry

$$
\operatorname{Norm}(T(r,s))=H(r,s)
$$

to make the unit-sector classification reusable inside the zero-sector descent.

## Next declaration to read

The next declaration is **`goldenZeroSectorLift_norm`**.

Its declaration kind is `theorem`.

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

Where 0373 fixes the second coordinate of the lift, 0374 identifies its norm with the quartic factor occurring in fifth-power coordinates. This is the identity that makes the zero-sector algebraic re-entry substantive.

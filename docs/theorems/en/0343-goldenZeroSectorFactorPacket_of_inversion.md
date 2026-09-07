# 0343 — `goldenZeroSectorFactorPacket_of_inversion`

## Declaration kind

This declaration is a **`noncomputable def`**.

```lean
/-- Chosen exact factor packet attached to an inversion packet. -/
noncomputable def goldenZeroSectorFactorPacket_of_inversion
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

## Lean type

Its type is

```lean
GoldenZeroSectorInversionPacket → GoldenZeroSectorFactorPacket
```

More concretely, it takes

```lean
p : GoldenZeroSectorInversionPacket
```

and returns one

```lean
GoldenZeroSectorFactorPacket
```

value.

`GoldenZeroSectorFactorPacket` is the dependent structure defined immediately before:

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

Thus the `factors` field of the returned packet is tied at the type level to the `inversion` field of that same packet.

Because this definition sets

```lean
inversion := p
```

the expected type of the second field becomes definitionally

```lean
GoldenZeroSectorFactorData p
```

The previous theorem 0342, `nonempty_factorData p`, proves that this type is inhabited, and `Classical.choice` selects one witness.

## Mathematical meaning

By 0342 it has already been proved that every inversion packet `p` admits at least one exact factor datum:

$$
\operatorname{Nonempty}(\operatorname{GoldenZeroSectorFactorData}(p)).
$$

Declaration 0343 turns that existence result into a concrete chosen factor datum and packages it together with the original inversion packet.

Conceptually,

$$
p
\longmapsto
\bigl(p,\;\operatorname{choose}(\text{factor data for }p)\bigr).
$$

No new number-theoretic assertion is proved here. The operation is a passage from an already established existence statement to a concrete structured object that later APIs can consume directly.

The definition itself does not specify which of the three branches

```lean
GoldenZeroSectorFactorData.odd
GoldenZeroSectorFactorData.evenLeftLow
GoldenZeroSectorFactorData.evenRightLow
```

is chosen. The previous existence theorem guarantees the appropriate branch according to parity, and `Classical.choice` extracts one inhabitant from that proof.

## Role in the overall proof

This definition sits at the **boundary between the existence-proof layer and the packet API layer** of the zero-sector factorization.

The preceding development has the shape

$$
\text{inversion packet}
\to
\text{odd/even analysis}
\to
\operatorname{Nonempty}(\text{factor data}).
$$

Declaration 0343 continues with

$$
\operatorname{Nonempty}(\text{factor data})
\to
\text{chosen factor data}
\to
\text{complete factor packet}.
$$

Once this packet exists, later theorems do not need to reopen `Nonempty` or reanalyse the parity of `c`; they may simply consume

```lean
packet : GoldenZeroSectorFactorPacket
```

as a proof-carrying object.

The next theorem, 0344 `nonempty_goldenZeroSectorFactorPacket`, starts from a raw zero-sector candidate, builds its inversion packet, applies this definition, and obtains the existence of a factor packet. Shortly afterward, `GoldenZeroSectorFactorExclusion` is defined as

```lean
GoldenZeroSectorFactorPacket → False
```

so factor packets become the direct input to the exclusion layer.

Therefore 0343 is the connection point that seals the long internal factorization proof into one witness-carrying object for downstream descent and exclusion arguments.

## Direct dependencies

The direct dependencies are:

- `GoldenZeroSectorInversionPacket`
- `GoldenZeroSectorFactorPacket`
- `GoldenZeroSectorFactorData`
- 0342 `nonempty_factorData`
- `Classical.choice`

In particular, all direct number-theoretic work is hidden behind 0342.

The theorem 0342 itself depended on

- 0338 `nonempty_odd_factorData`
- 0341 `nonempty_even_factorData`
- `Nat.even_or_odd`

so 0343 can consume only the existence result without knowing any details of the odd/even factorization.

## Construction flow

The construction consists of filling two fields of a structure literal.

1. Receive `p : GoldenZeroSectorInversionPacket`.
2. Store the same `p` in `GoldenZeroSectorFactorPacket.inversion`.
3. Use 0342 `nonempty_factorData p` to obtain

   ```lean
   Nonempty (GoldenZeroSectorFactorData p)
   ```

4. Apply `Classical.choice` to select one witness of

   ```lean
   GoldenZeroSectorFactorData p
   ```

5. Store that witness in the `factors` field.

The whole construction is compressed in Lean to

```lean
where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

## Lean-specific processing

### `noncomputable def`

The declaration is marked `noncomputable` because it uses `Classical.choice`.

`nonempty_factorData p` returns only

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

rather than a computational function that determines a branch and returns explicit data. Classical choice is therefore used to extract an inhabitant from proposition-level existence.

Consequently, this definition does not provide an executable branch-selection algorithm.

### Dependent structure field

The second field of `GoldenZeroSectorFactorPacket` is

```lean
factors : GoldenZeroSectorFactorData inversion
```

and depends on the first field `inversion`.

Once the structure literal specifies

```lean
inversion := p
```

Lean automatically specializes the expected type of `factors` to

```lean
GoldenZeroSectorFactorData p
```

so no cast or explicit equality transport is required.

### `Classical.choice` and `Nonempty`

Lean's `Classical.choice` turns `Nonempty α` into `α`. Here

```lean
α := GoldenZeroSectorFactorData p
```

The choice of `Nonempty (GoldenZeroSectorFactorData p)` as the output of 0342 is therefore used directly by this definition.

## Redundancy and duplication

There is essentially no redundancy in this declaration.

```lean
inversion := p
factors := Classical.choice (nonempty_factorData p)
```

fills exactly the two required fields in the shortest clear form.

One could introduce a local binding such as

```lean
let factors := Classical.choice (nonempty_factorData p)
```

before constructing the structure, but that would only make the code longer.

A positional constructor form such as `⟨p, Classical.choice ...⟩` should also be possible, but the named-field form used here is clearer because it makes the dependent relationship between `inversion` and `factors` visible.

## Optimization candidates

There is almost no local code-level optimization to perform.

At a broader design level, one could make 0338 / 0341 / 0342 return `GoldenZeroSectorFactorData p` directly, whether computationally or noncomputably, and thereby remove the `Classical.choice` call from 0343.

However, the current architecture deliberately separates

1. the proof that suitable mathematical data exists, expressed as proposition-valued `Nonempty`, and
2. the layer that chooses a concrete object by classical choice.

That separation has the advantage of localizing noncomputability to a clear boundary, so merging the layers should not automatically be considered an optimization.

Another possibility would be to propagate only `Nonempty GoldenZeroSectorFactorPacket` if downstream code needed existence alone. The later `GoldenZeroSectorFactorExclusion`, however, takes an actual packet as input, so the chosen-packet API has a direct purpose.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

For declaration 0343 itself, the principal Mathlib-level ingredients are

- `Nonempty`
- `Classical.choice`
- the classical infrastructure needed for a `noncomputable` choice

The project-specific dependencies `GoldenZeroSectorInversionPacket`, `GoldenZeroSectorFactorPacket`, and `nonempty_factorData` are earlier declarations of `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean`.

The ordered source list of the standalone artifact also places `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` after `SignedGoldenZeroSectorInversion.lean`.

The isolated definition could probably be supported by a much smaller Mathlib import set, but no Lean build is performed in this documentation run, so no specific fine-grained import is asserted to be sufficient.

If import optimization is pursued, it is more appropriate to audit `SignedGoldenZeroSectorFactorization.lean` as a whole rather than optimize this two-line declaration in isolation.

## Comparator challenge suitability

**Yes. It is well suited as a small challenge about dependent structures and classical choice.**

For example:

```lean
noncomputable def challenge
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket := by
  -- fill here
```

If the solver is given

```lean
nonempty_factorData p : Nonempty (GoldenZeroSectorFactorData p)
```

then the task tests whether they can

- understand the dependent field of `GoldenZeroSectorFactorPacket`,
- extract a witness from `Nonempty` with `Classical.choice`, and
- place factor data for exactly the same `p` into the packet.

The mathematical difficulty is low, but it is a useful Lean challenge about the boundary between existence proofs and concrete data.

A harder version could hide `nonempty_factorData` and require reconstructing the parity split of 0342, but that would be a combined 0342–0343 exercise rather than a challenge focused on 0343 alone.

## Next declaration to read

The next declaration is

```lean
/-- Every raw zero-sector candidate produces one of the three exact factor branches. -/
theorem nonempty_goldenZeroSectorFactorPacket
    (p : GoldenZeroSectorCandidate) :
    Nonempty GoldenZeroSectorFactorPacket :=
  ⟨goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket p)⟩
```

Its declaration kind is **`theorem`**.

Now that 0343 can construct a chosen factor packet from an inversion packet, 0344 first transforms a raw `GoldenZeroSectorCandidate` by

```lean
goldenZeroSectorInversionPacket p
```

then applies 0343 and wraps the result in `Nonempty`.

Thus the next stage exposes the public factorization-existence pipeline

$$
\text{raw candidate}
\to
\text{inversion packet}
\to
\text{chosen factor packet}
\to
\operatorname{Nonempty}(\text{factor packet}).
$$

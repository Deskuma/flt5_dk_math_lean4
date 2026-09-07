# 0342 — `nonempty_factorData`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc
```

## Lean type

Its type is

```lean
(p : GoldenZeroSectorInversionPacket) →
Nonempty (GoldenZeroSectorFactorData p)
```

`GoldenZeroSectorFactorData p` is a dependent inductive type indexed by the inversion packet `p`. This theorem proves, without any additional parity assumption, that this type always has an inhabitant.

The fact that the result is not a factor datum itself but rather `Nonempty (GoldenZeroSectorFactorData p)` is important. At this stage the proof establishes existence without computationally choosing which branch datum to use. The immediately following `goldenZeroSectorFactorPacket_of_inversion` performs that choice using `Classical.choice`.

## Mathematical meaning

For every `GoldenZeroSectorInversionPacket`, the natural number `p.source.c` is either even or odd:

$$
\operatorname{Even}(c)\lor\operatorname{Odd}(c).
$$

Two branch-construction theorems have already been established.

In the even case, 0341 `nonempty_even_factorData` gives

$$
\operatorname{Nonempty}(\operatorname{GoldenZeroSectorFactorData}(p)).
$$

In the odd case, 0338 `nonempty_odd_factorData` gives the same conclusion.

Therefore one exhaustive parity split yields exact factor-data existence for every inversion packet.

## Role in the full proof

This theorem is the **branch join point** of zero-sector factorization.

0338 constructs the odd-`c` branch, while 0341 constructs the even-`c` branch. Internally, those two theorems contain the substantial arithmetic work: two-adic analysis, coprimality, fifth-power splitting, and factor ownership. Declaration 0342 compresses those completed branch proofs into a single unconditional existence statement.

Structurally, it has the form

$$
\text{odd construction}
\quad\cup\quad
\text{even construction}
\longrightarrow
\text{unconditional factor-data existence}.
$$

There is almost no new number theory in 0342 itself. It is a proof-control layer that connects the two completed arithmetic branches by parity exhaustion. Its architectural role is nevertheless important: downstream code no longer needs to reconsider the parity of `p.source.c`; it can use only the fact that `GoldenZeroSectorFactorData p` is inhabited.

## Direct dependencies

The direct dependencies are very small:

- `GoldenZeroSectorInversionPacket`
- `GoldenZeroSectorFactorData`
- `nonempty_even_factorData`
- `nonempty_odd_factorData`
- `Nat.even_or_odd`

All mathematically heavy dependencies are encapsulated inside 0338 and 0341.

In particular, 0341 constructs either `.evenLeftLow` or `.evenRightLow`, while 0338 constructs `.odd`. Thus 0342 guarantees that one of the three constructors

```lean
GoldenZeroSectorFactorData.odd
GoldenZeroSectorFactorData.evenLeftLow
GoldenZeroSectorFactorData.evenRightLow
```

exists for the fixed inversion packet `p`, according to the parity of `c`.

## Proof flow

The proof consists of four simple steps.

1. Apply `Nat.even_or_odd p.source.c`.
2. In the branch `hc : Even p.source.c`, return `nonempty_even_factorData p hc`.
3. In the branch `hc : Odd p.source.c`, return `nonempty_odd_factorData p hc`.
4. Both branches have the same codomain, `Nonempty (GoldenZeroSectorFactorData p)`, so they join immediately.

The Lean line

```lean
rcases Nat.even_or_odd p.source.c with hc | hc
```

is a direct formalization of the elementary exhaustive statement that every natural number is even or odd.

## Lean-specific processing

### Existence through `Nonempty`

In ordinary mathematical prose one would simply say that factor data exists. Lean stores exactly that information as

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

so that a later declaration may obtain an inhabitant by classical choice without exposing the internal fields at this point.

### Matching dependent codomains

Both parity branches return data indexed by the same packet `p`:

```lean
GoldenZeroSectorFactorData p
```

Only the proof of the parity of `p.source.c` is split. The packet itself is not rewritten or replaced, so the return types of the two branches are definitionally identical. No cast, transport, or `Eq.ndrec` is required.

### `private theorem`

`nonempty_factorData` is marked `private` because it is an internal bridge in this source module. Its main purpose is to supply the existence proof consumed immediately by `goldenZeroSectorFactorPacket_of_inversion`; it does not need to become part of the external API.

## Redundancy and duplication

There is essentially no meaningful redundancy in this theorem.

The two branches

```lean
· exact nonempty_even_factorData p hc
· exact nonempty_odd_factorData p hc
```

are syntactically symmetric, but they are also the clearest presentation of the exhaustive parity split. Compressing them further would save almost nothing and would likely reduce readability.

The large constructions from 0338 and 0341 are not duplicated here; keeping them in helper theorems is precisely the right factoring of the proof.

## Optimization candidates

The current implementation is already close to minimal. A stylistic reformulation into a denser term expression is possible, but it would not materially simplify the proof.

A broader API redesign could make 0338 and 0341 return `GoldenZeroSectorFactorData p` directly rather than `Nonempty (...)`. However, the current design deliberately postpones witness selection to `Classical.choice` in the next declaration. Changing that boundary would alter the computational/noncomputational structure of the development, so it should not be treated as a routine optimization.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

For this theorem itself, the direct Mathlib-level ingredients are mainly `Nat.even_or_odd` and `Nonempty`. In practice, however, it also depends on the earlier definitions and helper theorems for `GoldenZeroSectorInversionPacket`, `GoldenZeroSectorFactorData`, `nonempty_even_factorData`, and `nonempty_odd_factorData`.

In the ordered source manifest, this declaration belongs to `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean`. The standalone artifact consolidates everything under the umbrella import `Mathlib`. Because no Lean build is performed in this documentation task, the exact minimal fine-grained Mathlib import set for the original source module has not been verified and is therefore not asserted here.

If import optimization is desired, the proper target is the entire `SignedGoldenZeroSectorFactorization.lean` module rather than this four-line theorem in isolation.

## Comparator challenge suitability

**Yes, but the difficulty is low.**

A natural challenge is to provide only the target

```lean
example (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  -- fill here
```

while making 0338 and 0341 available. The expected solution is almost forced: discover `Nat.even_or_odd` and dispatch to the two branch constructors.

This makes a good small proof-orchestration challenge, testing whether the solver can find and combine the correct dependency theorems. It is not a strong number-theory challenge by itself.

A harder Comparator problem would have to forbid direct use of 0338 and 0341 and require rebuilding the branch constructions. That would no longer be a challenge about 0342 alone, but about the entire zero-sector factorization stage.

## Next declaration to read

The next declaration is

```lean
noncomputable def goldenZeroSectorFactorPacket_of_inversion
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

Its declaration kind is **`noncomputable def`**.

It uses the `Nonempty (GoldenZeroSectorFactorData p)` proved in 0342, chooses one concrete factor datum with `Classical.choice`, and packages it together with the same inversion packet into

```lean
GoldenZeroSectorFactorPacket
```

Thus 0342 provides unconditional existence, while the next declaration performs witness selection and packet construction.
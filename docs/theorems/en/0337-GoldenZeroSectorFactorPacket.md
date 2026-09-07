# 0337 — `GoldenZeroSectorFactorPacket`

## Declaration kind

This declaration is not a theorem but a **`structure`**.

It packages a `GoldenZeroSectorInversionPacket` together with the exact factor certificate `GoldenZeroSectorFactorData inversion` that depends on that specific inversion packet, forming one proof-carrying packet.

```lean
/-- Complete zero-sector factor packet. -/
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

## Lean type

The declaration itself has type

```lean
GoldenZeroSectorFactorPacket : Type
```

Conceptually, making its generated constructor explicit gives

```lean
GoldenZeroSectorFactorPacket.mk :
  (inversion : GoldenZeroSectorInversionPacket) →
  GoldenZeroSectorFactorData inversion →
  GoldenZeroSectorFactorPacket
```

The key point is that the second field

```lean
factors : GoldenZeroSectorFactorData inversion
```

refers in its own type to the value of the first field `inversion`. Thus `factors` is not arbitrary factor data: it must have been built for the very same `inversion` stored in this packet.

## Mathematical meaning

This structure does not prove a new equation or divisibility statement by itself. Its mathematical role is to preserve, as a single object whose consistency cannot be broken, two stages of the zero-sector certificate:

1. the inverted and normalized zero-sector information, and
2. an exact fifth-power factorization branch for that information.

Writing the stored inversion data as $p$, the second component is necessarily

$$
\operatorname{GoldenZeroSectorFactorData}(p).
$$

As seen in declaration 0334, `GoldenZeroSectorFactorData p` carries branch-specific exact factorization data. For example, the odd branch contains

$$
A_0=2e^5,
\qquad
B_0=2f^5,
$$

and

$$
e^5+4d^5=f^5.
$$

The present structure fixes, through type dependency, exactly which inversion packet that certificate belongs to.

## Role in the full FLT5 proof

The zero-sector development cannot merely show that “some factorization exists.” It must construct a factorization for the concrete `c,d,A0,B0,Q` data obtained in the preceding `GoldenZeroSectorInversionPacket`, and then pass that matched data into the descent phase.

If inversion data and factor data could be stored independently, in a shape morally like

```lean
inversion : GoldenZeroSectorInversionPacket
factors : GoldenZeroSectorFactorData someOtherPacket
```

then proof objects originating from two different zero-sector packets could accidentally be combined.

The field

```lean
factors : GoldenZeroSectorFactorData inversion
```

rules out that mismatch during type checking.

Accordingly, this structure is a **dependent-type consistency boundary** between the zero-sector inversion phase and the exact factorization phase. Once downstream descent machinery receives a `GoldenZeroSectorFactorPacket`, it no longer needs a separate proof that the inversion data and the factor certificate have the same provenance.

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

This is the type of the first field

```lean
inversion : GoldenZeroSectorInversionPacket
```

and is the certificate carrying the zero-sector source data together with the identities, coprimality facts, and non-divisibility information obtained by inversion and normalization.

### `GoldenZeroSectorFactorData`

Declaration 0334, a dependent `inductive` type.

Its shape is conceptually

```lean
GoldenZeroSectorFactorData :
  GoldenZeroSectorInversionPacket → Type
```

and its constructors `odd`, `evenLeftLow`, and `evenRightLow` carry branch-specific exact factorization data.

The present second field supplies the first field itself as the index of this type.

## Construction flow

There is no proof script in this declaration. The structure declaration itself causes Lean to generate a constructor and projections.

### 1. Receive an inversion certificate

```lean
inversion : GoldenZeroSectorInversionPacket
```

This first fixes which zero-sector inversion packet is being handled.

### 2. Require factor data for that exact inversion

```lean
factors : GoldenZeroSectorFactorData inversion
```

Once the first field is fixed, only a factor certificate indexed by that value is accepted.

### 3. Pass both forward as one packet

The constructor can conceptually be used in the form

```lean
⟨p, data⟩
```

but Lean checks that `data` has precisely the type

```lean
GoldenZeroSectorFactorData p
```

before the packet can be constructed.

## Lean-specific processing

### Dependent field

In many ordinary structures the field types are independent. Here, however, the type of the later field depends on the value of the earlier field:

```lean
factors : GoldenZeroSectorFactorData inversion
```

This is a standard Lean dependent-structure pattern.

### Automatically generated projections

Lean provides projections conceptually of the form

```lean
GoldenZeroSectorFactorPacket.inversion :
  GoldenZeroSectorFactorPacket → GoldenZeroSectorInversionPacket
```

and, for each packet `p`,

```lean
p.factors : GoldenZeroSectorFactorData p.inversion
```

The dependency is preserved in the return type of the second projection.

### Binding proof-carrying data by provenance

`GoldenZeroSectorFactorData` already contains many proof terms. The present structure does not prove those facts again; instead it binds already-certified data to its source inversion packet at the type level.

This is not a logical implication between propositions but an **invariant enforced by data design**.

## Redundancy and duplication

The declaration has only two fields, so there is essentially no code-level redundancy.

Because `GoldenZeroSectorFactorData` is already indexed by `p : GoldenZeroSectorInversionPacket`, one could ask whether the inversion packet should instead be recovered from factor data. An index, however, is not simply an ordinary runtime record projection, and downstream code benefits from carrying both the inversion and its factor data as one named object.

At the type-theoretic level, this wrapper could also be represented by the sigma type

```lean
Σ p : GoldenZeroSectorInversionPacket, GoldenZeroSectorFactorData p
```

which contains equivalent information. The dedicated structure nevertheless gives meaningful field names `inversion` and `factors`, clearer projections, and a domain-specific type name for later APIs.

## Optimization candidates

### Collapse to a sigma type

If minimizing the number of named declarations were the only concern, the same information could be represented as

```lean
Σ p : GoldenZeroSectorInversionPacket, GoldenZeroSectorFactorData p
```

and the dedicated structure omitted.

For a proof development, however, named projections and a domain-specific packet type are valuable, so the current structure is a reasonable API choice.

### Constructor helper

If later packet construction repeatedly becomes elaboration-heavy, a helper such as

```lean
def GoldenZeroSectorFactorPacket.mkFrom ...
```

could provide a more specialized construction interface. The current constructor has only two arguments, and the repository evidence inspected here does not show a present need for another abstraction.

### Converting it to `Prop` would be inappropriate

This packet is a data container from which downstream code can recover a branch certificate and perform case analysis. Keeping it in `Type` preserves that information, whereas collapsing it to a mere existence proposition would hide useful data.

## Required Mathlib imports and import optimization

The standalone canonical source uses

```lean
import Mathlib
```

for the generated file as a whole.

The present structure itself does not directly invoke arithmetic theorems or Mathlib tactics once

```lean
GoldenZeroSectorInversionPacket
GoldenZeroSectorFactorData
```

are already available. Its direct language-level requirements are Lean's structure and dependent-type machinery plus those preceding local declarations.

In the original modular layout this declaration occurs in the `SignedGoldenZeroSectorFactorization.lean` stage and therefore needs whatever earlier project modules make those two types available. The exact minimal import list for that module cannot be established from this declaration alone.

Thus the umbrella `import Mathlib` is potentially much broader than this one declaration requires, but because no Lean build is performed in this task, no concrete reduced import list is claimed as verified.

## Comparator challenge suitability

**Suitable, but low difficulty in isolation.**

A small hole-filling task could present

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : ?m
```

and ask the solver to fill `?m` with

```lean
GoldenZeroSectorFactorData inversion
```

which tests understanding of dependent fields.

There is no proof search or arithmetic, however, so it is too easy as an ordinary theorem comparator. A stronger challenge would pair declaration 0334 with this structure and ask the solver to design an API in which factor data from one inversion packet cannot be mixed with another.

The key grading criterion would be whether the second component's type genuinely depends on the first component's value rather than merely storing the two values in an unrelated pair.

## Next declaration to read

The next declaration is

```lean
private theorem nonempty_odd_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
```

Its kind is **`private theorem`**.

It is the first branch-specific existence theorem that actually constructs the second field required by the packet defined here. Under the assumption that `c` is odd, it proves

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

and therefore begins the construction phase showing that the exact factor-certificate type introduced in 0334 is genuinely inhabited for a zero-sector inversion packet, rather than merely being a type-level specification.
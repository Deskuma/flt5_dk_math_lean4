# 0335 — `GoldenZeroSectorFactorData.branch`

## Declaration kind

This declaration is not a theorem but a **`def`**.

It defines a projection that forgets the heavy proof data stored in `GoldenZeroSectorFactorData p` and retains only the corresponding lightweight branch label `GoldenZeroSectorFactorBranch`.

```lean
/-- Branch label of an exact factor datum. -/
def GoldenZeroSectorFactorData.branch
    {p : GoldenZeroSectorInversionPacket} :
    GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
  | .odd .. => .odd
  | .evenLeftLow .. => .evenLeftLow
  | .evenRightLow .. => .evenRightLow
```

## Lean type

The declaration has type

```lean
GoldenZeroSectorFactorData.branch :
  {p : GoldenZeroSectorInversionPacket} →
  GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
```

After fixing the implicit argument

```lean
{p : GoldenZeroSectorInversionPacket}
```

it is an ordinary function

```lean
GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
```

The input `GoldenZeroSectorFactorData p`, defined in 0334, is a dependent inductive whose constructors carry the fifth-power factors $e,f$, positivity, coprimality, parity, the exact decompositions of $A_0,B_0$, ownership of `zeroSectorQ`, and the branch-specific difference equation. In contrast, the output `GoldenZeroSectorFactorBranch`, defined in 0333, is only the three-valued enumeration

```lean
.odd
.evenLeftLow
.evenRightLow
```

Thus this `def` is a forgetful map from a complete proof certificate to the tag saying which two-adic branch the certificate belongs to.

## Mathematical meaning

This declaration proves no new mathematical proposition.

The factorization after zero-sector inversion is classified into three cases.

1. Odd branch

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5.
$$

2. Even-left-low branch

$$
A_0 = 8e^5,
\qquad
B_0 = 16f^5.
$$

3. Even-right-low branch

$$
A_0 = 16e^5,
\qquad
B_0 = 8f^5.
$$

`GoldenZeroSectorFactorData p` stores these cases together with proofs. Some later theorems, however, need only the information “which branch are we in?” rather than the full factorization certificate.

For that purpose, `branch` performs the information compression

$$
\text{exact factor certificate}
\longmapsto
\text{branch label}.
$$

## Role in the complete proof

Immediately after this function, the source defines

```lean
theorem GoldenZeroSectorFactorData.odd_eleven_channel
    {p : GoldenZeroSectorInversionPacket}
    (data : GoldenZeroSectorFactorData p)
    (hbranch : data.branch = .odd) :
    ...
```

The theorem receives the complete `data`, but specifies the relevant case through the additional condition

```lean
hbranch : data.branch = .odd
```

This design lets callers state the branch through a public label equality without exposing a particular constructor of the dependent inductive in the theorem signature.

Inside the proof, `cases data` expands the three constructors. In the odd constructor the actual $e,f$ and the difference equation are available; in the two even constructors, `hbranch` reduces to an impossible branch-label equality and eliminates those cases.

Thus `branch` forms a small API boundary between

- the internal representation: a dependent inductive carrying proof data, and
- the external interface: a three-valued branch label.

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

This is the type of the implicit index `p`.

The body of `branch` does not inspect fields of `p`, but `p` is needed to form the input type

```lean
GoldenZeroSectorFactorData p
```

### `GoldenZeroSectorFactorData`

The dependent inductive from 0334.

The function pattern-matches on its three constructors:

```lean
.odd
.evenLeftLow
.evenRightLow
```

### `GoldenZeroSectorFactorBranch`

The branch-label type from 0333.

Each input constructor is mapped to the output constructor with the same name:

```lean
.odd
.evenLeftLow
.evenRightLow
```

There are no directly used arithmetic theorems or helper lemmas.

## Construction flow

The definition is completed by three pattern-matching equations.

### 1. Odd constructor

```lean
| .odd .. => .odd
```

All the $e,f$ values and proof fields carried by `GoldenZeroSectorFactorData.odd` are discarded through `..`, and the label `.odd` is returned.

### 2. Even-left-low constructor

```lean
| .evenLeftLow .. => .evenLeftLow
```

Again the certificate contents are ignored and the label `.evenLeftLow` is returned.

### 3. Even-right-low constructor

```lean
| .evenRightLow .. => .evenRightLow
```

The function returns `.evenRightLow`.

These three clauses define the correspondence on all constructors of `GoldenZeroSectorFactorData`.

## Lean-specific processing

### Forgetting dependency into a nondependent label

The input type

```lean
GoldenZeroSectorFactorData p
```

depends on `p`, whereas the output

```lean
GoldenZeroSectorFactorBranch
```

does not.

The function therefore extracts nondependent classification information from dependent proof data.

### The `..` pattern

Each factor-data constructor has many arguments, but none is needed to determine its branch.

The pattern

```lean
.odd ..
```

ignores them without individually naming every field. This is particularly appropriate here because it makes the purpose of the definition visually explicit: only the constructor identity matters.

### Contextual resolution of constructor names

The `.odd` on the left is resolved as `GoldenZeroSectorFactorData.odd`, while the `.odd` on the right is resolved as `GoldenZeroSectorFactorBranch.odd` from the expected types.

Because both types use matching constructor names, the one-to-one map is immediately visible in the Lean source.

## Redundancy and duplication

There is essentially no implementation-level redundancy.

Three input constructors must be mapped to three output constructors, so the three pattern clauses are required.

At the design level, `GoldenZeroSectorFactorData` and `GoldenZeroSectorFactorBranch` duplicate the same three branch names. This duplication appears intentional: the former is proof-carrying data, while the latter is a lightweight public label.

If no independent label type were needed, later proofs could simply perform `cases` directly on `GoldenZeroSectorFactorData`. However, the signature of the immediately following `odd_eleven_channel` demonstrates a concrete use for the separate label API.

## Optimization candidates

### Current implementation

The current pattern match is already close to minimal in both code size and computational meaning.

### Adding `@[simp]`

One possible optimization is

```lean
@[simp] def GoldenZeroSectorFactorData.branch ...
```

or separate simp lemmas for the three constructor equations.

The next theorem currently eliminates even branches with expressions of the form

```lean
simp [GoldenZeroSectorFactorData.branch] at hbranch
```

so registering the projection equations for simplification could shorten later proofs.

Whether `@[simp]` should be part of the public API depends on the library-wide rewriting policy. No Lean build is performed here, so the broader effect is unverified and this remains only an optimization candidate.

### Integrating the branch label with the certificate

A more radical redesign could index factor data by the branch label, schematically

```lean
GoldenZeroSectorFactorData : GoldenZeroSectorFactorBranch → ...
```

but this would substantially alter the downstream API and constructor design and could make the current existential/certificate workflow more complicated. The present design is operationally simpler.

## Required Mathlib imports and import optimization candidates

The standalone canonical source uses

```lean
import Mathlib
```

However, the body of this particular `def` uses only pattern matching and the three previously defined types. It invokes no new Mathlib theorem, tactic, or arithmetic API.

Therefore this declaration itself adds essentially no Mathlib dependency beyond having

```lean
GoldenZeroSectorInversionPacket
GoldenZeroSectorFactorData
GoldenZeroSectorFactorBranch
```

available.

At the source-module level, determining a minimal replacement for `import Mathlib` cannot be done from this declaration alone, because other declarations in the same `SignedGoldenZeroSectorFactorization.lean` source use `Nat.Coprime`, `Odd`, `Even`, `omega`, `norm_num`, `ring`, and related APIs. The exact minimal import set is unverified.

## Comparator challenge suitability

**Suitable, with low difficulty.**

A challenge can provide the 0333 and 0334 types and ask the participant to implement

```lean
def GoldenZeroSectorFactorData.branch ...
```

The comparator criterion is simple: each of the three constructors must map to the corresponding branch label.

It is not a good challenge for mathematical reasoning, because this definition performs no number-theoretic deduction. It is instead a clean exercise in Lean data design, dependent inductives, and pattern matching.

## Next declaration to read

The next declaration is

```lean
theorem GoldenZeroSectorFactorData.odd_eleven_channel
```

This theorem puts the new lightweight condition

```lean
data.branch = .odd
```

to actual use and extracts from odd-branch factor data

$$
11 \mid d,
$$

as well as

$$
11 \nmid c,
\qquad
11 \nmid e,
\qquad
11 \nmid f,
\qquad
11 \nmid ef.
$$

The modulo-$11$ channel prepared by 0331 `fifth_mod_eleven_cases` and 0332 `eleven_dvd_d_of_fifth_add_four_fifth` is therefore connected, through the exact factor certificate of 0334 and the branch API defined here, to explicit branch-specific packet information.
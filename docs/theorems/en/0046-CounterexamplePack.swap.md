# 0046 — `CounterexamplePack.swap`

## 1. Target declaration

```lean
theorem CounterexamplePack.swap
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    CounterexamplePack y x z where
  hx := hPack.hy
  hy := hPack.hx
  hz := hPack.hz
  hxy := hPack.hxy.symm
  hEq := by
    simpa [Fermat5Equation, Nat.add_comm] using hPack.hEq
```

Its fully qualified name is `DkMath.FLT.Five.CounterexamplePack.swap`.

## 2. Lean type

For arbitrary natural numbers `x y z`, it constructs `CounterexamplePack y x z` from `CounterexamplePack x y z`.

```lean
CounterexamplePack x y z → CounterexamplePack y x z
```

Because the theorem is placed under the `CounterexamplePack` namespace, it can also be used in method form as `hPack.swap`.

## 3. Mathematical statement

For a positive primitive Fermat candidate

$$
x^5+y^5=z^5,\qquad \gcd(x,y)=1,
$$

swapping the two terms on the left preserves

$$
y^5+x^5=z^5,\qquad \gcd(y,x)=1.
$$

Thus the counterexample packet is symmetric under exchanging the two left coordinates.

## 4. Role in the whole proof

The later signed Branch A development must send both the case where a five-divisible object appears on the `z-y` side and the corresponding case on the swapped `z-x` side into the same mechanism. This theorem makes the left-side symmetry explicit as a structure transformation in Lean, allowing lemmas written in one orientation to be reused in the other.

It introduces no new number theory. Instead, it fixes the symmetry of the Fermat equation and primitivity as a reusable API.

## 5. Direct dependencies

- `CounterexamplePack`: structure containing positivity, coprimality, and the Fermat equation.
- `Fermat5Equation`: the proposition `x ^ 5 + y ^ 5 = z ^ 5`.
- `Nat.Coprime.symm`: derives `Coprime y x` from `Coprime x y`.
- `Nat.add_comm`: exchanges the two terms in the Fermat equation.
- `simpa`: combines unfolding and normalization by commutativity.

## 6. Proof flow

1. Directly construct the swapped `CounterexamplePack y x z` with `where` syntax.
2. Fill the new `hx` with the old `hy`, and the new `hy` with the old `hx`.
3. Reuse `hz` unchanged because the right coordinate does not move.
4. Reverse coprimality with `hPack.hxy.symm`.
5. Unfold `Fermat5Equation`, commute the left-hand addition with `Nat.add_comm`, and reuse `hPack.hEq`.

## 7. Lean-specific processing

### Named-field structure construction

Every field is filled by name below `where`, so the proof does not depend on the declaration order of the fields of `CounterexamplePack`. This is more robust than a positional constructor for long-term maintenance.

### Namespace method

Because the declaration is named `CounterexamplePack.swap`, dot notation applies to a value of the matching type, allowing the compact form `hPack.swap`.

### Definitional unfolding by `simpa`

The type of `hPack.hEq` is `Fermat5Equation x y z`, while the target is `Fermat5Equation y x z`. After unfolding both propositions, the only difference is the order of addition, so `simpa [Fermat5Equation, Nat.add_comm]` closes the field.

## 8. Redundancy and duplication

Mathematically, the theorem merely lifts symmetry of addition and coprimality into a structure. Its logical content is small. Nevertheless, it removes repeated field rearrangement downstream and clarifies the symmetric routing of the signed branches, so it is valuable as a separate theorem.

The line `hz := hPack.hz` is an identity-level repetition, but it is required to complete the structure.

## 9. Optimization candidates

The current proof is already short and uses stable named-field construction, so no substantial optimization is needed. One could rewrite the equation field with a more explicit unfolding step, but the current local `simpa` is clearer and avoids unfolding the entire structure hypothesis.

A further symmetry API could state that swapping twice returns the original packet:

```lean
(hPack.swap).swap = hPack
```

However, since these are values in `Prop`, proof irrelevance makes such an equality easy and it is usually unnecessary in the mathematical route.

## 10. Required Mathlib imports and import optimization

The generated standalone file uses `import Mathlib`. This declaration itself only needs natural numbers, powers, `Nat.Coprime`, structures, `simpa`, and commutativity of addition.

The exact minimal import is not established in this run because the original split module could not be fetched directly. It is likely that importing the preceding module defining `CounterexamplePack` and `Fermat5Equation` is sufficient without an additional broad Mathlib import. This is an explicit inference that should be checked by a Lean import audit.

## 11. Comparator challenge suitability

It is well suited. A challenge can be stated as follows:

> From `CounterexamplePack x y z`, construct the swapped `CounterexamplePack y x z`. Use commutativity of addition for the equation and fill every structure field explicitly.

Useful comparison criteria are whether a solution:

- uses named-field construction,
- selects `Nat.Coprime.symm` correctly,
- keeps the unfolding of `Fermat5Equation` local,
- reuses the equation with `simpa [Nat.add_comm]`.

Although short, it is a good test of structure repackaging and definitional unfolding.

## 12. Evidence and qualifications

The declaration type and proof body were confirmed from the generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch. There it appears at the beginning of the section corresponding to `SignedBranchA.lean`.

Existing PDFs are narrative support, while the retrieved Lean declaration is the final authority here. The exact import line of the original split file could not be fetched from this repository during this run, so the import-minimization discussion is explicitly marked as an inference.

## 13. Next theorem to read

Next read `DkMath.FLT.Five.five_not_dvd_GN5_of_five_not_dvd_gap`.

Using the five-adic decomposition

$$
GN5(g,y)=g^4+5K,
$$

it proves that if five does not divide the gap, then five does not divide `GN5 g y` either. This supports the mod-5 and mod-25 routing in signed Branch A.

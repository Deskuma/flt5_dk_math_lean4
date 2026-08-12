# 0049 — `pow_five_mod_five`

## 1. Target declaration

```lean
theorem pow_five_mod_five (n : ℕ) :
    n ^ 5 % 5 = n % 5 := by
  rw [Nat.pow_mod]
  have hn : n % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 5 <;> norm_num [h]
```

The fully qualified name is `DkMath.FLT.Five.pow_five_mod_five`.

## 2. Lean type

```lean
(n : ℕ) → n ^ 5 % 5 = n % 5
```

For every natural number `n`, its fifth power and the base itself have the same remainder modulo five.

## 3. Mathematical statement

Mathematically, the theorem states

$$
n^5 \equiv n \pmod 5.
$$

This is the specialization of Fermat's little theorem to the prime five. The Lean proof does not invoke the general theorem; instead, it directly checks the five possible values of `n % 5`.

## 4. Role in the overall proof

This lemma is the normalization rule used when the FLT5 equation

$$
x^5+y^5=z^5
$$

is mapped modulo five. It reduces fifth powers to their bases and exposes the linear congruence

$$
x+y \equiv z \pmod 5.
$$

Subsequent declarations use this relation to show that if one coordinate is divisible by five, then either the difference `z-x` or the sum `x+y` is divisible by five.

The preceding theorem `five_not_dvd_x_of_branchB` establishes `5 ∤ x` for a Branch B candidate. The present theorem is the modular arithmetic kernel that allows the proof to proceed from that fact to the two signed Branch A orientations.

## 5. Direct dependencies

- `Nat.pow_mod`: rewrites the remainder of a power through the remainder of its base.
- `Nat.mod_lt`: proves `n % 5 < 5` for the positive modulus five.
- `interval_cases`: splits a natural number known to lie in a finite interval into all possible values.
- `norm_num`: closes the numerical equality in each residue case `0,1,2,3,4`.
- `by decide`: discharges the decidable fact `0 < 5`.

The theorem has no direct dependency on an FLT5-specific definition; it is a pure natural-number arithmetic lemma.

## 6. Proof flow

1. `rw [Nat.pow_mod]` normalizes the left-hand side to a power of `n % 5`.
2. `Nat.mod_lt` establishes `n % 5 < 5`.
3. `interval_cases h : n % 5` enumerates the five residues from `0` through `4`.
4. `norm_num [h]` evaluates each branch.

Thus the proof performs a complete finite-state check rather than invoking general congruence theory.

## 7. Lean-specific processing

`rw [Nat.pow_mod]` explicitly performs the mathematically familiar operation of reducing the base before computing the power. This is what turns the unrestricted input `n` into the finite object `n % 5` that `interval_cases` can exhaust.

The local fact `hn : n % 5 < 5` is inferred by `interval_cases` as the interval bound. In each generated branch, the equality `h` is supplied to `norm_num` as a rewrite rule.

## 8. Redundancy and duplication

Although `hn` is not named later in the visible script, it is not logically unused: `interval_cases` relies on it to infer the upper bound.

The mathematical statement overlaps with Fermat's little theorem and with possible lemmas over `ZMod 5`. Nevertheless, the current proof is short, transparent, and highly auditable because it exposes the complete residue calculation for the fixed modulus five.

## 9. Optimization candidates

One possible generalization is to prove, for a prime `p`, a theorem of the form

```lean
n ^ p % p = n % p
```

from an existing Fermat theorem and specialize it to `p = 5`. That route may introduce a larger modular-arithmetic API and additional coercions, making the local proof longer than the five-case enumeration.

For the present fixed-modulus purpose, the implementation is already small and stable. A replacement is worthwhile only if Mathlib contains an exactly matching `Nat` theorem that can be reused by a direct `simpa`.

## 10. Required Mathlib imports and import optimization

The generated standalone source is confirmed to compile under `import Mathlib`.

The proof actually needs natural-number remainder and powers together with `interval_cases` and `norm_num`. The exact import list of the split source module `SignedBranchA.lean` could not be retrieved in this audit, so the following is only a candidate list and includes an explicit inference:

- `Mathlib.Data.Nat.ModEq`
- `Mathlib.Tactic.IntervalCases`
- `Mathlib.Tactic.NormNum`

Any import minimization should be checked by compiling the split module. No Lean build was run in this museum update.

## 11. Comparator challenge suitability

The theorem is well suited to a Comparator challenge. The fixed target can be

```lean
theorem challenge (n : ℕ) : n ^ 5 % 5 = n % 5 := by
  ...
```

Useful comparison axes include:

- finite residue enumeration versus Fermat's little theorem;
- a direct `Nat` proof versus a proof through `ZMod 5`;
- import count and proof-term size;
- transparency of the specialization to the constant five.

Despite its small size, the theorem gives a clear comparison between computational and general-theory proof styles.

## 12. Next theorem to read

The next declaration is

```lean
DkMath.FLT.Five.five_dvd_z_sub_x_of_fermat5_of_five_dvd_y
```

Assuming `5 ∣ y`, it maps the Fermat equation modulo five, uses the present theorem to reduce fifth powers to bases, and derives

$$
5 \mid z-x.
$$

It is the first direct consumer of `pow_five_mod_five`.
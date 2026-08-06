# 0051 — `five_dvd_x_add_y_of_fermat5_of_five_dvd_z`

## 1. Target declaration

```lean
theorem five_dvd_x_add_y_of_fermat5_of_five_dvd_z
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5z : 5 ∣ z) :
    5 ∣ x + y := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hz0 : z % 5 = 0 := Nat.mod_eq_zero_of_dvd h5z
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.add_mod, pow_five_mod_five, hz0] using hmod
```

The fully qualified name is `DkMath.FLT.Five.five_dvd_x_add_y_of_fermat5_of_five_dvd_z`.

## 2. Lean type

```lean
{ x y z : ℕ } →
Fermat5Equation x y z →
5 ∣ z →
5 ∣ x + y
```

From a natural-number FLT5 equation and `5 ∣ z`, the theorem proves that the sum of the two left bases, `x + y`, is divisible by five.

## 3. Mathematical statement

The assumptions are

$$
x^5+y^5=z^5,\qquad 5\mid z.
$$

Reducing modulo five makes the right-hand side zero. Using article 0049,

$$
n^5\equiv n\pmod 5,
$$

we obtain

$$
x+y\equiv 0\pmod 5.
$$

Therefore,

$$
5\mid(x+y).
$$

This is the counterpart of article 0050's difference-gap lemma. Article 0050 produces `z-x` when one left coordinate is divisible by five; the present theorem produces the signed sum `x+y` when the result coordinate is divisible by five.

## 4. Role in the complete proof

This theorem is the **sum-gap routing bridge** into signed Branch A. The later signed routing transforms the finite residue-class split on the Branch B side into two orientations:

```text
5 ∣ y
  → 5 ∣ z - x
  → SignedBranchAOrientation.differenceGap

5 ∣ z
  → 5 ∣ x + y
  → SignedBranchAOrientation.sumGap
```

In particular, `signedBranchA_normalForm_of_branchB` directly uses this theorem in the `5 ∣ z` case to construct `SignedBranchAOrientation.sumGap`. Thus it is a local adapter converting an ordinary Fermat equation into the evidence for a “sum gap” accepted by the signed five-adic descent.

## 5. Direct dependencies

- `Fermat5Equation`: the entry definition for `x^5 + y^5 = z^5`.
- `pow_five_mod_five`: article 0049, reducing fifth powers to their bases modulo five.
- `congrArg`: applies `fun n => n % 5` to both sides of an equality.
- `Nat.mod_eq_zero_of_dvd`: derives `z % 5 = 0` from `5 ∣ z`.
- `Nat.add_mod`: decomposes the remainder of a sum.
- `Nat.dvd_of_mod_eq_zero`: converts remainder zero back to divisibility.
- `simpa`: simultaneously normalizes fifth-power remainders, sum remainders, and `z % 5 = 0`.

The theorem does not directly depend on `CounterexamplePack`, positivity, or coprimality. The equation and `5 ∣ z` suffice.

## 6. Proof flow

1. Unfold `Fermat5Equation` into the ordinary equality `hEqNat`.
2. Apply `% 5` to both sides with `congrArg`, obtaining `hmod`.
3. Derive `hz0 : z % 5 = 0` from `h5z`.
4. Use `Nat.dvd_of_mod_eq_zero` to change the goal into `(x+y)%5=0`.
5. Simplify `hmod` with `Nat.add_mod`, `pow_five_mod_five`, and `hz0`.

## 7. Lean-specific processing

`hEqNat` removes the definitional wrapper. The line `simpa [Fermat5Equation] using hEq` converts the hypothesis into a shape directly accepted by `congrArg`.

`congrArg (fun n : ℕ => n % 5)` obtains a modulo-five equality from the general principle of applying the same function to equal terms, without introducing a dedicated congruence structure.

`apply Nat.dvd_of_mod_eq_zero` transforms the divisibility goal into a zero-remainder goal. The final `simpa` uses

```lean
Nat.add_mod
pow_five_mod_five
hz0
```

together to normalize `hmod` into the target.

Unlike article 0050, this theorem contains no natural-number subtraction, so no order or truncated-subtraction issue appears.

## 8. Redundancy and duplication

`hEqNat` and `hmod` could be compressed into one expression. Their separation, however, makes the removal of the entry wrapper and the modulo-five mapping independently auditable.

The proof skeleton substantially duplicates article 0050. Both proofs unfold `Fermat5Equation`, apply `% 5` to both sides, set one coordinate's remainder to zero, and reduce fifth powers using `pow_five_mod_five`.

The final `apply` and `simpa` are already concise, so there is little local redundancy within this theorem itself.

## 9. Optimization candidates

The most natural shared abstraction is a lemma deriving

```lean
(x + y) % 5 = z % 5
```

from the Fermat equation. For example:

```lean
theorem add_mod_five_eq_of_fermat5
    {x y z : ℕ} (hEq : Fermat5Equation x y z) :
    (x + y) % 5 = z % 5 := by
  ...
```

Then the present theorem would become a short consumer replacing the right-hand side by zero using `h5z`. Article 0050 could also be built from the same shared kernel.

Another option is to return `Nat.ModEq 5 (x+y) z`, but the current code closes directly with remainder equalities, so the extra conversion layer should be justified.

For this theorem alone, the existing proof is already compact. The main optimization opportunity is duplication removal.

## 10. Required Mathlib imports and import optimization

The generated standalone source is checked under `import Mathlib`. In generated order, the declaration belongs to `DkMath/FLT/Five/SignedBranchA.lean`.

The directly used Mathlib facilities are natural-number remainder and divisibility, `Nat.add_mod`, `congrArg`, and `simpa`. The exact imports of the split source module could not be confirmed in this repository, so the following minimal candidates include inference:

- `Mathlib.Data.Nat.ModEq`
- `Mathlib.Data.Nat.Prime.Basic`
- `Mathlib.Tactic`

`Mathlib.Data.Nat.Prime.Basic` is probably unnecessary for this theorem in isolation and may only be retained for neighboring declarations in the same module. Exact import minimization requires a standalone build of the split source. No Lean build was run in this article.

## 11. Comparator challenge suitability

The theorem is suitable. A challenge can fix the following type:

```lean
theorem challenge
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5z : 5 ∣ z) :
    5 ∣ x + y := by
  ...
```

Useful comparison axes are:

- direct remainder equalities versus `Nat.ModEq`,
- reusing `pow_five_mod_five` versus invoking a general Fermat theorem,
- extracting a shared congruence kernel with article 0050 versus keeping local proofs independent,
- using `apply Nat.dvd_of_mod_eq_zero` versus passing a completed remainder equality as a term.

It is short, but exposes meaningful choices in congruence API design and reuse policy.

## 12. Next declaration

The next declaration is

```lean
DkMath.FLT.Five.SignedBranchAOrientation
```

This inductive interface represents the exceptional five-adic orientations of the exponent-five equation with two constructors:

- `differenceGap`,
- `sumGap`.

It is the first structured layer receiving the two divisibility facts supplied by this article and article 0050 and routing them into the signed five-adic descent.

# 0050 — `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y`

## 1. Target declaration

```lean
theorem five_dvd_z_sub_x_of_fermat5_of_five_dvd_y
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5y : 5 ∣ y) :
    5 ∣ z - x := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hy0 : y % 5 = 0 := Nat.mod_eq_zero_of_dvd h5y
  have hxz : x % 5 = z % 5 := by
    simpa [Nat.add_mod, pow_five_mod_five, hy0] using hmod
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxz.symm)
```

The fully qualified name is `DkMath.FLT.Five.five_dvd_z_sub_x_of_fermat5_of_five_dvd_y`.

## 2. Lean type

```lean
{ x y z : ℕ } →
Fermat5Equation x y z →
5 ∣ y →
5 ∣ z - x
```

From an FLT5 equation over the natural numbers and `5 ∣ y`, the theorem proves that the truncated natural-number difference `z - x` is divisible by five.

## 3. Mathematical statement

The assumptions are

$$
x^5+y^5=z^5,\qquad 5\mid y.
$$

Modulo five, `y^5` vanishes, and article 0049 gives

$$
n^5\equiv n\pmod 5.
$$

Therefore

$$
x\equiv z\pmod 5,
$$

and hence

$$
5\mid(z-x).
$$

The Lean conclusion uses natural subtraction rather than integer subtraction. Nevertheless, the truncated difference of two natural numbers with the same residue is still zero modulo five, so the theorem type does not need a separate hypothesis `x ≤ z`.

## 4. Role in the complete proof

This theorem is the **difference-gap routing bridge** into signed Branch A. When a separate finite residue classification yields `5 ∣ y` for a Branch B candidate, the result is combined with `CounterexamplePack.swap` to build the orientation in which the swapped natural gap `z-x` is divisible by five.

The later theorem `signedBranchA_normalForm_of_branchB` consumes it in the following pattern:

```text
5 ∣ y
  + CounterexamplePack.swap
  + 5 ∣ z - x
        ↓
SignedBranchAOrientation.differenceGap
```

Thus the theorem converts a congruence fact modulo five into a structured branch witness accepted by the signed five-adic descent.

## 5. Direct dependencies

- `Fermat5Equation`: the entry definition for `x^5 + y^5 = z^5`.
- `pow_five_mod_five`: article 0049, reducing fifth powers to their bases modulo five.
- `congrArg`: applies `fun n => n % 5` to both sides of an equality.
- `Nat.mod_eq_zero_of_dvd`: derives `y % 5 = 0` from `5 ∣ y`.
- `Nat.add_mod`: decomposes the residue of a sum.
- `Nat.sub_mod_eq_zero_of_mod_eq`: turns equal residues into zero residue for the corresponding natural difference.
- `Nat.dvd_of_mod_eq_zero`: converts zero residue back to divisibility.

The theorem does not directly depend on `CounterexamplePack`, positivity, or coprimality. The equation and `5 ∣ y` are sufficient.

## 6. Proof flow

1. Unfold `Fermat5Equation` and obtain the ordinary natural-number equality `hEqNat`.
2. Apply `% 5` to both sides with `congrArg`, producing `hmod`.
3. Derive `hy0 : y % 5 = 0` from `h5y`.
4. Simplify `hmod` with `Nat.add_mod`, `pow_five_mod_five`, and `hy0` to obtain `hxz : x % 5 = z % 5`.
5. Use `hxz.symm` to prove `(z-x)%5=0`, then convert this to `5 ∣ z-x` with `Nat.dvd_of_mod_eq_zero`.

## 7. Lean-specific processing

`hEqNat` removes the definitional wrapper. The line `simpa [Fermat5Equation] using hEq` turns the packaged proposition into an ordinary equality that is convenient for `congrArg`.

`congrArg (fun n : ℕ => n % 5)` uses the general principle of applying the same function to equal terms rather than a dedicated congruence API.

The final use of `hxz.symm` is determined by the orientation of the target. Since the target is `z-x`, `Nat.sub_mod_eq_zero_of_mod_eq` needs `z % 5 = x % 5`, so the equality `x % 5 = z % 5` is reversed.

Natural subtraction is truncated, but no ordering proof is needed because the proof proceeds directly from equality of residues.

## 8. Redundancy and duplication

`hEqNat` could be eliminated by combining definitional unfolding with the `congrArg` step. It is retained because it separates unwrapping the equation from mapping it modulo five, which improves auditability.

Likewise, `hmod` and `hxz` could be compressed into a single intermediate statement, but they represent two distinct semantic stages: the fifth-power equation modulo five and equality of the base residues.

The proof skeleton is duplicated in the following theorem `five_dvd_x_add_y_of_fermat5_of_five_dvd_z`. Both map the equation modulo five, reduce fifth powers with `pow_five_mod_five`, and substitute zero for one coordinate residue.

## 9. Optimization candidates

The most natural shared abstraction would derive once from the fifth-power equation that

```lean
(x + y) % 5 = z % 5
```

Then this theorem and the following sum-gap theorem would become short consumers obtained by replacing one residue with zero.

However, keeping the local theorems independent makes their dependency structure and mathematical directions explicit. The amount of duplication removed would be small, so such abstraction is worthwhile only if eliminating repeated modular normalization is a priority.

A second option is to use `Nat.ModEq 5 x z` as the intermediate representation. The current proof already closes cleanly with equality of `%` expressions, so the extra conversion layer offers limited benefit.

## 10. Required Mathlib imports and import optimization

The generated standalone source is verified under `import Mathlib`. The generated ordering also confirms that this declaration belongs to `DkMath/FLT/Five/SignedBranchA.lean`.

The directly used Mathlib functionality consists of natural-number remainders and divisibility, `Nat.add_mod`, the natural-subtraction remainder lemma, and simplification. The split source file is not present in this repository, so its exact import lines could not be verified. The following are therefore candidate minimal imports and include an explicit element of inference:

- `Mathlib.Data.Nat.ModEq`
- `Mathlib.Data.Nat.Prime.Basic`
- `Mathlib.Tactic`

Actual import minimization would require building the split module in isolation. No Lean build was run in this article.

## 11. Comparator challenge suitability

This theorem is suitable. A challenge can fix the following type:

```lean
theorem challenge
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5y : 5 ∣ y) :
    5 ∣ z - x := by
  ...
```

Useful comparison axes are:

- direct manipulation of `%` equalities versus `Nat.ModEq`;
- reuse of `pow_five_mod_five` versus a general Fermat little theorem;
- deriving `x ≤ z` and treating the difference arithmetically versus avoiding order through the natural-subtraction residue lemma;
- extracting a shared kernel with the following sum-gap theorem.

Although short, the theorem exposes meaningful design choices around natural subtraction, congruences, and API selection.

## 12. Next theorem to read

The next declaration is

```lean
DkMath.FLT.Five.five_dvd_x_add_y_of_fermat5_of_five_dvd_z
```

Assuming `5 ∣ z`, it uses the same modulo-five normalization to prove

$$
5\mid(x+y),
$$

supplying the paired `sumGap` direction of signed Branch A.
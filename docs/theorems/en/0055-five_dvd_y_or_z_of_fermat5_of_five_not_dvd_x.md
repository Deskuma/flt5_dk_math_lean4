# 0055 — `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x`

## 1. Lean declaration

```lean
/-- A fifth-power equation with `5 ∤ x` forces five into `y` or `z`. -/
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z := by
  let xr : Fin 25 := ⟨x % 25, Nat.mod_lt _ (by decide)⟩
  let yr : Fin 25 := ⟨y % 25, Nat.mod_lt _ (by decide)⟩
  let zr : Fin 25 := ⟨z % 25, Nat.mod_lt _ (by decide)⟩
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hEqMod :
      ((x % 25) ^ 5 + (y % 25) ^ 5) % 25 = (z % 25) ^ 5 % 25 := by
    have h := congrArg (fun n : ℕ => n % 25) hEqNat
    simpa [Nat.add_mod, Nat.pow_mod] using h
  have h5xr : ¬ 5 ∣ x % 25 := by
    intro h
    exact h5x ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h)
  have hres := mod25_fifth_residue_classification xr yr zr
  have hfinite : 5 ∣ y % 25 ∨ 5 ∣ z % 25 := by
    simpa [xr, yr, zr] using hres hEqMod h5xr
  rcases hfinite with h5yr | h5zr
  · exact Or.inl ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5yr)
  · exact Or.inr ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5zr)
```

## 2. Lean type

```lean
{x y z : ℕ} →
Fermat5Equation x y z →
(¬ 5 ∣ x) →
5 ∣ y ∨ 5 ∣ z
```

The theorem takes a natural-number Fermat equation of exponent five together with `5 ∤ x`, and returns that five divides at least one of the remaining two coordinates.

## 3. Mathematical statement

If

$$
x^5+y^5=z^5,
\qquad
5\nmid x,
$$

then

$$
5\mid y
\quad\text{or}\quad
5\mid z.
$$

The implementation does not classify the natural numbers directly. It reduces all three coordinates modulo $25$ and invokes the finite residue classification from article 0054.

## 4. Role in the full proof

Article 0048 gives `5 ∤ x` from the Branch B hypothesis. To route the candidate into signed Branch A, the proof then has to determine which of `y` or `z` carries a factor of five.

```text
CounterexamplePack x y z
        +
Branch B: 5 ∤ (z - y)
        ↓ 0048
      5 ∤ x
        ↓ 0055
  5 ∣ y  ∨  5 ∣ z
      ↙             ↘
0050 difference     0051 sum
      ↘             ↙
 SignedBranchAOrientation
```

In the `5 ∣ y` branch, article 0050 yields `5 ∣ z - x`, so after swapping the counterexample pack one obtains a `differenceGap` orientation. In the `5 ∣ z` branch, article 0051 yields `5 ∣ x + y`, giving a `sumGap` orientation for the original pack.

Thus this theorem is the central arithmetic branching point of the routing theorem that sends a Branch B candidate into one of the two signed five-adic entry configurations.

## 5. Direct dependencies

Repository-specific direct dependencies are:

- `Fermat5Equation`
- `mod25_fifth_residue_classification` — article 0054, the private finite residue lemma

The main Mathlib components are:

- `Fin 25`
- `Nat.mod_lt`
- `congrArg`
- `Nat.add_mod`
- `Nat.pow_mod`
- `Nat.dvd_mod_iff`
- `norm_num`
- `Or.inl`, `Or.inr`
- `rcases`

The key bridge is `Nat.dvd_mod_iff`, which transfers divisibility by five back and forth between a natural number and its representative modulo $25$.

## 6. Proof flow

1. Construct `xr yr zr : Fin 25` from `x % 25`, `y % 25`, and `z % 25`.
2. Unfold `Fermat5Equation` to obtain the natural-number equality `x^5 + y^5 = z^5`.
3. Apply `% 25` to both sides with `congrArg`.
4. Normalize the result with `Nat.add_mod` and `Nat.pow_mod` into the shape expected by article 0054.
5. Derive `5 ∤ x % 25` from `5 ∤ x`, using `Nat.dvd_mod_iff` and the fact that $5\mid25$.
6. Apply `mod25_fifth_residue_classification xr yr zr` to obtain `5 ∣ y % 25 ∨ 5 ∣ z % 25`.
7. In each branch, use `Nat.dvd_mod_iff` again to lift the divisibility statement back to the original natural number.

The essential pattern is therefore “naturals → finite modulo-25 world → naturals”.

## 7. Lean-specific processing

### 7.1 `let xr : Fin 25 := ...`

A `Fin 25` value contains both the natural value and a proof that it is below $25$. `Nat.mod_lt _ (by decide)` supplies that bound.

### 7.2 `congrArg`

The proof derives a congruence by applying `% 25` to both sides of the original equality:

```lean
have h := congrArg (fun n : ℕ => n % 25) hEqNat
```

No separate congruence relation type is introduced; the congruence is represented as equality of remainder values.

### 7.3 `Nat.pow_mod`

The finite lemma expects powers of residue representatives. Applying `% 25` to the original equation initially produces powers before reduction, so `Nat.pow_mod` and `Nat.add_mod` push the reduction inside.

### 7.4 `Nat.dvd_mod_iff`

Because $5\mid25$,

$$
5\mid(n\bmod25)
\quad\Longleftrightarrow\quad
5\mid n.
$$

The current proof uses this bridge three times.

### 7.5 Public wrapper around a `private` lemma

Article 0054 is an implementation detail local to the source file. The present theorem hides that finite-computation detail and exposes a stable natural-number theorem as public API.

## 8. Redundancy and duplication

`Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)` appears three times: once when pushing nondivisibility of `x` down modulo $25$, and twice when lifting the final divisibility alternatives back to `y` and `z`. A local lemma such as

```lean
have h5mod : ∀ n : ℕ, 5 ∣ n % 25 ↔ 5 ∣ n := ...
```

would remove this repetition.

The three definitions `xr`, `yr`, and `zr` also have identical structure. A local map

```lean
let mod25 : ℕ → Fin 25 := fun n => ⟨n % 25, Nat.mod_lt _ (by decide)⟩
```

could reduce that duplication, though the current three-line version is arguably more explicit and readable.

`hEqNat` is also eliminable in principle because `Fermat5Equation` is only a definition, but naming the unpacked equality makes the subsequent `congrArg` step clearer.

## 9. Optimization candidates

1. Factor the three uses of `Nat.dvd_mod_iff` into a local equivalence `h5mod`.
2. Introduce a local map `mod25 : ℕ → Fin 25` for the three finite residues.
3. Extract the construction of `hEqMod` into a reusable lemma saying that a Fermat-five equation descends modulo $25$.
4. For greater mathematical transparency, rewrite the proof around `Nat.ModEq 25`. This makes the congruence intent explicit in the type, although the finite classifier still expects equality of remainder values at the boundary.
5. Replace the finite decision lemma 0054 with explicit fifth-power residue lemmas if one wants less dependence on finite computation and more visible mathematics, at the cost of substantially more code.

## 10. Required Mathlib imports

The generated `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

for the whole standalone development.

For this theorem alone, the relevant areas are `Fin`, natural-number remainder/divisibility/powers, `norm_num`, and basic tactics. Plausible minimal-import candidates include roughly:

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
```

This is not a verified minimal import set: the split source file `DkMath/FLT/Five/SignedBranchA.lean` has not been rebuilt while deleting imports. The surrounding file also uses `interval_cases`, `norm_num`, and finite decision proofs, so import optimization should be audited at module level rather than from this theorem in isolation.

## 11. Comparator challenge suitability

This theorem is well suited to a comparator challenge.

### Challenge proposal

Prove

```lean
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z
```

in two different ways:

- Method A: reduce to `Fin 25` and use the current finite classifier proved by `decide +kernel`.
- Method B: classify fifth-power residues modulo $25$ explicitly and reason through `Nat.ModEq`.

Compare proof time, proof-term size, readability, explanatory mathematical content, generalizability, and trust boundary.

## 12. Evidence versus inference

The declaration name, full type, proof body, direct use of article 0054, and direct consumption by the following theorem `signedBranchA_normalForm_of_branchB` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The repository README lists the existing explanatory PDFs `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`, and both files were confirmed to exist on the target branch. The exact PDF section and page corresponding to this declaration were not extracted in this run, so no PDF-specific detail has been inferred or invented.

The minimal-import suggestions above are likewise explicitly provisional because no deletion-based build audit was performed.

## 13. Next theorem to read

The next theorem uses this divisibility split to construct the signed Branch A normal form itself:

```lean
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  ...
```

At that point articles 0048, 0050, 0051, 0052, 0053, and 0055 converge into a single routing theorem, completing the normalization entry point for the following signed five-adic layer.

# 0105 — `exists_branchB_squareGoldenNormalForm`

## Lean type

```lean
theorem exists_branchB_squareGoldenNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  have hzy : a ^ 5 + y = z := by
    simpa [Nat.add_comm] using hNF.z_eq.symm
  have hGolden :
      GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5 := by
    have h := goldenNorm_eq_fifth_power_of_GN5 hNF.GN_eq
    simpa [SquareGoldenM, SquareGoldenN, hzy] using h
  have hzInt : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5 := by
    exact_mod_cast hNF.z_eq
  have hTenth :
      SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10 := by
    calc
      SquareGoldenM z y - 2 * SquareGoldenN z y =
          ((z : ℤ) - (y : ℤ)) ^ 2 := squareGolden_tenth_boundary_base z y
      _ = (a : ℤ) ^ 10 := by
        rw [hzInt]
        ring
  have hSquare := squareGolden_square_discriminant z y
  have hDiscFive :
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
          5 * (SquareGoldenN z y) ^ 2 =
        4 * (b : ℤ) ^ 5 := by
    calc
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
            5 * (SquareGoldenN z y) ^ 2 =
          4 * GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) :=
        (four_mul_goldenNorm_eq_discriminant_five
          (SquareGoldenM z y) (SquareGoldenN z y)).symm
      _ = 4 * (b : ℤ) ^ 5 := by rw [hGolden]
  exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

## Mathematical statement

The assumptions describe a primitive FLT5 candidate in Branch B.

- `hPack : CounterexamplePack x y z` carries positivity, coprimality, and $x^5+y^5=z^5$.
- `hBranch : ¬ 5 ∣ z-y` is the Branch-B condition that the gap is not divisible by $5$.

From these two assumptions, the theorem proves that there exist natural numbers $a,b$ satisfying 0104 `BranchBSquareGoldenNormalForm x y z a b`.

Expanding the packet from 0104, one first retains the fifth-power normal form

$$
z=y+a^5,
$$

and

$$
GN5(a^5,y)=b^5,
$$

and then, for the square/golden coordinates

$$
M=z^2+y^2,\qquad N=zy,
$$

obtains simultaneously

$$
\operatorname{GoldenNorm}(M,N)=b^5,
$$

$$
M-2N=a^{10},
$$

$$
M^2-4N^2=(z^2-y^2)^2,
$$

$$
(2M+N)^2-5N^2=4b^5.
$$

Thus the theorem does not discover one new algebraic identity. It proves that the fifth-power, square, golden, and discriminant-$5$ facts established separately earlier all hold **for the same witnesses $a,b$**.

## Role in the overall proof

This theorem is the **assembly theorem** of `SquareGoldenNormalForm.lean`.

Up to 0104, the required components had been prepared separately.

1. `exists_branchB_fifthPowerNormalForm` supplies $a,b$ and the fifth-power normal form.
2. 0099 `goldenNorm_eq_fifth_power_of_GN5` transports `GN5 = b^5` into the golden norm.
3. 0102 `squareGolden_tenth_boundary_base` gives $M-2N=(z-y)^2$.
4. 0103 `squareGolden_square_discriminant` gives $M^2-4N^2=(z^2-y^2)^2$.
5. 0097 `four_mul_goldenNorm_eq_discriminant_five` diagonalizes the golden norm into discriminant-$5$ form.

This theorem connects those ingredients exactly once and finally constructs the packet by

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

After this transformation, downstream contradiction cores no longer need to revisit cyclotomic factorization or coercion details. They can accept only `BranchBSquareGoldenNormalForm` and work directly with the square/golden invariants.

Architecturally, the proof is therefore split into clear phases:

$$
\text{Branch-B arithmetic}
\longrightarrow
\text{fifth-power normal form}
\longrightarrow
\text{square/golden packet}
\longrightarrow
\text{contradiction core}.
$$

## Direct dependencies

The theorem directly uses the following project-local declarations.

1. `CounterexamplePack`
2. 0104 `BranchBSquareGoldenNormalForm`
3. `exists_branchB_fifthPowerNormalForm`
4. 0099 `goldenNorm_eq_fifth_power_of_GN5`
5. 0100 `SquareGoldenM`
6. 0101 `SquareGoldenN`
7. 0102 `squareGolden_tenth_boundary_base`
8. 0103 `squareGolden_square_discriminant`
9. 0097 `four_mul_goldenNorm_eq_discriminant_five`

It also uses `BranchBFifthPowerNormalForm.z_eq` and `BranchBFifthPowerNormalForm.GN_eq` through the fields of `hNF`.

A key distinction is that the 0104 structure itself does not reference 0099, 0102, 0103, or 0097, while this theorem actually invokes them to build an inhabitant. If 0104 is the API type, 0105 is its canonical constructor theorem.

## Proof flow

### 1. Obtain the fifth-power normal-form witnesses

```lean
rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

The existential witnesses $a,b$ are fixed once at the beginning, guaranteeing at the type level that every later invariant is tied to the same fifth-power decomposition.

### 2. Orient `z = y + a^5` for the golden bridge

From the orientation of `hNF.z_eq`, the proof derives

```lean
have hzy : a ^ 5 + y = z := by
  simpa [Nat.add_comm] using hNF.z_eq.symm
```

The bridge in 0099 uses coordinates of the form `g + y`, so this form is convenient for rewriting the gap $g=a^5$ back to the endpoint $z$.

### 3. Transport the fifth power of GN5 into the golden norm

```lean
have h := goldenNorm_eq_fifth_power_of_GN5 hNF.GN_eq
simpa [SquareGoldenM, SquareGoldenN, hzy] using h
```

The result of 0099 is expressed in gap coordinates $(a^5,y)$. Using `hzy`, the proof restores the endpoint $z$ and matches the named coordinate API of 0100 and 0101, producing `hGolden`.

### 4. Move the natural-number normal form into an integer equality

```lean
have hzInt : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5 := by
  exact_mod_cast hNF.z_eq
```

The later difference

$$
(z:ℤ)-(y:ℤ)
$$

lives in the integers, so the natural-number equality is transported into $\mathbb Z$.

### 5. Build the tenth-power boundary

From 0102 one has

$$
M-2N=(z-y)^2.
$$

Substituting `hzInt` yields

$$
(z-y)^2=(a^5)^2=a^{10}.
$$

Lean delegates the last normalization to `ring`.

### 6. Reuse the square discriminant directly

```lean
have hSquare := squareGolden_square_discriminant z y
```

This is pure theorem reuse, with no new algebraic normalization.

### 7. Convert the golden norm into discriminant-$5$ form

Using 0097 in the reverse direction gives

$$
(2M+N)^2-5N^2=4\operatorname{GoldenNorm}(M,N),
$$

then rewriting by `hGolden` yields

$$
(2M+N)^2-5N^2=4b^5.
$$

### 8. Construct the packet

Finally the proof passes the original normal form and the four derived invariants to the constructor.

That single constructor line is the clearest summary of the theorem's purpose.

## Lean-specific processing

### 1. `rcases` synchronizes existential witnesses

The core issue in this theorem is witness synchronization. Fixing `a,b` with `rcases` at the beginning ensures that all later golden and square identities descend from the same fifth-power decomposition.

### 2. `simpa` absorbs a coordinate-API conversion

In `hGolden`, no new mathematics is proved. Instead, the gap-based expression from 0099 is converted into the endpoint-based API of 0100 and 0101.

```lean
simpa [SquareGoldenM, SquareGoldenN, hzy] using h
```

combines definition unfolding, additive rewriting, and endpoint identification in one step.

### 3. `exact_mod_cast` handles the $\mathbb N \to \mathbb Z$ boundary

`hNF.z_eq` is an equality of natural numbers, whereas the square/golden world lives over the integers. `exact_mod_cast` transports the same equality safely into $\mathbb Z$.

This is more than cosmetic coercion management: it is the phase transition that avoids truncated `Nat.sub` and permits ordinary ring subtraction.

### 4. `ring` is used only locally

The theorem does not re-prove large identities with `ring`. Its only algebraic normalization is essentially

$$
((y+a^5)-y)^2=a^{10}.
$$

The square discriminant and discriminant-$5$ identities are obtained by reusing earlier theorems, preserving proof provenance.

### 5. `.symm` puts 0097 in consumer-friendly orientation

0097 states

$$
4\operatorname{GoldenNorm}(M,N)=(2M+N)^2-5N^2,
$$

while the current goal starts from the discriminant expression. `.symm` reverses the equality into the convenient direction.

## Redundancy and duplication

### `hDiscFive` is derivable from `hGolden`

As noted in 0104, `discriminant_five_eq` always follows from `golden_eq` together with 0097. This theorem therefore materializes a logically redundant field explicitly.

That redundancy is nevertheless useful at the API level: downstream users that want the discriminant-$5$ equation can obtain it by projection without reapplying 0097.

### `hzy` and `hzInt` are two typed views of the same normal form

`hzy` is used over natural numbers to rewrite gap coordinates for 0099, whereas `hzInt` is used over integers for the tenth-power boundary. Both come from the same `hNF.z_eq`, so they are semantically duplicated.

Trying to force them into one helper, however, would likely introduce more cast rewriting and reduce readability. The current proof makes the natural-number and integer phases explicit.

### The 0102 square completion could be redone here with `ring`

One could prove all of `hTenth` directly from 0100, 0101, and `hzInt`. The current proof instead reuses 0102, making the proof graph and provenance clearer while avoiding repeated algebra.

## Optimization candidates

### Candidate A — add typed conversion lemmas to the normal-form API

A derived theorem such as

```lean
z_eq_int : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5
```

could hide the local `exact_mod_cast`.

The tradeoff is that it would expand a previously natural-number-oriented API with integer-world projections and blur the phase boundary.

### Candidate B — turn the derived 0104 field into a theorem

If `discriminant_five_eq` were removed from the structure and exposed instead as something like

```lean
theorem BranchBSquareGoldenNormalForm.discriminant_five_eq ...
```

then the `hDiscFive` block and one constructor obligation would disappear.

This is the clearest way to minimize the logical core, at the cost of weakening the current semantics that the packet is fully materialized when construction finishes.

### Candidate C — use a named-field constructor

The current

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

is concise but depends on the field order of 0104.

A named-field construction would be longer but more robust against field reordering or future additions.

### Candidate D — compare `ring` with `ring_nf` or a dedicated helper lemma

The current `ring` is already clear and close to optimal. Replacing it with `ring_nf` is unlikely to help much. A more meaningful design comparison would be whether the identity

$$
((Y+A^5)-Y)^2=A^{10}
$$

should exist as a named helper theorem at all.

## Required Mathlib imports and import optimization candidates

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses `import Mathlib`.

Mathlib functionality visibly used by this theorem includes mainly:

- `rcases`
- `simpa`
- `exact_mod_cast`
- `rw`
- `ring`
- `Nat.add_comm`
- coercions from naturals to integers

Thus, viewed in isolation, the tactic-side requirements are centered on `Mathlib.Tactic`, especially ring normalization and cast handling. However, the project module also depends on many project-local declarations such as `CounterexamplePack`, the normal form, and the square/golden bridge, so their import closure must also be taken into account.

Because this museum run does not perform a Lean build, no concrete minimal import list is asserted as verified fact. The safe observed state is the standalone artifact's `import Mathlib`; import minimization would need a separate incremental `#check` / build experiment.

## Comparator challenge suitability

**Yes.** This theorem is especially suitable for proof-architecture comparisons.

### Challenge 1 — theorem reuse vs monolithic `ring`

The current proof reuses 0102, 0103, and 0097. An alternative could unfold `SquareGoldenM/N` and close much more of the proof directly with algebraic tactics.

Useful comparison metrics are:

1. line count,
2. tactic cost,
3. robustness under upstream changes,
4. visibility of mathematical provenance,
5. failure localization.

The current proof may not be the absolute shortest, but it makes the origin of each invariant explicit.

### Challenge 2 — materialized packet vs minimal packet

Compare the current 0104 structure, which stores `discriminant_five_eq`, with a minimal packet where that fact is derived from `golden_eq` when needed.

This is a good test of logical minimality versus downstream API convenience.

### Challenge 3 — positional constructor vs named constructor

The final one-line constructor can be compared with a named-field construction. Positional syntax favors brevity; named fields likely favor maintainability.

## Cross-check against existing materials

The formal source of record is the `DkMath/FLT/Five/SquareGoldenNormalForm.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. There the theorem appears immediately after 0104 `BranchBSquareGoldenNormalForm`, and `BranchBSquareGoldenCore` follows it.

For the existing Japanese and English PDFs, GitHub code search returned an upstream 502 error during this run, so the concrete PDF paths and page correspondence could not be re-established. No page or section numbers are guessed. The mathematical and formal content here therefore uses the Lean source as the final authority.

## Next declaration to read

The next declaration in dependency order is

```lean
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

It narrows the large packet constructed by 0105 to the interface actually required by the later proof:

$$
\text{BranchBSquareGoldenNormalForm}\to\mathrm{False}.
$$

The theorem immediately after that, `branchB_false_of_squareGoldenCore`, constructs the packet using the present theorem `exists_branchB_squareGoldenNormalForm` and passes it to `BranchBSquareGoldenCore` to close Branch B.

Thus `BranchBSquareGoldenCore` is the natural next declaration in dependency order.
# 0104 — `BranchBSquareGoldenNormalForm`

## Lean type

```lean
structure BranchBSquareGoldenNormalForm
    (x y z a b : ℕ) : Prop where
  normal : BranchBFifthPowerNormalForm x y z a b
  golden_eq :
    GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
  tenth_boundary :
    SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
  square_discriminant :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
  discriminant_five_eq :
    (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
        5 * (SquareGoldenN z y) ^ 2 =
      4 * (b : ℤ) ^ 5
```

This is not a theorem but a `Prop`-valued structure that packages four facts that should be retained after projecting the Branch-B fifth-power normal form into square/golden coordinates.

## Mathematical statement

Write the coordinates from 0100 and 0101 as

$$
M=z^2+y^2,\qquad N=zy.
$$

Together with the already available Branch-B fifth-power normal form, this structure retains three kinds of quadratic-form information.

First, the fifth-power condition for the golden norm:

$$
\operatorname{GoldenNorm}(M,N)=b^5.
$$

Next, the tenth-power boundary coming from the gap:

$$
M-2N=a^{10}.
$$

Then, the endpoint-square discriminant:

$$
M^2-4N^2=(z^2-y^2)^2.
$$

Finally, the discriminant-five diagonalization of the golden norm:

$$
(2M+N)^2-5N^2=4b^5.
$$

Thus `BranchBSquareGoldenNormalForm` does not state one new identity. It simultaneously preserves the Branch-B natural-number data, the fifth-power decomposition, the square-world perfect-square boundaries, the golden quadratic form, and the discriminant-five equation in one proof packet.

In particular, two different “square worlds” are present in parallel.

$$
M-2N=a^{10}=(a^5)^2
$$

is the square boundary coming directly from the gap, whereas

$$
M^2-4N^2=(z^2-y^2)^2
$$

is an independent square discriminant carried by the endpoint-square coordinates. By contrast,

$$
(2M+N)^2-5N^2=4b^5
$$

is the discriminant-five boundary obtained by reading the same $(M,N)$ through the golden-ratio quadratic form.

## Role in the overall proof

The role of this structure is to serve as a **junction of invariants**.

Before this point in the proof chain, the relevant information exists as separate lemmas.

- `BranchBFifthPowerNormalForm` retains the Branch-B fifth-power normal form, including $z=y+a^5$ and `GN5 ... = b^5`.
- 0099 `goldenNorm_eq_fifth_power_of_GN5` transports the GN5 fifth-power information into the golden norm.
- 0102 `squareGolden_tenth_boundary_base` gives $M-2N=(z-y)^2$.
- 0103 `squareGolden_square_discriminant` gives $M^2-4N^2=(z^2-y^2)^2$.
- 0097 `four_mul_goldenNorm_eq_discriminant_five` diagonalizes the golden norm into discriminant-five form.

`BranchBSquareGoldenNormalForm` encloses all of this information in one type so that downstream proofs can recover the required invariants by field projection without returning to the original cyclotomic expansion.

In the Lean source, the immediately following theorem `exists_branchB_squareGoldenNormalForm` constructs an inhabitant of this structure. It ends with

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

where, after choosing the existential witnesses `a,b`, the four structure fields are supplied in order. In this sense, the present structure is the **target data model** of the next theorem.

Immediately afterward, the source defines

```lean
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

which creates a narrow core interface that only needs to consume this packet and derive a contradiction. Architecturally, the structure therefore separates “complex preprocessing” from the final contradiction core.

## Direct dependencies

The project-local dependencies that appear directly in the declaration type are:

1. `BranchBFifthPowerNormalForm`
2. 0093 `GoldenNorm`
3. 0100 `SquareGoldenM`
4. 0101 `SquareGoldenN`

In addition, the theorem that actually constructs the fields immediately afterward effectively depends on:

1. 0099 `goldenNorm_eq_fifth_power_of_GN5`
2. 0102 `squareGolden_tenth_boundary_base`
3. 0103 `squareGolden_square_discriminant`
4. 0097 `four_mul_goldenNorm_eq_discriminant_five`

The structure declaration itself does not reference these four theorems. In Lean, declaring the type of a structure is separate from constructing an inhabitant of that structure.

## Proof flow

The declaration itself has no `by` proof script. Instead, it specifies which proved facts should travel together as fields.

Conceptually, it is best read in four stages.

### 1. Preserve the original fifth-power provenance

```lean
normal : BranchBFifthPowerNormalForm x y z a b
```

Keeping this field makes it possible to return to the original Branch-B normal form even after projection into square/golden coordinates.

### 2. Fix the fifth-power value of the golden norm

```lean
golden_eq :
  GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
```

This transports and stores the fifth-power carrier previously expressed through GN5 as an integer quadratic-form statement.

### 3. Preserve both square-world boundaries

```lean
tenth_boundary :
  SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
```

and

```lean
square_discriminant :
  (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
    ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
```

The first comes from the gap relation $a^5=z-y$; the second is the square discriminant intrinsic to the endpoint coordinates.

### 4. Preserve the discriminant-five form

```lean
discriminant_five_eq :
  (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
      5 * (SquareGoldenN z y) ^ 2 =
    4 * (b : ℤ) ^ 5
```

This field materializes the diagonalized golden norm inside the packet. Downstream proofs can therefore use a Pell-like or quadratic-order equation directly without unfolding `GoldenNorm` again.

## Lean-specific processing

### 1. A proof packet via `structure ... : Prop`

Although this is a structure, its sort is `Prop`. Its fields therefore represent proof information rather than computational data and live in the world of proof irrelevance.

The intent is not to define a new numerical object, but to certify that the same tuple $(x,y,z,a,b)$ simultaneously satisfies several invariants.

### 2. The type boundary is fixed on the `ℤ` side

The parameters `x y z a b` are all natural numbers, but all quadratic-form fields are expressed over the integers. In particular, differences and discriminants are handled after `SquareGoldenM/N : ℕ → ℕ → ℤ` has already crossed the type boundary.

This avoids truncation issues from `Nat.sub` and allows expressions such as

$$
M-2N
$$

and

$$
(2M+N)^2-5N^2
$$

to be stored as ordinary ring identities.

### 3. Field names become the API

Lean automatically generates projections such as `.normal`, `.golden_eq`, `.tenth_boundary`, `.square_discriminant`, and `.discriminant_five_eq`.

In particular, the current source names the final field `discriminant_five_eq`. This article follows the current branch source rather than any older description or guessed alternative name.

### 4. Positional construction depends on field order

When using constructor notation such as

```lean
⟨hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

the order of the fields matters. A named-field constructor could reduce this order dependence, but the current theorem chooses the shorter positional form.

## Redundancy and duplication

The clearest logical redundancy is between `golden_eq` and `discriminant_five_eq`. By 0097,

$$
4\operatorname{GoldenNorm}(M,N)=(2M+N)^2-5N^2,
$$

so `discriminant_five_eq` is derivable once `golden_eq` is known.

Therefore, from the perspective of logical minimality, the final field is redundant. From the perspective of API design, however, it is useful: if downstream reasoning needs the discriminant-five equation, it can project it directly from the packet instead of reapplying 0097 each time.

Likewise, `square_discriminant` can be reproved as an identity from the definitions of 0100 and 0101. Materializing it as a field instead says explicitly that this proof phase has already established and retained the square invariant.

The `normal` field may also look excessive once a downstream stage only uses square/golden data, but it preserves provenance. Dropping it would make it harder to recover positivity, coprimality, and other information contained in the original fifth-power normal form.

Thus the duplication in this structure should be understood as prioritizing **phase-level information preservation and explicit API design** over strict logical minimality.

## Optimization candidates

### Candidate A — Separate a minimal core packet from derived API theorems

A logically smaller structure could keep only:

- `normal`
- `golden_eq`
- `tenth_boundary`
- `square_discriminant`

and derive `discriminant_five_eq` later as a theorem projection.

The advantage is a clearer dependency relation between invariants and one fewer constructor obligation. The disadvantage is that every downstream use of the discriminant-five equation must rederive it.

### Candidate B — Use named-field construction

The following construction in the next theorem is short:

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

but it is sensitive to field insertion and reordering. A named-field version such as

```lean
refine ⟨a, b, {
  normal := hNF
  golden_eq := hGolden
  tenth_boundary := hTenth
  square_discriminant := hSquare
  discriminant_five_eq := hDiscFive
}⟩
```

would be more robust, at the cost of verbosity.

### Candidate C — Make the coordinates themselves a structure

Because `SquareGoldenM z y` and `SquareGoldenN z y` are repeated in every field, one could introduce something like

```lean
structure SquareGoldenCoordinates where
  M : ℤ
  N : ℤ
```

and then state invariants about the coordinate object.

At present, however, the two lightweight `def`s are easy to unfold and rewrite. Introducing an additional coordinate structure would also add projections and constructors and would not necessarily reduce Lean proof surface.

### Candidate D — Group fields semantically

Another design would split the square-side and golden-side information into substructures, for example `SquareBoundaryPacket` and `GoldenNormPacket`, then compose them.

This could improve conceptual separation, but with only four fields at this stage the current flat structure is arguably easier to read.

## Required Mathlib imports and import optimization candidates

The standalone artifact uses

```lean
import Mathlib
```

The `BranchBSquareGoldenNormalForm` declaration itself uses no tactics. Its direct requirements are essentially:

- `ℕ`, `ℤ`
- notation and basic typeclasses for powers and ring operations
- the project-local `BranchBFifthPowerNormalForm`
- `GoldenNorm`
- `SquareGoldenM`
- `SquareGoldenN`

So, viewed in isolation, importing all of `Mathlib` is much broader than necessary.

However, the construction theorem immediately following this declaration uses `simpa`, `exact_mod_cast`, `ring`, and `rw`, while dependencies such as 0097, 0099, 0102, and 0103 also rely on tactic support. Therefore the minimal import set for the whole `SquareGoldenNormalForm.lean` module cannot be determined from this structure alone.

A safe import-optimization workflow would first expose the project-local dependency graph, then reduce tactic imports to the needed parts of `Mathlib.Tactic`, and verify the result with Lean builds. This run does not perform a Lean build, so no exact minimal import list is asserted.

## Comparator challenge suitability

This declaration is suitable, but not as a conventional “prove the same theorem more briefly” challenge. It is better viewed as a **proof-packet API design challenge**.

Possible designs to compare include:

1. The current flat structure, materializing derived invariants as fields.
2. A logically minimal field set with `discriminant_five_eq` moved to a derived theorem.
3. Separate square-side and golden-side substructures.
4. A structure that stores the coordinate pair $(M,N)$ explicitly.
5. A design that preserves `normal` provenance versus one reduced to only the downstream invariants.

Evaluation should include more than field count: downstream proof length, clarity of dependency direction, rewrite stability, projection convenience, provenance preservation, and maintainability under future field additions all matter.

From this perspective, the current design appears to prioritize a clear proof-phase boundary and downstream usability over logical minimality.

## Next theorem to read

The theorem immediately following this structure in the Lean source is

```lean
theorem exists_branchB_squareGoldenNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b := by
  ...
```

This is where the packet declared in 0104 is shown to be genuinely constructible from every Branch-B candidate rather than merely being an empty interface.

Its proof:

1. obtains `a,b,hNF` from `exists_branchB_fifthPowerNormalForm`;
2. builds `golden_eq` using 0099;
3. builds `tenth_boundary` from 0102 together with $z-y=a^5$;
4. obtains `square_discriminant` from 0103;
5. builds `discriminant_five_eq` from 0097 and `golden_eq`;
6. finally constructs the structure.

Thus article 0105 should naturally cover `exists_branchB_squareGoldenNormalForm`.

## Sources and notes

The formal source is the `DkMath/FLT/Five/SquareGoldenNormalForm.lean` section embedded in the generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch. In the current source, this structure appears immediately after the theorem corresponding to 0103 `squareGolden_square_discriminant`, followed by `exists_branchB_squareGoldenNormalForm`.

The current field name is `discriminant_five_eq`. If an older description uses another spelling, this article follows the current Lean source on the target branch.

A concrete page or section correspondence in the existing Japanese and English PDFs could not be confirmed in this run. GitHub code search returned an upstream error, so no PDF page or section number is guessed.

The standalone artifact is generated and records `DkMath/FLT/Five/SquareGoldenNormalForm.lean` as the split-source name. This article uses the current standalone content retrieved from the target branch as its primary formal evidence.
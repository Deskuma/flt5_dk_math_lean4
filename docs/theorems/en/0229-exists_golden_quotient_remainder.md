# 0229 — `exists_golden_quotient_remainder`

## Lean type

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

This is a `theorem` stating that for every nonzero divisor `y`, there exist a golden quotient `q` and remainder `r` satisfying

$$
x=qy+r
$$

and

$$
r=0\quad\text{or}\quad
\operatorname{size}(r)<\operatorname{size}(y).
$$

It packages the concrete quotient and remainder constructed earlier into a single existential Euclidean-division statement.

## Mathematical statement

The theorem is the usual existence statement for Euclidean division in the golden order.

For nonzero `y`, the preceding development has already constructed

$$
q:=\operatorname{goldenQuotient}(x,y),
$$

and

$$
r:=\operatorname{goldenRemainder}(x,y)=x-qy.
$$

The quotient-remainder reconstruction law gives

$$
x=qy+r,
$$

while 0228 `golden_remainder_size_lt` gives

$$
\operatorname{size}(r)<\operatorname{size}(y).
$$

Therefore the proof does not even need to decide whether `r = 0`: it can always choose the strict-decrease branch of the disjunction.

The theorem is thus the final packaging of already-established quotient, remainder, reconstruction, and strict-decrease facts.

## Role in the full proof

Declarations 0209–0228 in `GoldenEuclidean.lean` build the Euclidean-division machinery piece by piece.

- `GoldenRat` and `goldenRatNorm` introduce rational quotient coordinates and the quadratic norm form.
- nearest-integer rounding places the quotient error inside the fundamental cell;
- `goldenRat_norm_abs_lt_one` establishes norm contraction on that cell;
- `goldenQuotientCoords` constructs rational coordinates for `x / y`;
- `goldenQuotient` rounds those coordinates back to the golden integer lattice;
- `goldenRemainder` defines `r = x - qy`;
- `goldenEuclideanSize` turns `|N(x)|` into a natural-number measure;
- 0227 proves the exact remainder-norm identity;
- 0228 proves strict decrease of the remainder size.

Declaration 0229 is the first point where all of those ingredients are exposed as **one Euclidean-division statement**.

It does not establish a new analytic estimate or algebraic identity. Its job is assembly: package the quotient, remainder, reconstruction law, and strict decrease that have already been proved.

Immediately afterward, `goldenEuclideanDomain : EuclideanDomain GoldenInt` registers the same quotient / remainder / size mechanism in Mathlib's typeclass hierarchy. Thus 0229 provides the human-readable theorem-level Euclidean division statement immediately before the final typeclass integration.

## Direct dependencies

The main direct dependencies are:

- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0224 `goldenEuclideanSize`
- 0228 `golden_remainder_size_lt`
- 0159 `golden_mul_eq`
- `GoldenInt`

The theorem statement uses standard multiplication `q * y`, while `goldenRemainder` is defined internally through the raw operation `goldenMul`. Consequently `golden_mul_eq` is part of the raw/standard API bridge used by the reconstruction proof.

Conceptually the theorem only packages

$$
q:=goldenQuotient(x,y),
$$

$$
r:=goldenRemainder(x,y),
$$

$$
x=qy+r,
$$

and

$$
y\neq0\Longrightarrow size(r)<size(y)
$$

into

$$
\exists q,r,\ x=qy+r\land(r=0\lor size(r)<size(y)).
$$

## Proof flow

### 1. Choose the witnesses explicitly

```lean
refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
```

The proof does not search abstractly for witnesses. It directly chooses the canonical quotient and remainder already constructed upstream.

Only two goals remain:

1. `x = q * y + r`;
2. `r = 0 ∨ size r < size y`.

### 2. Close the quotient-remainder identity

```lean
· simp [goldenRemainder, golden_mul_eq]
```

Unfolding `goldenRemainder x y` gives

$$
x-goldenMul(q,y).
$$

`golden_mul_eq` converts the raw multiplication to standard `q * y`, after which `simp` closes the additive-group identity

$$
qy+(x-qy)=x.
$$

This has the same mathematical content as 0223 `golden_quotient_mul_add_remainder`, but the current proof recomputes the small identity through unfolding and simplification rather than invoking that theorem by name.

### 3. Choose the strict-decrease branch

```lean
· exact Or.inr (golden_remainder_size_lt x hy)
```

Since 0228 always provides

$$
size(r)<size(y)
$$

for nonzero `y`, the proof can select the right side of the disjunction with `Or.inr`.

No test of `r = 0` is needed.

## Lean-specific processing

`refine ⟨..., ..., ?_, ?_⟩` constructs a nested existential together with a conjunction in one constructor expression.

The logical structure is essentially

```lean
Exists fun q =>
  Exists fun r =>
    And
      (x = q * y + r)
      (Or (r = 0) (goldenEuclideanSize r < goldenEuclideanSize y))
```

The first `refine` fills the two witnesses and leaves the two proof fields as metavariables.

`Or.inr` explicitly selects the right constructor of the disjunction.

The simplification

```lean
simp [goldenRemainder, golden_mul_eq]
```

also absorbs the recurring representation boundary between the raw multiplication API and the standard ring notation.

## Redundancy and duplication

The clearest duplication is that the first conjunct does not directly reuse 0223 `golden_quotient_mul_add_remainder`.

That theorem is stated as

```lean
y * goldenQuotient x y + goldenRemainder x y = x
```

whereas 0229 requires

```lean
x = goldenQuotient x y * y + goldenRemainder x y.
```

Using 0223 directly would therefore require reversing the equality and reconciling the multiplication order. The local `simp` proof is likely shorter in the current commutative-ring API.

There is also intentional logical redundancy in

```lean
r = 0 ∨ size r < size y.
```

Under `y ≠ 0`, 0228 always proves the strict inequality, so the left branch is never needed here. The disjunction is retained because it matches the usual Euclidean-division API shape.

## Optimization candidates

1. **Reuse 0223 directly**
   - avoids reproving the reconstruction law;
   - may require symmetry and commutativity normalization.

2. **Add a reconstruction theorem in the exact standard orientation**
   - a theorem stated as `x = q * y + r` would let the first branch close by `exact`.

3. **Bundle Euclidean-division data in a structure**
   - quotient, remainder, reconstruction, and decrease certificates could be returned together, reducing overlap between 0229 and the final instance.

4. **Use a stronger internal theorem without the disjunction**
   - since nonzero `y` always gives strict decrease, one could prove internally

```lean
∃ q r, x = q * y + r ∧ size r < size y
```

   and convert to the disjunctive API only where needed.

5. **Keep the current thin packaging theorem**
   - the proof is extremely short and exposes the mathematical Euclidean-division statement clearly, so there is substantial documentation value in the current design.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct Mathlib surface used by this theorem is small:

- existential and conjunction constructors;
- `Or.inr`;
- `simp`;
- standard additive-group and ring notation.

The theorem itself uses no difficult analytic or arithmetic tactic.

However, its direct dependency 0228 uses `round`, absolute-value inequalities, and `exact_mod_cast`, while `GoldenEuclidean.lean` as a whole also uses tactics such as `field_simp`, `ring`, `linarith`, and `norm_num`.

Therefore the declaration in isolation could probably use a much smaller import set than full `Mathlib`, but module-level import minimization is controlled by the surrounding Euclidean construction. No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Although 0229 is mathematically thin, it is a good API-packaging comparison.

Possible variants are:

- A: current `refine` + `simp` + `Or.inr`;
- B: direct theorem-level composition of 0223 and 0228;
- C: bundle quotient / remainder / decrease in a structure;
- D: construct the final `EuclideanDomain` first and derive a generic division-existence theorem afterward;
- E: prove a stronger internal theorem without the disjunction and convert it to the public API shape.

Useful comparison axes include proof length, upstream theorem reuse, API readability, duplication with the final `EuclideanDomain` instance, and portability to a generic quadratic order.

The contrast between A and C is especially useful for comparing a thin-lemma architecture with a bundled-certificate architecture.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The preceding 0228 source document records the next declaration exactly as:

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

Japanese and English PDFs exist on the target branch. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0230 `goldenEuclideanDomain`**.

It is a `noncomputable instance` constructing `EuclideanDomain GoldenInt` and registering the machinery prepared so far, including:

- `goldenQuotient`
- `goldenRemainder`
- `goldenEuclideanSize`
- `goldenQuotient_zero`
- `golden_quotient_mul_add_remainder`
- `golden_remainder_size_lt`
- `goldenEuclideanSize_mul`
- `goldenEuclideanSize_pos_of_ne_zero`

into Mathlib's Euclidean-domain typeclass fields.

If 0229 is the human-readable theorem-level package saying that Euclidean division exists, 0230 is the final integration point connecting the same mechanism to Lean's algebra hierarchy.
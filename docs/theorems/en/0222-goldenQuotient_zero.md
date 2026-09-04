# 0222 — `goldenQuotient_zero`

## Lean type

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

This is a `theorem` stating that the total quotient operation defined in 0220 `goldenQuotient` returns the golden integer `0` when the divisor is `0`.

## Mathematical statement and meaning of the declaration

Ordinary Euclidean division has no mathematical quotient for divisor `0`. However, the quotient operation required by Lean / Mathlib's `EuclideanDomain` API is a total function, so `goldenQuotient x 0` must still have a value.

The present implementation fixes that special value by proving

$$
goldenQuotient(x,0)=0.
$$

This follows naturally from 0219 `goldenQuotientCoords` and 0220 `goldenQuotient`. If `y=0`, then

$$
\overline{0}=0,
$$

hence

$$
x\overline{0}=0,
$$

and also

$$
N(0)=0.
$$

Thus both coordinates of `goldenQuotientCoords x 0` reduce to `0 / 0`. Rational division in Lean is totalized, with `0⁻¹=0`, so `0 / 0 = 0`. Finally `round 0 = 0`, and therefore the rounded golden quotient is also `0`.

The important point is that this theorem does **not** claim that division by zero is mathematically equal to zero in the ordinary partial-function sense. It records the **zero-divisor branch policy of the total Euclidean-domain quotient API**.

## Role in the full proof

`GoldenEuclidean.lean` constructs a concrete norm-Euclidean division algorithm and installs it into Mathlib's `EuclideanDomain` structure.

The relevant sequence is:

1. 0219 `goldenQuotientCoords` constructs rational quotient coordinates.
2. 0220 `goldenQuotient` rounds each coordinate to the nearest integer, producing a discrete quotient.
3. 0221 `goldenRemainder` defines

$$
r=x-qy.
$$

4. **0222 `goldenQuotient_zero` establishes the divisor-zero quotient law.**
5. Later declarations prove the division identity and strict remainder decrease.
6. The final `goldenEuclideanDomain` instance installs this theorem directly as

```lean
quotient_zero := goldenQuotient_zero
```

Therefore 0222 is not a norm-contraction theorem. It supplies the **boundary-condition law** required for the total quotient operation to satisfy the `EuclideanDomain` interface.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt`
- 0220 `goldenQuotient`
- 0219 `goldenQuotientCoords`
- 0216 `goldenQuotientNumerator`
- 0163 `goldenConj`
- 0124 `goldenMul`
- 0164 `goldenNorm`
- `GoldenInt.ext` and the projection simp API
- simp rules for `round 0`
- simp rules for total rational division

The theorem does not require 0215 `goldenNorm_ne_zero_of_ne_zero`. In fact, it handles precisely the opposite branch, namely `y=0`, and simply unfolds the totalized quotient definitions.

Conceptually,

$$
y=0
\Longrightarrow
x\overline y=0
\Longrightarrow
goldenQuotientCoords(x,y)=(0,0)
\Longrightarrow
round(0,0)=(0,0)
\Longrightarrow
goldenQuotient(x,0)=0.
$$

## Proof flow

The proof is a one-line tactic pipeline:

```lean
by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

### 1. Split the golden-integer equality into coordinates

The goal

```lean
goldenQuotient x 0 = 0
```

is reduced by `GoldenInt.ext` to equality of the first and second coordinates.

### 2. Unfold the quotient stack

The simplifier is given the definitions

- `goldenQuotient`
- `goldenQuotientCoords`
- `goldenQuotientNumerator`
- `goldenConj`
- `goldenMul`
- `goldenNorm`

so the divisor-zero computation is pushed all the way down to rational arithmetic.

### 3. Let `simp` discharge `0 / 0` and `round 0`

Because rational inverse is total in Lean, `0⁻¹=0`, hence `0/0=0`. The rounding simplification then gives `round 0 = 0`, closing both coordinate goals.

No `ring` or `field_simp` is needed. The zero branch is completed entirely by simplification.

## Lean-specific processing

### 1. Division by zero is still a well-typed term

Field division in Lean is total. Therefore an expression such as

```lean
(goldenQuotientNumerator x 0).fst / goldenNorm 0
```

is a normal well-typed term.

The reduction `0 / 0 = 0` comes from the algebraic convention `Inv.inv 0 = 0`; it is not a statement that mathematical partial division has been redefined conceptually.

### 2. `ext` exploits implementation transparency

`goldenQuotient` is built as a `GoldenInt` structure literal containing two rounded coordinates. Splitting the equality coordinatewise allows the simplifier to expose and normalize those two expressions directly.

### 3. No nonzero certificate is needed in the zero branch

For nonzero-divisor quotient identities, 0215

```lean
goldenNorm_ne_zero_of_ne_zero
```

is used to discharge denominator-nonzero obligations in `field_simp`. The present theorem instead uses the totalized zero branch directly, so no such certificate appears.

### 4. The theorem is implementation-sensitive

If `goldenQuotient` were defined explicitly by

```lean
if y = 0 then 0 else ...
```

then the theorem would likely reduce to a much shallower `simp [goldenQuotient]`. The current implementation instead derives the zero law from total rational division and coordinate rounding.

## Redundancy and duplication

The current proof unfolds a fairly deep implementation stack:

```lean
simp [goldenQuotient, goldenQuotientCoords,
  goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

This is locally short, but it hides the intermediate fact that the real core statement is

```lean
goldenQuotientCoords x 0 = (0, 0)
```

before rounding.

If more zero-divisor lemmas are added later, one could introduce a helper theorem such as

```lean
theorem goldenQuotientCoords_zero (x : GoldenInt) :
    goldenQuotientCoords x 0 = (0, 0) := ...
```

and derive 0222 from it. If 0222 remains the only consumer, the present one-shot simplification is reasonably lightweight.

## Optimization candidates

1. **Make the zero branch explicit in `goldenQuotient`**

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  if y = 0 then 0 else
    ⟨round ..., round ...⟩
```

This makes the zero law immediate, but may introduce `if` splitting into the nonzero branch proofs.

2. **Extract `goldenQuotientCoords_zero`**

This separates rational-coordinate zero normalization from the rounding step.

3. **Keep the current deep `simp` proof**

It is locally minimal and adds no extra API. If the zero branch is needed only once, this is likely the cheapest design.

4. **Move toward standard bundled algebra notation**

Reducing explicit raw `goldenMul` / `goldenConj` unfolding may shrink the simplifier surface if more of the arithmetic is exposed through standard morphism APIs.

5. **Abstract the zero policy for generic quadratic Euclidean division**

If the construction is generalized beyond the golden order, the pattern “total rational quotient + rounding implies quotient-zero law” may be reusable.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The Mathlib surface directly used by this theorem is mainly:

- the extensionality tactic `ext`
- the simplifier `simp`
- simp rules for rational division / inverse
- integer/rational rounding `round`
- product / structure projections

The theorem itself does not use `ring`, `field_simp`, or `nlinarith`.

The full `GoldenEuclidean.lean` module, however, also uses nearest-integer estimates, nonlinear inequalities, denominator clearing, and the Euclidean-domain hierarchy, so its actual minimal import set is much broader.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current deep `ext <;> simp [...]`
- B: a layered proof through `goldenQuotientCoords_zero`
- C: a `goldenQuotient` implementation with explicit `if y = 0 then 0`
- D: a quotient/remainder bundle carrying zero-branch specification certificates
- E: reuse a generic quadratic-order Euclidean quotient zero law

Useful comparison axes include:

- proof/source size
- simplifier unfolding depth
- robustness under implementation changes
- proof burden in zero and nonzero branches
- naturalness of integration with `EuclideanDomain`
- generalizability

The contrast between A and C is particularly clear: it compares relying on the default total-field zero behavior with making the zero policy explicit at the domain level.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

During this run, GitHub code search temporarily returned an upstream 502. Therefore the Lean type and proof of 0222 were also cross-checked against the complete source-order excerpt recorded in the preceding repository document 0221 `goldenRemainder`. The Japanese and English 0221 documents agree, and both 0222 target files were confirmed absent before selection.

The branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is the Euclidean quotient/remainder identity, **0223 `golden_quotient_mul_add_remainder`**.

The repository's preceding 0221 document records that the following source proves

$$
yq+r=x
$$

and installs that theorem as the `quotient_mul_add_remainder_eq` field of the final `EuclideanDomain` instance.

Now that 0222 closes the divisor-zero boundary condition, 0223 moves back to arbitrary `x,y` and rewrites the definition

$$
r=x-qy
$$

into the standard Euclidean division equation.

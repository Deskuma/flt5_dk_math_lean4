# 0201 — `goldenUnit_of_norm_eq_one_or_neg_one`

## Lean type

```lean
theorem goldenUnit_of_norm_eq_one_or_neg_one {x : GoldenInt}
    (h : goldenNorm x = 1 ∨ goldenNorm x = -1) : GoldenUnit x :=
  h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

This is a `theorem` stating that if the norm of a golden integer `x` is either `1` or `-1`, then `x` satisfies `GoldenUnit`, hence is a unit of the golden order.

## Mathematical statement

The statement is

$$
N(x)=1\ \lor\ N(x)=-1
\Longrightarrow
GoldenUnit(x).
$$

Declaration 0199 `goldenUnit_of_norm_eq_one` proves

$$
N(x)=1
\Longrightarrow
GoldenUnit(x)
$$

by constructing `goldenConj x` as an inverse.

Declaration 0200 `goldenUnit_of_norm_eq_neg_one` proves

$$
N(x)=-1
\Longrightarrow
GoldenUnit(x)
$$

by constructing the sign-corrected inverse `-goldenConj x`.

Declaration 0201 simply combines those two branches by elimination of the disjunction. No new algebraic calculation is introduced here.

## Role in the full proof

Declarations 0199 and 0200 explicitly construct the unit witness in the norm `1` and norm `-1` branches. The present theorem packages those two cases into a single public API, allowing downstream proofs to move from the compact condition

$$
N(x)=\pm1
$$

directly to unitness without knowing which inverse construction is used internally.

The immediately following theorem `goldenNorm_eq_one_or_neg_one_of_unit` proves the converse

$$
GoldenUnit(x)
\Longrightarrow
N(x)=1\ \lor\ N(x)=-1.
$$

Together, 0201 and that converse establish the golden-order unit criterion

$$
GoldenUnit(x)
\iff
N(x)=\pm1.
$$

This criterion feeds into `goldenUnit_phi`, `goldenUnit_one`, `goldenUnit_neg`, `goldenUnit_mul`, `goldenUnit_pow`, and ultimately the definition of `GoldenRelPrime`.

## Direct dependencies

The direct dependencies are minimal:

- 0198 `GoldenUnit`
- 0199 `goldenUnit_of_norm_eq_one`
- 0200 `goldenUnit_of_norm_eq_neg_one`
- `Or.elim`

Conceptually,

$$
\bigl(N(x)=1\to GoldenUnit(x)\bigr)
+
\bigl(N(x)=-1\to GoldenUnit(x)\bigr)
\Longrightarrow
\bigl(N(x)=1\lor N(x)=-1\bigr)\to GoldenUnit(x).
$$

The theorem itself does not directly use `goldenConj`, `goldenMul`, or norm multiplicativity; all of that algebraic work has already been encapsulated in 0199 and 0200.

## Proof flow

The proof is a single expression:

```lean
h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

The hypothesis is

```lean
h : goldenNorm x = 1 ∨ goldenNorm x = -1
```

so `Or.elim` requires one function for each branch:

```lean
goldenNorm x = 1  → GoldenUnit x

goldenNorm x = -1 → GoldenUnit x
```

Declarations 0199 and 0200 have exactly those shapes, so they can be supplied directly and the goal `GoldenUnit x` closes.

## Lean-specific processing

`h.elim` is method-style syntax for eliminating the disjunction represented by `h`.

From the expected target `GoldenUnit x` and the left/right types inside `h`, Lean implicitly specializes

```lean
goldenUnit_of_norm_eq_one
```

and

```lean
goldenUnit_of_norm_eq_neg_one
```

to the current `x`.

An expanded version of the same proof would be

```lean
by
  rcases h with h1 | hm1
  · exact goldenUnit_of_norm_eq_one h1
  · exact goldenUnit_of_norm_eq_neg_one hm1
```

The current implementation is simply the compact `Or.elim` form of that case split.

## Redundancy and duplication

There is essentially no internal duplication in 0201. Its purpose is precisely to merge the two separate branches already proved in 0199 and 0200.

At the API level, the three theorems

- `goldenUnit_of_norm_eq_one`
- `goldenUnit_of_norm_eq_neg_one`
- `goldenUnit_of_norm_eq_one_or_neg_one`

could appear somewhat fine-grained. However, the branch-specific theorems remain useful when the exact norm value is already known, because they avoid constructing an explicit disjunction.

Thus this is better viewed as layered API design—specific branch theorems plus a combined theorem—rather than unnecessary logical duplication.

## Optimization candidates

1. **Keep the current one-line proof**
   - it is already close to minimal and highly explicit about the logical structure.

2. **Expand to a `cases` proof**
   - this may be pedagogically clearer but increases code size.

3. **Publish the full bidirectional unit criterion**
   - together with the next theorem, expose

```lean
GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1
```

   as a rewrite-friendly API.

4. **Move toward Mathlib `IsUnit`**
   - connecting `GoldenUnit` with the standard unit predicate could improve generic algebra reuse.

5. **Bundle the norm as a multiplicative map**
   - this may make the unit/norm relation more structural and reduce bespoke lemmas later.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present theorem itself needs only a very small logical surface:

- `Or`
- `Or.elim`
- the branch theorems 0199 and 0200
- `GoldenUnit`

It does not directly use `ring`, `norm_num`, `rw`, or any advanced number-theory API.

The surrounding `GoldenDivisibility` module has broader dependencies because the upstream branch theorems use conjugation, norms, multiplication, and integer arithmetic. Therefore the minimal import set for the complete module is controlled by the surrounding development rather than by 0201 alone.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes, although the theorem is tiny. Possible variants include:

- A: current `h.elim ... ...`
- B: explicit `rcases h with h | h`
- C: automation such as a small `aesop`-style proof
- D: first build a bidirectional norm/unit criterion and reuse its forward direction
- E: formulate the result through Mathlib `IsUnit`

Useful comparison axes are proof-term size, readability, explicitness of branches, automation dependence, API reuse, and pedagogical transparency.

For this declaration, API-design comparison is more interesting than raw proof performance because the current implementation is already nearly minimal.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The preceding 0200 document identifies this theorem as the next declaration and records its Lean type. The target branch also contains Japanese and English PDFs, but the exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0202 `goldenNorm_eq_one_or_neg_one_of_unit`**:

```lean
theorem goldenNorm_eq_one_or_neg_one_of_unit {x : GoldenInt}
    (h : GoldenUnit x) : goldenNorm x = 1 ∨ goldenNorm x = -1 := by
  rcases h with ⟨y, hxy, _⟩
  have hn : goldenNorm x * goldenNorm y = 1 := by
    rw [← goldenNorm_mul, hxy]
    norm_num [goldenNorm, goldenOne]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

Declaration 0201 completes the direction from norm `±1` to unitness. Declaration 0202 proves the converse: from a unit witness it derives that the product of the two integer norms is `1`, then applies the integer fact that a factor of a product equal to `1` must be `±1`.
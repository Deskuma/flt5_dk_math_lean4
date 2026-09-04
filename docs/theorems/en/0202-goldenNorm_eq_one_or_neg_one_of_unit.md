# 0202 — `goldenNorm_eq_one_or_neg_one_of_unit`

## Lean type

```lean
theorem goldenNorm_eq_one_or_neg_one_of_unit {x : GoldenInt}
    (h : GoldenUnit x) : goldenNorm x = 1 ∨ goldenNorm x = -1 := by
  rcases h with ⟨y, hxy, _⟩
  have hn : goldenNorm x * goldenNorm y = 1 := by
    rw [← goldenNorm_mul, hxy]
    norm_num [goldenNorm, goldenOne]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

This is a `theorem` stating that if a golden integer `x` satisfies `GoldenUnit`, then its integer-valued norm is either `1` or `-1`.

## Mathematical statement

The theorem states

$$
GoldenUnit(x)\Longrightarrow N(x)=1\ \lor\ N(x)=-1.
$$

`GoldenUnit x` means that there exists `y : GoldenInt` such that

$$
xy=1,\qquad yx=1.
$$

Using norm multiplicativity from 0174 `goldenNorm_mul`, one obtains

$$
N(x)N(y)=N(xy)=N(1)=1.
$$

Since both norms are integers, an integer product equal to `1` forces each factor to be `1` or `-1`. In particular,

$$
N(x)=\pm1.
$$

Declaration 0201 `goldenUnit_of_norm_eq_one_or_neg_one` proves the converse direction

$$
N(x)=\pm1\Longrightarrow GoldenUnit(x),
$$

so 0201 and 0202 together complete the golden-order unit criterion

$$
GoldenUnit(x)\iff N(x)=\pm1.
$$

## Role in the full proof

Declarations 0198–0202 form the unit-by-norm block.

- 0198 `GoldenUnit` defines a unit by the existence of a two-sided inverse.
- 0199 `goldenUnit_of_norm_eq_one` proves that norm `1` implies unitness.
- 0200 `goldenUnit_of_norm_eq_neg_one` proves that norm `-1` implies unitness.
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one` combines the two branches into the implication `N(x)=±1 → GoldenUnit(x)`.
- 0202 proves the converse implication from unitness to norm `±1`.

This converse lets later closure arguments for units be transported to integer arithmetic on norms. For results such as `goldenUnit_neg` and `goldenUnit_mul`, a unit hypothesis can first be projected to the discrete condition `N=±1`, manipulated on the integer side, and converted back to `GoldenUnit` using 0201.

The criterion also matters for the later definition of `GoldenRelPrime`, where every common divisor must be shown to be a unit. Thus the present theorem is an important bridge from golden divisibility to ordinary integer arithmetic through the norm.

## Direct dependencies

The direct dependencies are:

- 0198 `GoldenUnit`
- 0174 `goldenNorm_mul`
- `goldenOne`
- `goldenNorm`
- `Int.eq_one_or_neg_one_of_mul_eq_one`
- `norm_num`

The proof uses only one side of the two-sided inverse witness supplied by `GoldenUnit`. Although `GoldenUnit` stores both `xy=1` and `yx=1`, one product equality is enough to derive the norm equation.

Conceptually,

$$
GoldenUnit(x)\Longrightarrow \exists y,\ xy=1\Longrightarrow N(x)N(y)=1\Longrightarrow N(x)=\pm1.
$$

## Proof flow

### 1. Extract the unit witness

```lean
rcases h with ⟨y, hxy, _⟩
```

From `GoldenUnit x`, Lean extracts an inverse candidate `y` and

```lean
hxy : goldenMul x y = goldenOne.
```

The opposite multiplication equality is not needed in this proof, so it is discarded with `_`.

### 2. Prove that the product of norms is `1`

```lean
have hn : goldenNorm x * goldenNorm y = 1 := by
  rw [← goldenNorm_mul, hxy]
  norm_num [goldenNorm, goldenOne]
```

The reverse use of `goldenNorm_mul` turns `N(x)N(y)` back into `N(xy)`. Then `hxy` rewrites `xy` to `1`, and `norm_num` computes the norm of `goldenOne`.

### 3. Classify the integer factor

```lean
exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

The integer theorem applied to `hn` yields that `goldenNorm x` is `1` or `-1`.

## Lean-specific processing

`rcases h with ⟨y, hxy, _⟩` simultaneously eliminates the existential witness and the conjunction in

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

The final `_` intentionally discards the second inverse equality.

The rewrite

```lean
rw [← goldenNorm_mul, hxy]
```

uses `goldenNorm_mul` in the reverse direction. The current expression is the integer product `goldenNorm x * goldenNorm y`, while the available unit witness concerns `goldenMul x y`. Reversing norm multiplicativity reconstructs exactly the expression on which `hxy` can act.

The final theorem `Int.eq_one_or_neg_one_of_mul_eq_one` uses the fact that the norm lands specifically in `ℤ`. The conclusion is a discrete integer classification rather than a generic integral-domain unit statement.

## Redundancy and duplication

Declarations 0201 and 0202 are converse theorems and can naturally be packaged into a single equivalence:

```lean
GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1
```

Publishing that equivalence would make the unit criterion directly rewriteable by downstream code.

There is also structural redundancy in `GoldenUnit`: it stores two multiplication equalities, while the present theorem needs only one. Since `GoldenInt` is already commutative, a one-sided inverse would mathematically suffice. This redundancy comes from the explicit raw bootstrap design.

The norm of `1` is recomputed by `norm_num [goldenNorm, goldenOne]`; a dedicated simp theorem such as `goldenNorm_one` could remove repeated closed-coordinate calculations if the pattern appears often enough downstream.

## Optimization candidates

1. Package 0201 and 0202 as `GoldenUnit x ↔ N(x)=±1`.
2. Connect `GoldenUnit` to Mathlib `IsUnit` with a bridge theorem.
3. Bundle `goldenNorm` as a multiplicative map and reuse generic unit-image lemmas.
4. Publish `goldenNorm_one` as a simp theorem.
5. Compare the current two-sided-inverse API with a one-sided formulation in the commutative ring.

The current proof is already short and makes the integer-norm projection explicit, so local proof compression is not a high-priority optimization.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface used by this theorem is mainly:

- `Int.eq_one_or_neg_one_of_mul_eq_one`
- `norm_num`
- existential and conjunction elimination
- equality rewriting

The theorem itself should require much less than the whole of `Mathlib`, but the surrounding `GoldenDivisibility.lean` module also uses integer divisibility, conjugation, norm arithmetic, and ring tactics. Therefore import minimization must be measured at module scope.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful variants include:

- A: current witness extraction + `goldenNorm_mul` + integer classification lemma
- B: a generic proof through Mathlib `IsUnit`
- C: bundle `goldenNorm` as a multiplicative map and derive the result from the image of a unit
- D: redesign 0201/0202 around one bidirectional unit criterion
- E: reformulate `GoldenUnit` using only one inverse equation

Useful comparison axes are proof size, dependency depth, reuse of standard Mathlib APIs, mathematical transparency, compatibility with the explicit-coordinate layer, and downstream rewrite ergonomics.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository's 0201 Japanese document records this declaration and proof as the next item in source order. This run also confirmed that neither Japanese nor English 0202 existed before selecting it.

Japanese and English PDFs exist on the target branch, but the exact page or section corresponding to this theorem was not directly identified in this run, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0203 `goldenUnit_phi`**:

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

By 0202, the equivalence between unitness and norm `±1` has been completed in both directions. Declaration 0203 begins applying that criterion to concrete golden integers, starting with the generator `φ` itself.

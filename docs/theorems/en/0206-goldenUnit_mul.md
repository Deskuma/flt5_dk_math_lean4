# 0206 — `goldenUnit_mul`

## Lean type

```lean
theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [goldenNorm_mul]
  rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
    rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
    simp [hx', hy']
```

This is a `theorem` stating that if two golden integers `x` and `y` satisfy `GoldenUnit`, then their product `goldenMul x y` also satisfies `GoldenUnit`.

## Mathematical statement and meaning of the declaration

The statement is the ordinary closure of units under multiplication:

$$
GoldenUnit(x)\land GoldenUnit(y)
\Longrightarrow
GoldenUnit(xy).
$$

The current proof does not construct the inverse of the product directly. Instead, it uses the unit criterion developed in declarations 0198–0202.

If `x` and `y` are units, declaration 0202 `goldenNorm_eq_one_or_neg_one_of_unit` gives

$$
N(x)\in\{1,-1\},\qquad N(y)\in\{1,-1\}.
$$

By norm multiplicativity from 0174 `goldenNorm_mul`,

$$
N(xy)=N(x)N(y).
$$

The product of two values in `±1` is again `±1`, so 0201 `goldenUnit_of_norm_eq_one_or_neg_one` converts that norm condition back into unitness of the product.

The four sign combinations are

$$
1\cdot1=1,\qquad
1\cdot(-1)=-1,\qquad
(-1)\cdot1=-1,\qquad
(-1)\cdot(-1)=1,
$$

and Lean's final `simp` discharges these finite cases.

## Role in the full proof

Declarations 0205–0207 form the elementary closure block for `GoldenUnit`.

- 0205 `goldenUnit_neg` — negation preserves unitness.
- 0206, the present theorem — multiplication preserves unitness.
- 0207 `goldenUnit_pow` — natural powers preserve unitness.

In particular, 0207 uses this theorem directly in its successor case:

```lean
| succ n ih => exact goldenUnit_mul ih hx
```

Thus 0206 is not merely a restatement of a generic ring fact. It supplies the recursive multiplication step that transports the custom `GoldenUnit` predicate to arbitrary powers, including the fifth powers that are central to the FLT5 development.

Later parts of the proof combine unit factors with fifth powers and unit-class representatives, so multiplicative and power closure are basic infrastructure for the golden factorization layer.

## Direct dependencies

The current proof directly relies on:

- 0198 `GoldenUnit`
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- 0202 `goldenNorm_eq_one_or_neg_one_of_unit`
- 0174 `goldenNorm_mul`
- 0124 `goldenMul`
- `simp`

Conceptually, the dependency chain is

$$
GoldenUnit(x),GoldenUnit(y)
\Longrightarrow
N(x),N(y)\in\{\pm1\}
\Longrightarrow
N(xy)=N(x)N(y)\in\{\pm1\}
\Longrightarrow
GoldenUnit(xy).
$$

## Proof flow

The proof has three stages.

### 1. Move the unit goal to the norm criterion

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
```

This changes the goal to

```lean
goldenNorm (goldenMul x y) = 1 ∨
  goldenNorm (goldenMul x y) = -1
```

### 2. Rewrite the norm of the product

```lean
rw [goldenNorm_mul]
```

The target becomes

```lean
goldenNorm x * goldenNorm y = 1 ∨
  goldenNorm x * goldenNorm y = -1
```

### 3. Split the two unit hypotheses into the four `±1` cases

```lean
rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
  rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
  simp [hx', hy']
```

Each unit hypothesis is converted to a two-way norm alternative. Together they generate four goals, all of which are solved by evaluating the corresponding sign product with `simp`.

## Lean-specific processing

The distinctive Lean feature is the nested use of `rcases` together with the `<;>` tactical sequencer:

```lean
rcases ... hx with hx' | hx' <;>
  rcases ... hy with hy' | hy' <;>
  simp [hx', hy']
```

The first `rcases` creates two goals, and `<;>` applies the second `rcases` to both. Each of those goals splits again, producing four branches. The final `simp` is then applied to every branch.

The same branch-local names `hx'` and `hy'` can be reused, avoiding an explicit four-case proof.

Also, `rw [goldenNorm_mul]` applies directly because the norm theorem is stated for the raw multiplication `goldenMul`. No `change` through standard `x * y` notation is needed here.

## Redundancy and duplication

Mathematically, closure of units under multiplication is generic ring theory. Once `GoldenUnit` is connected to Mathlib's `IsUnit`, a golden-specific proof could likely be delegated to the standard unit API.

The current proof also expands the two `±1` alternatives into four branches. This is very small and transparent, but logically it is just the closure of the set `{1,-1}` under integer multiplication.

Another structural duplication is that 0201 and 0202 together already amount to

$$
GoldenUnit(x)\iff N(x)=1\lor N(x)=-1,
$$

but that equivalence has not yet been packaged as a single named theorem. Exposing it could make later closure arguments more uniform.

A different proof architecture could avoid norms entirely: destruct the inverse witnesses for `x` and `y`, multiply the inverse candidates, and prove directly that the resulting element is an inverse of `xy`. Since `GoldenInt` is commutative, the ordering issues are mild.

## Optimization candidates

1. **Keep the current norm-based proof**
   - it is short and clearly reuses the unit criterion and norm multiplicativity.

2. **Construct the inverse witness directly**
   - extract inverse witnesses from `hx` and `hy` and use their product as the inverse of `xy`;
   - avoids the four norm-sign cases.

3. **Publish the unit criterion as an iff theorem**
   - expose `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` for direct rewriting or simp.

4. **Move the `GoldenUnit ↔ IsUnit` bridge earlier**
   - generic Mathlib closure of units under multiplication could replace this custom proof.

5. **Bundle `goldenNorm` as a multiplicative map**
   - `goldenNorm_mul`, `goldenNorm_pow`, and unit arguments could then use a more general morphism API.

6. **Factor out closure of `±1` under multiplication**
   - useful if the same sign split occurs repeatedly, although for this single theorem the current `simp` is probably simpler than another abstraction layer.

Locally, the present proof is already efficient; the larger optimization opportunities concern API bundling around `GoldenUnit` and the norm.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface used by this theorem is mainly:

- `rcases`
- `<;>` tactical sequencing
- `simp`
- equality rewriting

The theorem itself does not directly use heavier arithmetic tactics such as `ring` or `norm_num`; the unit criterion and norm multiplicativity have already encapsulated those earlier calculations.

The surrounding `GoldenDivisibility.lean` module does use integer divisibility, `Int.eq_one_or_neg_one_of_mul_eq_one`, `norm_num`, and ring arithmetic, so the real minimal import set must be measured at module scope rather than from 0206 alone.

No Lean build is run in this museum pass, so the exact minimal imports remain unverified and are recorded only as optimization candidates.

## Comparator challenge suitability

Yes. Useful competitors include:

- A: the current four-case norm `±1` proof
- B: direct multiplication of inverse witnesses
- C: a unit-criterion iff plus simp
- D: the `GoldenUnit ↔ IsUnit` bridge plus generic Mathlib unit API
- E: an abstract proof using a bundled multiplicative norm

Useful comparison axes are proof size, number of case splits, direct dependency depth, reuse of standard Mathlib APIs, visibility of mathematical provenance, dependence on the explicit coordinate layer, and robustness under refactoring.

The contrast between A and B is especially instructive: A makes the norm `±1` criterion the central interface for units, while B works directly with inverse witnesses.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The current source places this theorem immediately after 0205 `goldenUnit_neg` and immediately before 0207 `goldenUnit_pow`.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified directly in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0207 `goldenUnit_pow`**:

```lean
theorem goldenUnit_pow {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (goldenPow x n) := by
  induction n with
  | zero => exact goldenUnit_one
  | succ n ih => exact goldenUnit_mul ih hx
```

Declaration 0204 `goldenUnit_one` supplies the zero-power base case, while 0206 supplies the multiplicative successor step. Therefore 0207 proves that every natural power of a unit, in particular its fifth power, remains a unit.
# 0198 — `GoldenUnit`

## Lean type

```lean
/-- A two-sided unit in the coordinate order.  Later theorems identify this predicate
with Mathlib's `IsUnit` and with norm `±1`. -/
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

This is a `def`, not a theorem. It defines a domain-specific predicate expressing that a golden integer `epsilon` has a two-sided inverse.

## Mathematical statement and meaning of the declaration

`GoldenUnit ε` means that there exists a golden integer `η` such that

$$
\varepsilon\eta=1,
\qquad
\eta\varepsilon=1.
$$

Thus, mathematically, it states that `ε` is a unit of the ring $\mathbb Z[\varphi]$, expressed entirely through the raw coordinate API.

`GoldenInt` has already been constructed as a commutative ring, so in this specific setting one-sided invertibility would imply the other side. The definition nevertheless records both equations explicitly. This keeps the predicate close to a general monoid-style notion of a unit while remaining readable using only `goldenMul` and `goldenOne`.

## Role in the full proof

Declarations 0187–0197 establish golden divisibility together with compatibility of conjugation, norm, and powers. With 0198 the development enters the block that converts norm information into invertibility.

The source immediately continues with:

- `goldenUnit_of_norm_eq_one`
- `goldenUnit_of_norm_eq_neg_one`
- `goldenUnit_of_norm_eq_one_or_neg_one`
- `goldenNorm_eq_one_or_neg_one_of_unit`

These results build the standard unit criterion in the golden order:

$$
GoldenUnit(x)
\iff
N(x)=1\ \text{or}\ N(x)=-1.
$$

The following lemmas `goldenUnit_phi`, `goldenUnit_one`, `goldenUnit_neg`, `goldenUnit_mul`, and `goldenUnit_pow` provide closure properties. Finally `GoldenRelPrime` is defined by

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

so `GoldenUnit` becomes the primitive vocabulary for the Bézout-free statement that every common divisor is a unit.

## Direct dependencies

Because this declaration is a definition, it has no direct theorem dependency. Its immediate definitions are:

- `GoldenInt`
- 0124 `goldenMul`
- `goldenOne`
- Lean's existential proposition `∃`

Conceptually,

$$
\texttt{GoldenInt}
+\texttt{goldenMul}
+\texttt{goldenOne}
\longrightarrow
\texttt{GoldenUnit}.
$$

The following theorems use 0176 `golden_mul_conj` and norm calculations to construct the inverse witness `eta` explicitly.

## Construction flow

The definition packages two inverse equations into one existential statement:

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

1. Require an inverse candidate `eta : GoldenInt`.
2. Require `epsilon * eta = 1`.
3. Require `eta * epsilon = 1`.

Given a hypothesis

```lean
h : GoldenUnit epsilon
```

a downstream proof can recover the witness and both identities with a pattern such as

```lean
rcases h with ⟨eta, hleft, hright⟩
```

## Lean-specific processing

`GoldenUnit epsilon : Prop` is an existential proposition rather than a structure carrying inverse data. The inverse witness is extracted from a proof only when needed.

The statement deliberately uses raw `goldenMul` instead of standard `*`, and raw `goldenOne` instead of standard `1`. These operations are definitionally connected to the `Mul` and `One` instances on `GoldenInt`, so interoperability with Mathlib's standard algebra API can usually be handled by light `simpa` or `change` steps.

The source comment says that later theorems identify this predicate with Mathlib's `IsUnit` and with norm `±1`. In the immediately verified source region, the norm-`±1` characterization is developed directly after this definition.

## Redundancy and duplication

Mathematically, `GoldenUnit` overlaps with Mathlib's standard `IsUnit epsilon`. It is another domain-specific wrapper similar in spirit to `GoldenDivides`.

There are nevertheless practical reasons to keep it. The predicate can be read entirely in the explicit coordinate layer, theorem names make the intended golden-order semantics obvious, and `GoldenRelPrime` can state relative primality directly as “every common golden divisor is a `GoldenUnit`.” This can improve auditability of the FLT5 argument.

There is also deliberate logical redundancy in requiring both left and right inverse equations even though `GoldenInt` is commutative. The symmetric definition favors explicitness and general algebraic shape over minimality.

## Optimization candidates

1. **Keep the current wrapper**
   - preserves raw-coordinate auditability and domain-specific theorem names.

2. **Use only Mathlib's `IsUnit`**
   - may allow more downstream lemmas to be replaced by generic unit API.

3. **Make `GoldenUnit` a thin alias/bridge to `IsUnit`**
   - retain the domain-specific name while moving implementation responsibility to the standard algebra layer.

4. **Require only one inverse equation**
   - shorter under the already available commutative-ring structure, but less symmetric as a raw API definition.

5. **Store inverse data in a structure**
   - potentially useful if the explicit inverse witness becomes persistent computational data, but probably unnecessary for the present Prop-oriented proof layer.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This definition by itself only needs `GoldenInt`, `goldenMul`, `goldenOne`, and basic existential syntax. It does not directly require advanced tactics or number-theory libraries.

The surrounding `GoldenDivisibility` section soon uses `IsUnit`, integer norms, divisibility, `norm_num`, and `simp`, so the minimal import set for the full module is necessarily broader than the surface needed by 0198 alone. No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. Natural variants are:

- A: current existential `GoldenUnit` wrapper
- B: use Mathlib `IsUnit` everywhere
- C: thin domain-specific alias plus bridge theorems
- D: a structure carrying explicit inverse data
- E: a one-sided inverse definition specialized to the commutative setting

Useful metrics include downstream theorem size, reuse of Mathlib's standard unit API, visibility of the raw/standard algebra boundary, auditability, convenience of inverse witnesses, and refactor robustness.

The A-versus-B comparison is especially similar to the earlier `GoldenDivides` design question: it measures how much value a domain-specific wrapper contributes to readability of the formal FLT5 proof.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In the verified source order, 0197 `goldenNorm_pow` is immediately followed by this definition, and `goldenUnit_of_norm_eq_one` follows immediately afterward.

The branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0199 `goldenUnit_of_norm_eq_one`**:

```lean
theorem goldenUnit_of_norm_eq_one {x : GoldenInt} (h : goldenNorm x = 1) :
    GoldenUnit x := by
  refine ⟨goldenConj x, ?_, ?_⟩
  · simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
  · have hc : goldenMul (goldenConj x) x =
        goldenMul x (goldenConj x) := by
      change goldenConj x * x = x * goldenConj x
      exact mul_comm _ _
    rw [hc]
    simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

After 0198 defines unitness as the existence of a two-sided inverse, 0199 shows that if `N(x)=1`, then the conjugate `goldenConj x` supplies that inverse explicitly. This begins the conversion between norm `±1` and unit status.
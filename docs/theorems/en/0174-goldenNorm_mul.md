# 0174 — `goldenNorm_mul`

## Lean type

```lean
/-- The golden norm is multiplicative. -/
theorem goldenNorm_mul (x y : GoldenInt) :
    goldenNorm (goldenMul x y) = goldenNorm x * goldenNorm y := by
  simp [goldenNorm, goldenMul]
  ring
```

This is a `theorem` stating that the explicit norm `goldenNorm` on the golden-integer ring `GoldenInt` is multiplicative with respect to the explicit multiplication `goldenMul`.

## Mathematical statement and meaning of the declaration

Write

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

with $\varphi^2=\varphi+1$. The norm is defined by

$$
N(a+b\varphi)=a^2+ab-b^2.
$$

The coordinate multiplication `goldenMul` implements

$$
xy=(ac+bd)+(ad+bc+bd)\varphi.
$$

The theorem proves the fundamental multiplicativity law

$$
N(xy)=N(x)N(y).
$$

Unlike declarations 0172–0173, which were representation bridges, this theorem establishes a substantive algebraic property: `goldenNorm` is not merely an integer-valued quadratic form, but a **multiplicative invariant** compatible with the ring product.

## Role in the overall proof

This theorem becomes one of the central bridges in the later golden-integer part of the FLT5 proof.

Together with the following results `goldenNorm_conj` and `golden_mul_conj`, it completes the basic interaction between multiplication, conjugation, and norm in the quadratic order.

More concretely, the subsequent `GoldenDivisibility.lean` section uses this theorem directly in

```lean
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

so golden divisibility is transported to ordinary integer divisibility of norms.

The theorem is also reused by `goldenNorm_pow` to prove

$$
N(x^n)=N(x)^n,
$$

and by later unit arguments that convert a multiplicative inverse equation into an integer equation involving a product of norms.

Conceptually,

```text
GoldenInt multiplication
      │
      ▼
goldenNorm_mul
      │
      ├─ divisibility → integer divisibility
      ├─ powers → norm powers
      └─ units → norm ±1
```

so 0174 is a shared foundation for several downstream proof paths.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenMul`
- `goldenNorm`
- the `simp` simplifier for unfolding and reducing coordinate projections
- the `ring` tactic for closing the resulting polynomial identity over `ℤ`

Declarations 0172 `goldenNorm_eq_GoldenNorm` and 0173 `goldenNorm_eq_existing_GoldenNorm` are closely related conceptually, but are not invoked by this proof.

Likewise, `goldenConj` is not used here. The implementation does not derive multiplicativity from the abstract identity $N(x)=x\overline{x}$; instead it proves the result directly from explicit coordinates.

## Proof / construction flow

The proof has two steps:

```lean
simp [goldenNorm, goldenMul]
ring
```

After unfolding multiplication and norm, if we abbreviate $x=(a,b)$ and $y=(c,d)$, the left-hand side becomes

$$
(ac+bd)^2+(ac+bd)(ad+bc+bd)-(ad+bc+bd)^2,
$$

while the right-hand side becomes

$$
(a^2+ab-b^2)(c^2+cd-d^2).
$$

`simp` removes the structure-level wrappers and exposes the integer polynomial expressions. `ring` then normalizes both sides in the commutative ring `ℤ` and proves that their normal forms coincide.

The conceptual proof flow is therefore

```text
N(goldenMul x y)
→ unfold coordinate multiplication
→ integer polynomial

N(x) * N(y)
→ unfold norm
→ integer polynomial

→ identical ring normal forms
```

## Lean-specific processing

The key Lean-specific point is that after

```lean
simp [goldenNorm, goldenMul]
```

the goal lies entirely in integer polynomial arithmetic, exactly the setting where `ring` is strongest.

No abstract quadratic-algebra norm API or ring homomorphism is required. This keeps the proof short and highly transparent at the representation level, although the mathematical reason for multiplicativity is delegated to polynomial normalization rather than expressed structurally.

The theorem statement also deliberately uses the raw API

```lean
goldenNorm (goldenMul x y)
```

rather than standard notation `goldenNorm (x * y)`. Since `golden_mul_eq` is already available, a standard-notation variant would be easy to derive, but the current source keeps the explicit coordinate API visible.

## Redundancy and duplication

There are two main design-level duplication candidates.

1. The theorem is stated for raw `goldenMul`, while `golden_mul_eq` already identifies `goldenMul x y` with `x * y`.
2. In a more structural development, multiplicativity could potentially be derived from multiplicativity of conjugation together with the identity relating an element times its conjugate to the embedded norm.

However, in the current source order `goldenNorm_mul` appears before `golden_mul_conj`, so deriving it from the latter would require reorganizing dependencies.

Downstream, the theorem is reused well: `goldenNorm_pow`, norm-divisibility, and unit results do not reprove multiplicativity independently.

## Optimization candidates

Possible designs include:

1. keep the current explicit-coordinate proof using `simp` and `ring`;
2. expose a standard-notation companion theorem

```lean
theorem goldenNorm_mul' (x y : GoldenInt) :
    goldenNorm (x * y) = goldenNorm x * goldenNorm y := by
  ...
```

and retain the raw theorem as a compatibility bridge;
3. bundle `goldenConj` as a `RingEquiv` and define norm through the product with conjugation, deriving multiplicativity structurally;
4. use an `AdjoinRoot (X^2-X-1)` or generic quadratic-algebra norm theorem;
5. define `goldenNorm` as a wrapper around `GoldenNorm x.fst x.snd` and share a multiplicativity theorem from the earlier binary quadratic-form layer.

The local proof is already very short. The interesting optimization question is therefore not tactic length, but API coherence and generalizability.

## Required Mathlib imports and import optimization

This theorem directly uses `simp` and `ring`.

A reduced import set would therefore need basic integer algebra, simplification, and ring normalization. The broad standalone `import Mathlib` is almost certainly more than this single theorem needs.

At module level, however, `GoldenOrder.lean` also uses `Zsqrtd`, `omega`, `norm_num`, `interval_cases`, and substantial algebraic typeclass infrastructure. Any exact import minimization must therefore be validated for the whole module with Lean. No Lean build is performed in this museum run, so no precise minimal import list is claimed.

## Comparator challenge suitability

Yes.

Useful implementation candidates are:

- explicit coordinate expansion followed by `ring`;
- a structural proof through conjugation and element-times-conjugate identities;
- a bundled `RingHom` / `RingEquiv` plus norm map;
- reuse of a generic `AdjoinRoot` or quadratic-algebra norm multiplicativity theorem.

Comparison criteria include proof-term size, simplifier dependence, definitional transparency, generalizability, and ergonomics for downstream divisibility, unit, and Euclidean-domain arguments.

The current implementation is especially easy to audit at the coordinate level, whereas the more abstract implementations offer stronger reuse. That trade-off makes 0174 a good Comparator challenge.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following 0174 in the Lean source is

```lean
/-- Conjugation preserves the golden norm. -/
theorem goldenNorm_conj (x : GoldenInt) :
    goldenNorm (goldenConj x) = goldenNorm x := by
  simp [goldenNorm, goldenConj]
  ring
```

Therefore the next museum entry is **0175 `goldenNorm_conj`**.

After 0174 establishes multiplicativity $N(xy)=N(x)N(y)$, 0175 proves the second fundamental norm law,

$$
N(\overline{x})=N(x),
$$

showing that quadratic conjugation preserves the norm.

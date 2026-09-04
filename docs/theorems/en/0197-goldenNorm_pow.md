# 0197 — `goldenNorm_pow`

## Lean type

```lean
theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]
```

This is a `theorem` stating that the golden norm `goldenNorm` preserves natural powers.

## Mathematical statement

For every golden integer $x\in\mathbb Z[\varphi]$ and every natural number $n$,

$$
N(x^n)=N(x)^n.
$$

Declaration 0174 `goldenNorm_mul` has already established

$$
N(xy)=N(x)N(y),
$$

so the present theorem is the inductive extension of norm multiplicativity to natural powers.

Since fifth powers are central in FLT5, the special case

$$
N(x^5)=N(x)^5
$$

is particularly important.

## Role in the full proof

In `GoldenDivisibility.lean`, declaration 0196 `goldenConj_pow` first establishes compatibility between conjugation and powers. The present theorem then establishes the corresponding power law for the norm.

This allows an internal fifth-power relation in the golden order to be projected to an ordinary fifth-power relation in the integers. For example, a relation of the form

$$
x=y^5
$$

can be transported to

$$
N(x)=N(y)^5.
$$

Together with 0174 `goldenNorm_mul` and 0192 `goldenNorm_dvd_of_goldenDivides`, this makes `goldenNorm` a central interface carrying multiplicative and divisibility information from `GoldenInt` into `ℤ`. The present theorem completes the power-compatible part of that interface.

## Direct dependencies

The proof directly uses:

- 0174 `goldenNorm_mul`
- the standard theorem `pow_succ`
- natural-number induction
- the induction hypothesis `ih`
- `norm_num` in the base case

At the type and operation level it depends on:

- `GoldenInt`
- 0164 `goldenNorm`
- 0124 `goldenMul`
- standard natural powers supplied by the `CommRing GoldenInt` structure

Conceptually,

$$
\texttt{goldenNorm\_mul}
+\text{natural-number induction}
\longrightarrow
\texttt{goldenNorm\_pow}.
$$

## Proof flow

The proof is induction on $n$.

### Base case $n=0$

```lean
| zero => norm_num [goldenNorm]
```

Mathematically,

$$
N(x^0)=N(1)=1=N(x)^0.
$$

The unit of `GoldenInt` has coordinates `⟨1,0⟩`, so unfolding `goldenNorm` gives the integer value `1`. The proof uses `norm_num [goldenNorm]` to normalize the zero power and the explicit quadratic form together.

### Inductive step $n\mapsto n+1$

```lean
| succ n ih =>
    rw [pow_succ]
    change goldenNorm (goldenMul (x ^ n) x) = _
    rw [goldenNorm_mul, ih, pow_succ]
```

1. Use `pow_succ` to rewrite $x^{n+1}$ as $x^n x$.
2. Use `change` to expose standard multiplication as the raw operation `goldenMul`.
3. Apply `goldenNorm_mul` to obtain

$$
N(x^n x)=N(x^n)N(x).
$$

4. Apply the induction hypothesis to replace $N(x^n)$ by $N(x)^n$.
5. Rewrite the target integer power using `pow_succ`.

Thus the theorem is the explicit induction proof of the generic principle that a multiplicative map preserves natural powers.

## Lean-specific processing

The characteristic representation step is

```lean
change goldenNorm (goldenMul (x ^ n) x) = _
```

After `pow_succ`, Lean exposes the standard multiplication `x ^ n * x`. Declaration 0174 `goldenNorm_mul`, however, is stated using the raw operation `goldenMul`.

The registered `Mul GoldenInt` instance is definitionally implemented by `goldenMul`, so the two expressions are definitionally connected. `change` is used only to present the goal in the form expected by the existing theorem.

The final line

```lean
rw [goldenNorm_mul, ih, pow_succ]
```

then chains norm multiplicativity, the induction hypothesis, and the successor law for integer powers.

Compared with 0196 `goldenConj_pow`, there is no final conversion back from raw multiplication on the codomain side: `goldenNorm` lands in `ℤ`, so the right-hand side is already ordinary integer multiplication and exponentiation.

## Redundancy and duplication

Mathematically, this theorem is a generic consequence of 0174 `goldenNorm_mul`, so it contains little independent information.

If `goldenNorm` were bundled as an appropriate multiplicative morphism, a generic `map_pow` theorem could likely provide this result automatically. In that sense, the explicit induction duplicates a standard algebraic pattern.

However, `goldenNorm : GoldenInt → ℤ` is not a ring homomorphism because it does not preserve addition. The relevant abstraction would be a multiplicative map preserving `1`, such as a `MonoidHom`-style interface.

The current theorem avoids introducing that abstraction and exposes exactly the power law needed by the FLT5 development. This keeps the local dependency surface small and audit-friendly.

## Optimization candidates

1. **Keep the current induction proof**
   - shallow dependencies and a transparent derivation from 0174.

2. **Bundle the norm as a multiplicative morphism**
   - package preservation of `1` and multiplication into a `MonoidHom`-style API and obtain power preservation generically.
   - such a bundle might also simplify later unit and divisibility arguments.

3. **Prove the result first for raw `goldenPow`**
   - induct on the explicit recursive power operation, then connect to standard powers using 0160 `golden_pow_eq`.

4. **Provide `goldenNorm_mul` in standard notation**
   - a theorem `goldenNorm (x * y) = goldenNorm x * goldenNorm y` could remove the explicit `change` step.

5. **Revisit the base-case tactic**
   - `norm_num [goldenNorm]` is clear, but `simp [goldenNorm]` or even a more definitional proof might be possible. This is unverified because no Lean build is run in this museum pass.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface used by this theorem includes:

- natural-number induction
- `pow_succ`
- rewriting
- `change`
- `norm_num`
- multiplication and powers on `GoldenInt`
- `goldenNorm_mul`

The theorem itself does not directly use `ring` or divisibility tactics. The proof of `goldenNorm_mul` upstream does use polynomial normalization, and the surrounding module also develops divisibility and units, so the true minimal import set for the entire module is broader.

Because no Lean build is performed here, the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementations to compare include:

- A: the current explicit natural-number induction
- B: bundle `goldenNorm` as a multiplicative `MonoidHom` and use generic `map_pow`
- C: induct over raw `goldenPow` and finish with `golden_pow_eq`
- D: first provide standard-notation norm multiplicativity and eliminate `change`
- E: shorten the tactic proof around `simp` / `simpa`

Comparison axes include proof length, abstraction cost, exposure of the raw/standard API boundary, downstream reuse, Mathlib dependency, and robustness under refactoring.

The contrast between A and B is especially useful for evaluating how much abstraction a norm API should carry in an explicit-coordinate formalization.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0196 and immediately before `GoldenUnit`:

```lean
theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]

/-- A two-sided unit in the coordinate order.  Later theorems identify this predicate
with Mathlib's `IsUnit` and with norm `±1`. -/
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0198 `GoldenUnit`**:

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

By 0197, compatibility of conjugation and the norm with powers is in place. Declaration 0198 begins the next block by defining a two-sided unit in the explicit coordinate API, after which unit status is related to norm `±1`.
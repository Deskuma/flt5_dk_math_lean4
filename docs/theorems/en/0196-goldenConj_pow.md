# 0196 — `goldenConj_pow`

## Lean type

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]
```

This is a `theorem` stating that golden conjugation `goldenConj` preserves natural powers.

## Mathematical statement

For every golden integer $x\in\mathbb Z[\varphi]$ and every natural number $n$,

$$
\overline{x^n}=\overline{x}^{\,n}.
$$

Declaration 0171 `goldenConj_mul` has already established

$$
\overline{xy}=\overline{x}\,\overline{y},
$$

so the present theorem is the inductive extension of multiplication preservation to natural powers.

## Role in the full proof

At this point in `GoldenDivisibility.lean`, declarations 0193–0195 have established compatibility of conjugation with addition, negation, and subtraction. Declaration 0196 adds compatibility with powers.

Since fifth powers are central to FLT5, the ability to rewrite

$$
\overline{x^5}=\overline{x}^{\,5}
$$

is important for later unit, norm, and fifth-power factorization arguments.

Together with 0170 `goldenConj_invol`, 0171 `goldenConj_mul`, 0193 `goldenConj_add`, 0194 `goldenConj_neg`, and 0195 `goldenConj_sub`, this theorem further exposes the fact that `goldenConj` behaves essentially as a ring automorphism of `GoldenInt`.

## Direct dependencies

The proof directly uses:

- 0171 `goldenConj_mul`
- 0159 `golden_mul_eq`
- the standard theorem `pow_succ`
- the induction hypothesis `ih`

At the type and operation level it depends on:

- `GoldenInt`
- 0163 `goldenConj`
- `Mul GoldenInt`
- natural powers on `GoldenInt`
- 0124 `goldenMul`

Conceptually,

$$
\texttt{goldenConj\_mul}
+\text{natural-number induction}
\longrightarrow
\texttt{goldenConj\_pow}.
$$

## Proof flow

The proof is induction on $n$.

### Base case $n=0$

```lean
| zero => rfl
```

Since $x^0=1$ and conjugation fixes the unit definitionally, the goal closes by reflexivity.

### Inductive step $n\mapsto n+1$

```lean
| succ n ih =>
    rw [pow_succ]
    change goldenConj (goldenMul (x ^ n) x) = _
    rw [goldenConj_mul, ih]
    rw [pow_succ, ← golden_mul_eq]
```

1. Rewrite $x^{n+1}$ as $x^n x$ using `pow_succ`.
2. Use `change` to expose standard multiplication as the raw operation `goldenMul`.
3. Apply `goldenConj_mul` to distribute conjugation across the product.
4. Apply the induction hypothesis to replace `goldenConj (x ^ n)` by `goldenConj x ^ n`.
5. Expand the target power with `pow_succ` and use `← golden_mul_eq` to align raw and standard multiplication syntax.

Thus the proof combines the mathematical induction with the representation bridge between the explicit coordinate API and Lean's standard multiplication API.

## Lean-specific processing

The most characteristic steps are `change` and `← golden_mul_eq`.

```lean
change goldenConj (goldenMul (x ^ n) x) = _
```

After `pow_succ`, the expression contains the standard multiplication `x ^ n * x`. The registered `Mul GoldenInt` instance is definitionally implemented by `goldenMul`, but `goldenConj_mul` is stated using the raw operation. `change` therefore reshapes the goal to match the theorem's statement.

The final

```lean
rw [pow_succ, ← golden_mul_eq]
```

performs the same raw/standard API alignment on the target side.

This theorem is a good example of a mathematically simple homomorphism law whose Lean proof must still account explicitly for the representation layer expected by previously stated lemmas.

## Redundancy and duplication

Mathematically, this theorem is a generic consequence of 0171 `goldenConj_mul`, so it contains little independent information.

If `goldenConj` were bundled as a `RingHom` or `RingEquiv`, a generic theorem corresponding to `map_pow` would provide this result automatically.

The current source instead exposes the conjugation laws individually, creating some structural duplication across `goldenConj_add`, `goldenConj_mul`, and `goldenConj_pow`.

That duplication nevertheless has audit value in an explicit-coordinate development: the proof makes the raw/standard multiplication boundary visible and shows exactly where representation conversion is required.

## Optimization candidates

1. **Keep the current induction proof**
   - clear dependency structure and explicit representation bridge.

2. **Bundle conjugation as a `RingHom`**
   - use generic `map_pow` instead of a custom induction proof.

3. **Bundle conjugation as a `RingEquiv`**
   - combine 0170 `goldenConj_invol` with the ring-homomorphism laws to expose the full automorphism API.

4. **Provide multiplication compatibility in standard notation**
   - a theorem `goldenConj (x * y) = goldenConj x * goldenConj y` could reduce the `change` / `golden_mul_eq` conversions.

5. **Attempt a shorter `simpa` proof**
   - this may be possible after appropriate simp lemmas are available, but exact behavior is unverified because no Lean build is performed here.

The local proof is already concise; the major optimization opportunity is bundling the conjugation API as a morphism.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface used here includes:

- natural-number induction
- `pow_succ`
- rewriting
- `change`
- multiplication and power on `GoldenInt`
- `goldenConj_mul`
- `golden_mul_eq`

The theorem itself does not directly use `ring`, `norm_num`, or divisibility tactics.

The surrounding module also develops divisibility, norms, and units, so its true minimal import set is broader. Because this museum pass does not run Lean builds, the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful implementations to compare include:

- A: the current explicit induction proof
- B: a version using standard-notation multiplication compatibility to reduce representation conversion
- C: bundle `goldenConj` as a `RingHom` and use generic `map_pow`
- D: bundle it as a `RingEquiv` and use the automorphism API
- E: induct on raw `goldenPow` first, then connect to standard powers with `golden_pow_eq`

Comparison axes include proof length, number of raw/standard API crossings, abstraction cost, visibility of mathematical provenance, downstream reuse, and robustness under refactoring.

The contrast between A and C is especially useful for evaluating the value of a generic morphism abstraction in an explicit-coordinate formalization.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0195 and immediately before 0197 `goldenNorm_pow`:

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]

theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]
```

The target branch contains Japanese and English PDFs, but the exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0197 `goldenNorm_pow`**:

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

Where 0196 lifts conjugation multiplicativity to powers, 0197 lifts 0174 `goldenNorm_mul` to powers. It is the direct bridge to later arguments using $N(x^5)=N(x)^5$.
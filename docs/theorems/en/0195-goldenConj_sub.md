# 0195 — `goldenConj_sub`

## Lean type

```lean
theorem goldenConj_sub (x y : GoldenInt) :
    goldenConj (x - y) = goldenConj x - goldenConj y := by
  calc
    goldenConj (x - y) = goldenConj (x + -y) := by rfl
    _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
    _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
    _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

This is a `theorem` stating that golden conjugation preserves subtraction.

## Mathematical statement

Write golden integers as

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

The theorem asserts

$$
\overline{x-y}=\overline{x}-\overline{y}.
$$

Declaration 0193 `goldenConj_add` has already proved

$$
\overline{x+y}=\overline{x}+\overline{y},
$$

and 0194 `goldenConj_neg` has proved

$$
\overline{-y}=-\overline{y}.
$$

Therefore

$$
\overline{x-y}
=\overline{x+(-y)}
=\overline{x}+\overline{-y}
=\overline{x}-\overline{y}.
$$

One could also prove the result by directly unfolding the coordinate definition `goldenConj (a,b) = (a+b,-b)`, but the current proof deliberately reuses the additive and negation compatibility theorems established immediately beforehand.

## Role in the full proof

Later parts of `GoldenDivisibility.lean` analyze common divisors of an element and its conjugate. A central expression in that relative-primality argument is

```lean
beta - goldenConj beta
```

Declaration 0191 `goldenDivides_sub` says that a common divisor also divides a difference, while 0195 says that conjugation itself commutes with subtraction. These two theorems form complementary pieces of the API needed to move freely between divisibility and conjugation in element/conjugate difference arguments.

The conjugation API now contains:

- 0170 `goldenConj_invol` — involution;
- 0171 `goldenConj_mul` — multiplication preservation;
- 0193 `goldenConj_add` — addition preservation;
- 0194 `goldenConj_neg` — negation preservation;
- 0195 `goldenConj_sub` — subtraction preservation.

Together these declarations expose, theorem by theorem, the fact that `goldenConj` behaves essentially as a ring automorphism.

## Direct dependencies

The proof directly uses the named theorems:

- 0193 `goldenConj_add`;
- 0194 `goldenConj_neg`.

It also uses the standard subtraction identity

```lean
sub_eq_add_neg
```

and relies on the fact that subtraction on `GoldenInt` is definitionally connected to addition and negation.

At the level of types and operations, it depends on:

- `GoldenInt`;
- 0163 `goldenConj`;
- `Sub GoldenInt`;
- `Add GoldenInt`;
- `Neg GoldenInt`.

Conceptually, the dependency is

$$
\texttt{goldenConj\_add}
+\texttt{goldenConj\_neg}
\longrightarrow
\texttt{goldenConj\_sub}.
$$

## Proof flow

The current proof is a `calc` chain mirroring the mathematical derivation:

```lean
calc
  goldenConj (x - y) = goldenConj (x + -y) := by rfl
  _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
  _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
  _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

1. Regard `x - y` definitionally as `x + -y`.
2. Apply `goldenConj_add` to distribute conjugation over addition.
3. Apply `goldenConj_neg` to replace `goldenConj (-y)` with `-goldenConj y`.
4. Use `sub_eq_add_neg` to return from addition-plus-negation syntax to standard subtraction notation.

Unlike 0193 and 0194, this theorem does not reopen the coordinate representation with `ext`. It composes the morphism-like API already established upstream.

## Lean-specific processing

The first line

```lean
goldenConj (x - y) = goldenConj (x + -y) := by rfl
```

closes by reflexivity because the registered subtraction on `GoldenInt` is definitionally tied to addition and negation through the raw subtraction implementation.

The `_` placeholders in the `calc` chain carry forward the previous right-hand side, keeping the algebraic transformation readable.

The second step supplies `goldenConj_add _ _` directly as a theorem term. The next two steps use local rewriting with `rw`.

In particular,

```lean
rw [sub_eq_add_neg]
```

expands the target-side subtraction `goldenConj x - goldenConj y` into addition with a negated term so that it matches `goldenConj x + -goldenConj y`.

The proof is therefore only lightly automated, and the exact algebraic laws used remain visible in the proof surface.

## Redundancy and duplication

Mathematically, 0195 is an immediate consequence of 0193 and 0194, so it carries little independent information.

If `goldenConj` were bundled as a `RingHom` or `RingEquiv`, subtraction preservation would also be available generically through a theorem corresponding to `map_sub`.

Nevertheless, a dedicated theorem is useful because differences such as `beta - goldenConj beta` are genuinely important downstream. A named `goldenConj_sub` theorem lets later proofs state the intended algebraic action directly instead of repeatedly expanding subtraction into addition and negation.

Thus the declaration can be viewed as intentional API redundancy at theorem level, while the absence of a bundled conjugation morphism is the larger structural duplication.

## Optimization candidates

1. **Keep the current `calc` proof**
   - highly readable and closely mirrors the mathematical derivation.

2. **Compress with `simpa [sub_eq_add_neg]`**
   - it may be possible to combine `goldenConj_add` and `goldenConj_neg` through simplification;
   - the exact simp behavior is unverified because no Lean build is run in this museum pass.

3. **Return to a direct coordinate proof**
   - a proof along the lines of `ext <;> simp [goldenConj] <;> ring` is plausible;
   - this would reduce theorem dependency depth but lose the structural reuse of 0193 and 0194.

4. **Bundle `goldenConj` as a `RingHom`**
   - generic `map_add`, `map_neg`, `map_sub`, and `map_mul` APIs could replace several custom compatibility theorems.

5. **Bundle conjugation as `RingEquiv GoldenInt GoldenInt`**
   - 0170 `goldenConj_invol` already supplies the inverse behavior needed for an automorphism-level abstraction.

The local proof is already quite efficient. The largest optimization opportunity lies in bundling the conjugation API as a whole rather than shortening this theorem.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface needed by this theorem is small:

- `calc`;
- equality rewriting;
- `sub_eq_add_neg`;
- addition, negation, and subtraction on `GoldenInt`;
- `goldenConj_add`;
- `goldenConj_neg`.

The theorem itself does not directly require `ring`, `norm_num`, divisibility machinery, or norm tactics.

The surrounding `GoldenDivisibility.lean` module does use divisibility, integer norms, units, and relative primality, so its module-wide minimal import set is broader. Since no Lean build is run here, the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful contestants include:

- A: current structural `calc` proof;
- B: compressed `simpa [sub_eq_add_neg]` proof;
- C: direct `ext` + `simp` + `ring` coordinate proof;
- D: bundle conjugation as a `RingHom` and use generic `map_sub`;
- E: bundle it as a `RingEquiv` and use the automorphism API.

Comparison axes include proof length, visibility of mathematical provenance, visibility of the coordinate implementation, abstraction cost, downstream reuse, and robustness under refactoring.

A versus C cleanly compares theorem reuse against coordinate recomputation, while D and E evaluate whether the entire conjugation layer should be structurally bundled.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source contains the consecutive block

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]

theorem goldenConj_sub (x y : GoldenInt) :
    goldenConj (x - y) = goldenConj x - goldenConj y := by
  calc
    goldenConj (x - y) = goldenConj (x + -y) := by rfl
    _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
    _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
    _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0196 `goldenConj_pow`**:

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

After 0193–0195 establish compatibility with the additive-group operations, 0196 repeatedly applies the multiplicative law from 0171 to show that conjugation preserves natural powers. This becomes useful when moving conjugation through fifth powers and other power expressions later in the FLT5 argument.
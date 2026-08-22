# 0189 — `goldenDivides_refl`

## Lean type

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

This is a `theorem` asserting reflexivity of the golden-order-specific divisibility relation `GoldenDivides` introduced in 0187: every golden integer divides itself.

## Mathematical statement

The mathematical content is simply the ordinary reflexivity of divisibility,

$$
x\mid x.
$$

If `GoldenDivides x x` is unfolded directly, one must produce some `q : GoldenInt` such that

$$
x=goldenMul\ x\ q.
$$

Choosing the quotient `goldenOne`, or standard `1`, makes the statement true.

The current proof does not construct that witness manually. Instead, it uses 0188 `goldenDivides_iff_dvd` to transport the goal to standard divisibility `x ∣ x` and delegates the result to Mathlib's existing reflexivity machinery.

## Role in the full proof

Declaration 0187 introduced `GoldenDivides` using the raw operation `goldenMul`, and 0188 proved it equivalent to Mathlib's standard divisibility relation. The present theorem is the first basic law that actually exploits that bridge.

The source then continues with `goldenDivides_trans` and `goldenDivides_sub`, transferring transitivity and subtraction closure to the same standard `dvd` API.

Thus 0189 does not add new number theory. Its role is to expose the ordinary algebraic behavior of divisibility through the domain-specific `GoldenDivides` vocabulary.

Later `GoldenRelPrime` arguments quantify over common divisors using `GoldenDivides`, so these thin basic-law wrappers form the foundation of the custom divisibility API.

## Direct dependencies

The direct dependencies are:

- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- `GoldenInt`
- Mathlib's standard reflexivity of divisibility

The proof script explicitly names only `goldenDivides_iff_dvd`.

Conceptually,

$$
\texttt{goldenDivides\_iff\_dvd}
+\text{standard divisibility reflexivity}
\longrightarrow
\texttt{goldenDivides\_refl}.
$$

## Proof flow

The complete proof is a single rewrite:

```lean
by
  rw [goldenDivides_iff_dvd]
```

1. Rewrite the goal `GoldenDivides x x` using 0188.
2. The goal becomes the standard proposition `x ∣ x`.
3. Lean / Mathlib closes the reflexive divisibility goal through the standard algebraic infrastructure available for `GoldenInt`.

No quotient witness is constructed explicitly in the local proof.

## Lean-specific processing

`rw [goldenDivides_iff_dvd]` performs proposition-level rewriting through an equivalence. Since 0188 has the type

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x
```

the occurrence `GoldenDivides x x` in the target is rewritten to `x ∣ x`.

The fact that the proof closes immediately after this rewrite demonstrates that 0188 is not merely explanatory documentation: it functions as the operational rewrite contract between the custom divisibility vocabulary and Mathlib's standard algebra API.

A direct proof from the definition would instead construct a witness, conceptually along the lines of

```lean
refine ⟨1, ?_⟩
```

and then resolve the equality through the raw multiplication interface. That route exposes more implementation detail but is unnecessary once 0188 exists.

## Redundancy and duplication

Standard divisibility already provides the fact `x ∣ x`, so `goldenDivides_refl` is logically a wrapper theorem.

Given 0188, downstream code could always rewrite `GoldenDivides` to standard divisibility and use the general theorem directly.

The wrapper nevertheless has API value:

- downstream statements remain entirely in golden-order vocabulary;
- callers do not need to know the bridge theorem name;
- the implementation route through standard `dvd` remains hidden;
- theorem names make the domain semantics explicit during proof auditing.

The redundancy is therefore best viewed as intentional API convenience rather than duplicated mathematics.

## Optimization candidates

1. **Keep the current thin wrapper**
   - preserves domain-specific naming while delegating implementation to Mathlib.

2. **Remove the wrapper and use standard divisibility directly**
   - reduces code volume, but may require repeated bridge rewrites downstream.

3. **Prove the statement directly from the definition**
   - makes the raw existential semantics visible, but bypasses the interoperability architecture established in 0188.

4. **Make 0188 a simp theorem and close reflexivity by simplification**
   - automatic normalization may reduce explicit rewrites;
   - proposition-level simp behavior should be checked before adopting this broadly.

The current one-line proof is already compact and readable, so local optimization pressure is low.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The theorem itself needs only a small surface:

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- the standard `Dvd` relation
- the `rw` tactic

It does not directly require `ring`, `norm_num`, or `omega`.

The complete `GoldenDivisibility.lean` module soon uses `dvd_trans`, `dvd_sub`, norm divisibility, and unit-related results, so the minimal import set for the entire module is wider. Since no Lean build is run in this museum pass, the exact fine-grained import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem is small enough that different proof architectures are easy to compare.

- A: current `rw [goldenDivides_iff_dvd]`
- B: unfold `GoldenDivides` and explicitly construct quotient `1`
- C: explicitly invoke standard divisibility reflexivity after transporting the goal
- D: mark 0188 as `[simp]` and use `simpa`

Useful comparison axes include proof-term size, visibility of raw semantics, Mathlib dependency depth, reuse of the bridge theorem, simp stability, and downstream readability.

The A-versus-B comparison is especially instructive: it contrasts proving a domain-specific definition directly with transporting it into a standard algebra API and reusing general theory.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The preceding 0188 document and source order confirm the sequence

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x := by
  ...

theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0190 `goldenDivides_trans`**:

```lean
theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

Where 0189 delegates reflexivity to standard divisibility, 0190 transports two `GoldenDivides` hypotheses to the standard API and reuses Mathlib's transitivity theorem `dvd_trans`.
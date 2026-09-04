# 0191 — `goldenDivides_sub`

## Lean type

```lean
theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

This is a `theorem` stating that if the same golden integer `d` divides both `x` and `y`, then it also divides their difference `x - y`.

## Mathematical statement

The mathematical content is the ordinary closure of divisibility under subtraction.

If

$$
d\mid x,\qquad d\mid y,
$$

then

$$
d\mid(x-y).
$$

Unfolding `GoldenDivides` directly would give quotients `q₁,q₂ : GoldenInt` such that

$$
x=dq_1,\qquad y=dq_2.
$$

Therefore

$$
x-y=dq_1-dq_2=d(q_1-q_2),
$$

so `q₁ - q₂` witnesses `GoldenDivides d (x - y)`.

The current Lean proof does not build that witness explicitly. Instead, it transports the custom divisibility relation to Mathlib's standard `∣` relation through 0188 `goldenDivides_iff_dvd`, then reuses the generic theorem `dvd_sub`.

## Role in the full proof

Declarations 0187–0191 form a small foundational API block for `GoldenDivides`:

- 0187 `GoldenDivides` — divisibility defined through raw `goldenMul`
- 0188 `goldenDivides_iff_dvd` — exact equivalence with standard `∣`
- 0189 `goldenDivides_refl` — reflexivity
- 0190 `goldenDivides_trans` — transitivity
- 0191 `goldenDivides_sub` — a common divisor also divides a difference

Among these basic laws, the present theorem has a particularly clear downstream role. Later in `GoldenDivisibility.lean`, if a golden integer `d` divides both `beta` and `goldenConj beta`, the proof forms

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

and thereby transports the common divisor to the difference between an element and its conjugate. That difference has a simpler coordinate form and can then be pushed through norm divisibility into ordinary integer constraints.

Thus 0191 is the basic mechanism that moves a common golden divisor from two conjugate factors to a more controllable difference. This is an important step in the later relative-primality argument used by the FLT5 proof.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- Mathlib theorem `dvd_sub`
- the subtraction structure on `GoldenInt`, provided by `Sub GoldenInt` / `goldenSub`

The proof script explicitly names only `goldenDivides_iff_dvd` and `dvd_sub`.

Conceptually, the proof is the transport

$$
\texttt{GoldenDivides}
\xleftrightarrow{\texttt{goldenDivides\_iff\_dvd}}
\text{standard divisibility}
\xrightarrow{\texttt{dvd\_sub}}
\texttt{GoldenDivides}.
$$

## Proof flow

The current proof has only two stages:

```lean
by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

1. Convert `hdx : GoldenDivides d x` to `d ∣ x`.
2. Convert `hdy : GoldenDivides d y` to `d ∣ y`.
3. Convert the goal `GoldenDivides d (x - y)` to `d ∣ x - y`.
4. Apply Mathlib's `dvd_sub hdx hdy` directly.

The proof never unfolds the existential witness inside `GoldenDivides`, nor does it unfold the coordinate definitions of `goldenMul` or `goldenSub`. It deliberately reuses the standard algebraic divisibility API.

## Lean-specific processing

In

```lean
rw [goldenDivides_iff_dvd] at hdx hdy ⊢
```

`⊢` includes the current goal among the rewrite targets. Thus

```lean
hdx : GoldenDivides d x
hdy : GoldenDivides d y
⊢ GoldenDivides d (x - y)
```

is converted in one command to

```lean
hdx : d ∣ x
hdy : d ∣ y
⊢ d ∣ x - y.
```

Because `goldenDivides_iff_dvd` is an `↔` theorem, Lean can use it for proposition-level rewriting. This is the same transport pattern as 0190, but the generic theorem at the destination is now `dvd_sub` rather than `dvd_trans`.

The goal already uses standard subtraction `x - y` through the `Sub GoldenInt` instance, so `dvd_sub` applies without any need to return to the raw operation `goldenSub`.

## Redundancy and duplication

`goldenDivides_sub` is a thin domain-specific wrapper around Mathlib's `dvd_sub`, so once 0188 exists it contains little new logical information.

A direct proof could unfold `GoldenDivides`, extract the two quotient witnesses, and construct `q₁ - q₂` as the new quotient. A design using only standard `∣` could omit this theorem entirely and call `dvd_sub` directly downstream.

Keeping the wrapper nevertheless has clear benefits:

- downstream proofs remain entirely in the `GoldenDivides` vocabulary;
- transport to standard divisibility is localized;
- the element-minus-conjugate argument is readable directly from theorem names;
- explicit quotient construction is hidden from downstream code.

In particular, because this theorem is actually used to transport a common divisor to `beta - goldenConj beta`, its domain-specific name contributes to the proof narrative rather than serving only as a convenience wrapper.

## Optimization candidates

1. **Keep the current proof**
   - essentially minimal and explicit about the bridge to Mathlib.

2. **Construct the quotient witness directly**
   - makes the raw semantics of `GoldenDivides` maximally visible;
   - but requires more work with subtraction, distributivity, and raw/standard multiplication interfaces.

3. **Use standard `∣` throughout**
   - could remove the wrapper block around 0189–0191;
   - at the cost of losing domain-specific vocabulary and some auditability.

4. **Use the bridge theorem as simp normalization**
   - could reduce repeated boilerplate;
   - but the global effect of proposition-level simp should be checked carefully.

5. **Introduce a more specialized common-divisor-of-conjugates lemma**
   - if the pattern `x - conj x` recurs often, a higher-level domain-specific lemma might better expose the mathematical intent.

Locally, the current proof is already concise and structurally clear, so there is little pressure to change it.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface needed by this theorem is small:

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- standard divisibility
- `dvd_sub`
- the `rw` tactic

The theorem itself does not use `ring`, `norm_num`, `omega`, or analysis APIs.

The surrounding `GoldenDivisibility.lean` module immediately proceeds to norm divisibility, conjugation, powers, and unit arguments, so the true minimal import set for the module is broader than the needs of 0191 in isolation. Since this museum pass does not run a Lean build, the exact fine-grained minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem is small enough that proof-architecture differences remain easy to inspect.

Possible contestants are:

- A: current `rw [...] at hdx hdy ⊢; exact dvd_sub hdx hdy`
- B: unfold `GoldenDivides` and construct quotient witness `q₁ - q₂`
- C: use a `simpa`-centered transport around `dvd_sub`
- D: eliminate `GoldenDivides` and use only standard `∣`

Useful comparison axes include:

- proof and source size
- visibility of raw semantics
- degree of Mathlib API reuse
- dependence on the bridge theorem
- robustness under refactoring
- downstream readability
- compatibility with the later conjugate-difference argument

The comparison between A and B is especially instructive: it contrasts direct manipulation of a domain-specific existential definition with transport into a mature generic algebra API.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms the sequence

```lean
theorem goldenDivides_trans {d x y : GoldenInt} ...

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy

/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides ...
```

The target branch contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0192 `goldenNorm_dvd_of_goldenDivides`**:

```lean
/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

By 0191, the elementary laws of `GoldenDivides` are in place. Declaration 0192 begins the next stage: projecting divisibility inside the golden order to ordinary integer divisibility of norms, which supplies the arithmetic constraints needed by the later unit and relative-primality arguments.

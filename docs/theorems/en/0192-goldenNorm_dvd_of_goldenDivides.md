# 0192 — `goldenNorm_dvd_of_goldenDivides`

## Lean type

```lean
/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

This is a `theorem` stating that if `d` divides `x` inside the golden order `GoldenInt`, then the integer norm `goldenNorm d` divides `goldenNorm x`.

## Mathematical statement

`GoldenDivides d x` is the raw golden-order statement

$$
d\mid x,
$$

which by definition means that some `q : GoldenInt` satisfies

$$
x=dq.
$$

By 0174 `goldenNorm_mul`, the golden norm is multiplicative:

$$
N(x)=N(dq)=N(d)N(q).
$$

Therefore, in the ordinary integer ring,

$$
N(d)\mid N(x).
$$

The theorem is the explicit `GoldenInt` API form of the standard principle that a multiplicative norm transports divisibility in the source ring to divisibility in the target ring.

## Role in the full proof

Declarations 0187–0191 established the elementary API of `GoldenDivides`:

- 0187 `GoldenDivides` — divisibility defined using raw `goldenMul`
- 0188 `goldenDivides_iff_dvd` — equivalence with Mathlib's standard `∣`
- 0189 `goldenDivides_refl` — reflexivity
- 0190 `goldenDivides_trans` — transitivity
- 0191 `goldenDivides_sub` — a common divisor also divides a difference

Declaration 0192 is the first step beyond those internal laws: it projects a factor relation in the golden order down to ordinary integer divisibility through the norm.

This becomes important in the later unit and relative-primality arguments. If a golden integer `d` divides two conjugate factors, 0191 first lets the proof move `d` to their difference. Then 0192 turns that golden divisibility into an integer statement

$$
N(d)\mid N(\text{difference}).
$$

At that point `N(d)` can be constrained using ordinary integer arithmetic, prime factors, absolute size, and eventually the condition that a unit has norm `±1`.

Thus 0192 is the entry point of the dimension-reduction pattern

$$
\text{golden divisibility}
\longrightarrow
\text{integer divisibility of norms}.
$$

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0187 `GoldenDivides`
- 0164 `goldenNorm`
- 0174 `goldenNorm_mul`
- standard integer divisibility in Mathlib
- Mathlib theorem `dvd_mul_right`

The proof script explicitly names `goldenNorm_mul` and `dvd_mul_right`.

Conceptually,

$$
\texttt{GoldenDivides } d\ x
\Rightarrow x=dq
\xrightarrow{\ N(x)=N(d)N(q)\ }
N(d)\mid N(x).
$$

## Proof flow

The current proof has three compact steps:

```lean
by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

1. Destructure `h : GoldenDivides d x`, obtaining a quotient `q` and the equality `x = goldenMul d q`.
2. The `rfl` pattern substitutes `goldenMul d q` for `x` immediately.
3. Rewrite the norm of the product with `goldenNorm_mul`:

$$
goldenNorm(goldenMul\ d\ q)=goldenNorm(d)\cdot goldenNorm(q).
$$

4. Close the resulting integer-divisibility goal with `dvd_mul_right _ _`.

Unlike 0189–0191, this theorem does not route through 0188 `goldenDivides_iff_dvd`; it uses the existential witness of `GoldenDivides` directly.

## Lean-specific processing

The command

```lean
rcases h with ⟨q, rfl⟩
```

uses the definition

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

to extract the quotient witness `q` while simultaneously consuming the equality through an `rfl` pattern.

As a result, every occurrence of `x` in the goal is replaced on the spot by `goldenMul d q`; no separate `rw [hq]` step is needed.

Then

```lean
rw [goldenNorm_mul]
```

uses 0174 to turn the `GoldenInt` statement into an integer product. Finally,

```lean
exact dvd_mul_right _ _
```

lets Lean infer the placeholders from the target. The proof contains no coordinate expansion, `ring`, or `norm_num`: it closes entirely by composing previously exposed APIs.

## Redundancy and duplication

Mathematically, this theorem is a specialization of the general principle that multiplicative maps preserve divisibility.

At present, however, `goldenNorm` is a plain function into `ℤ`, not a bundled multiplicative morphism. Therefore the preservation theorem is stated explicitly rather than obtained automatically from a generic morphism API.

If `goldenNorm` were packaged into a suitable multiplicative structure, later facts such as `goldenNorm_mul`, `goldenNorm_pow`, and divisibility preservation might be derivable from more generic lemmas. The design question is slightly subtle because `goldenNorm` is signed and takes values in `ℤ`, so the most natural existing abstraction should be chosen carefully.

The current dedicated theorem is nevertheless short and gives downstream FLT5 code a very readable statement, so its API value is high even if the mathematics is generic.

## Optimization candidates

1. **Keep the current proof**
   - uses the quotient witness directly, has shallow dependencies, and is mathematically transparent.

2. **Route through standard divisibility**
   - use 0188 `goldenDivides_iff_dvd`, obtain a standard quotient witness, then map norms.
   - likely more indirect than the present proof.

3. **Bundle `goldenNorm` as a multiplicative map**
   - could make `goldenNorm_mul`, `goldenNorm_pow`, and divisibility preservation instances of generic algebraic infrastructure.
   - attractive if the norm API continues to grow.

4. **Separate signed norm and absolute norm APIs more explicitly**
   - the Euclidean-domain layer later uses `Int.natAbs (goldenNorm x)`, so a clearer distinction between the signed quadratic norm and the nonnegative Euclidean size may improve architecture.

5. **Add a higher-level common-divisor norm lemma**
   - if the relative-primality proof repeats the pattern for two common-divisor hypotheses, the transport could be bundled one level above 0192.

Locally, the present proof is already concise and has little optimization pressure.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface used by this theorem is small:

- existential elimination via `rcases`
- `GoldenDivides`
- `goldenNorm`
- `goldenNorm_mul`
- integer divisibility
- `dvd_mul_right`
- rewriting via `rw`

The theorem itself does not use `ring`, `norm_num`, `omega`, or analysis APIs.

The surrounding `GoldenDivisibility.lean` module soon uses conjugation, powers, units, and integer norm arguments, so the true minimal import set for the full module is broader than the needs of 0192 alone. Since this museum pass does not run a Lean build, the exact fine-grained minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The comparison is clean:

- A: current `rcases` + `goldenNorm_mul` + `dvd_mul_right`
- B: transport through 0188 and use the standard `dvd` witness
- C: bundle `goldenNorm` as a multiplicative map and derive the theorem generically
- D: unfold all the way to raw coordinates and prove the integer statement directly

Useful comparison axes include:

- proof/source size
- dependency depth
- degree of norm structuring
- dependence on raw coordinates
- reuse of Mathlib's generic algebra API
- downstream readability
- suitability for later generalization to arbitrary quadratic orders

The contrast between A and C is especially instructive: A proves exactly the needed theorem with minimal structure, while C invests in an abstract norm-morphism layer in exchange for broader generic reuse.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms the sequence

```lean
theorem goldenDivides_sub {d x y : GoldenInt} ...

/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _

theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

The target branch contains Japanese and English PDFs as well. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0193 `goldenConj_add`**:

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

After 0192 projects divisibility through the norm, the source enters a block establishing compatibility of conjugation with addition, negation, subtraction, and powers. Declaration 0193 is the first theorem in that block and states that golden conjugation preserves addition.

# 0190 — `goldenDivides_trans`

## Lean type

```lean
theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

This is a `theorem` asserting transitivity of the golden-order-specific divisibility relation `GoldenDivides` introduced in 0187.

## Mathematical statement

The mathematical content is the ordinary transitivity of divisibility.

If

$$
d\mid x,\qquad x\mid y,
$$

then

$$
d\mid y.
$$

Unfolding `GoldenDivides` directly would give quotients `q₁,q₂ : GoldenInt` such that

$$
x=dq_1,
\qquad
y=xq_2.
$$

Substitution gives

$$
y=(dq_1)q_2=d(q_1q_2),
$$

so the product quotient `q₁q₂` witnesses `GoldenDivides d y`.

The current Lean proof does not construct this witness manually. Instead, it uses 0188 `goldenDivides_iff_dvd` to transport all three propositions to Mathlib's standard divisibility relation and then reuses the generic theorem `dvd_trans`.

## Role in the full proof

The block around 0187–0191 equips `GoldenDivides` with the basic laws needed for a domain-specific divisibility API:

- 0187 `GoldenDivides` — definition using raw `goldenMul`
- 0188 `goldenDivides_iff_dvd` — exact equivalence with standard `∣`
- 0189 `goldenDivides_refl` — reflexivity
- 0190 `goldenDivides_trans` — transitivity
- 0191 `goldenDivides_sub` — closure of a common divisor under subtraction

The present theorem is the basic tool for composing multi-stage factorizations into a single `GoldenDivides` fact.

Later FLT5 arguments propagate golden factors through further factorizations and conjugation relations. Naming transitivity at the domain-specific level lets downstream proofs avoid rebuilding products of quotient witnesses by hand.

The theorem is mathematically generic, but architecturally it is an important recovery of the 0188 bridge into the custom API.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- Mathlib theorem `dvd_trans`

The proof script explicitly names `goldenDivides_iff_dvd` and `dvd_trans`.

Conceptually,

$$
\texttt{GoldenDivides}
\xleftrightarrow{\texttt{goldenDivides\_iff\_dvd}}
\text{standard divisibility}
\xrightarrow{\texttt{dvd\_trans}}
\texttt{GoldenDivides}.
$$

## Proof flow

The proof has only two stages:

```lean
by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

1. `rw [goldenDivides_iff_dvd] at hdx hxy ⊢` converts both hypotheses and the goal to standard divisibility.
2. The context becomes

```lean
hdx : d ∣ x
hxy : x ∣ y
⊢ d ∣ y
```

3. `dvd_trans hdx hxy` closes the goal.

The proof never unfolds the existential definition of `GoldenDivides`. It transports the domain-specific propositions to the generic algebra API, uses the generic theorem there, and obtains the desired custom proposition through the rewritten goal.

## Lean-specific processing

In

```lean
rw [goldenDivides_iff_dvd] at hdx hxy ⊢
```

`⊢` tells `rw` to rewrite the current goal in addition to the named hypotheses.

Thus one rewrite command transforms

```lean
hdx : GoldenDivides d x
hxy : GoldenDivides x y
⊢ GoldenDivides d y
```

into

```lean
hdx : d ∣ x
hxy : x ∣ y
⊢ d ∣ y.
```

Because `goldenDivides_iff_dvd` is an `↔` theorem, it can be used for proposition-level rewriting. Declaration 0189 rewrote only the goal, whereas 0190 shows the more general pattern of aligning multiple hypotheses and the goal through the same bridge.

After that transport, `exact dvd_trans hdx hxy` needs no additional `simpa`, coercion handling, or raw multiplication unfolding.

## Redundancy and duplication

`goldenDivides_trans` is a thin domain-specific wrapper around Mathlib's standard transitivity theorem for divisibility.

Once 0188 exists, downstream proofs could always perform the bridge rewrite and call `dvd_trans` themselves. The theorem can also be proved by unfolding `GoldenDivides` and multiplying the two quotient witnesses.

Keeping the wrapper nevertheless has useful API value:

- downstream code can remain entirely in the `GoldenDivides` vocabulary;
- quotient-witness composition is hidden;
- the transport to Mathlib's standard divisibility API is localized;
- the public theorem name can remain stable even if the internal representation of `GoldenDivides` changes.

So the declaration is logically redundant but intentionally useful as an API and auditability layer.

## Optimization candidates

1. **Keep the current proof**
   - short, explicit about standard-theorem reuse, and easy to maintain.

2. **Compress with a `simpa`-centered proof**
   - a shorter form may be possible, but the current `rw ... at ... ⊢` makes the transport architecture especially visible.

3. **Construct quotient witnesses directly**
   - this exposes the raw meaning of divisibility most directly;
   - however, it would likely require explicit use of multiplication associativity and raw/standard multiplication bridges, increasing proof burden.

4. **Remove `GoldenDivides` and use standard `∣` everywhere**
   - this could eliminate much of the wrapper layer around 0189–0191;
   - the cost is losing the domain-specific vocabulary used for proof auditing.

5. **Consider simp-based normalization through 0188**
   - automatic transport may reduce boilerplate;
   - proposition-level simp direction and global effects should be evaluated carefully.

Locally, the current proof is already minimal and clear enough that optimization pressure is low.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface required by this theorem is small:

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- standard divisibility
- `dvd_trans`
- the `rw` tactic

The theorem itself does not use `ring`, `norm_num`, `omega`, or analysis APIs.

The surrounding `GoldenDivisibility.lean` module soon uses `dvd_sub`, norm divisibility, conjugation, and unit theorems, so its true minimal import set is broader than the needs of 0190 in isolation. Since this museum pass does not run a Lean build, the exact fine-grained import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem is small enough that differences in proof architecture remain easy to inspect.

Possible contestants are:

- A: current `rw [...] at hdx hxy ⊢; exact dvd_trans hdx hxy`
- B: unfold `GoldenDivides` and compose quotient witnesses directly
- C: transport around `dvd_trans` using a `simpa`-centered proof
- D: eliminate `GoldenDivides` and use standard `∣` directly

Useful comparison axes include:

- proof term and source size
- visibility of raw semantics
- reuse of Mathlib standard APIs
- dependence on the bridge theorem
- robustness under refactoring
- downstream readability

The comparison between A and B is especially instructive: it contrasts direct manipulation of a domain-specific existential definition with transport into a mature generic algebra API.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms the sequence

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]

theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  ...
```

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0191 `goldenDivides_sub`**:

```lean
theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

Where 0190 delegates transitivity to `dvd_trans`, 0191 delegates the fact that a common divisor divides a difference to `dvd_sub`. That step is used later when common divisors of an element and its conjugate are propagated to their difference.
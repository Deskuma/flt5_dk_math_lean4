# 0193 — `goldenConj_add`

## Lean type

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

This is a `theorem` stating that golden conjugation `goldenConj` preserves addition.

## Mathematical statement

Write

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

Declaration 0163 defines `goldenConj` by the coordinate transformation

$$
(a,b)\longmapsto(a+b,-b).
$$

Therefore

$$
\overline{x+y}=\overline{x}+\overline{y}.
$$

Indeed,

$$
x+y=(a+c)+(b+d)\varphi,
$$

so conjugating the sum gives

$$
\overline{x+y}=(a+c+b+d)-(b+d)\varphi.
$$

On the other hand,

$$
\overline{x}+\overline{y}
=(a+b-b\varphi)+(c+d-d\varphi)
=(a+b+c+d)-(b+d)\varphi,
$$

which is the same element.

The theorem therefore exposes the fact that golden conjugation is not merely a coordinate function: it preserves the additive structure of the golden order.

## Role in the full proof

The development since 0163 has gradually exposed the structural properties of `goldenConj`:

- 0166 `goldenConj_phi` — $\overline\varphi=1-\varphi$
- 0168 `goldenConj_ofInt` — embedded integers are fixed
- 0170 `goldenConj_invol` — $\overline{\overline{x}}=x$
- 0171 `goldenConj_mul` — $\overline{xy}=\overline{x}\,\overline{y}$
- 0175 `goldenNorm_conj` — $N(\overline{x})=N(x)$

Declaration 0193 opens a block in `GoldenDivisibility.lean` that records compatibility of conjugation with addition, negation, subtraction, and powers.

This matters in the later relative-primality argument, where an element `beta` and its conjugate `goldenConj beta` are combined through sums and differences. Once a common divisor has been transported to such a difference, additive compatibility of conjugation helps normalize the surrounding expressions into the standard ring API.

Together with 0171, the present theorem also makes it natural to package `goldenConj` eventually as a `RingHom`, or, using the involution theorem 0170, as a `RingEquiv`.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0163 `goldenConj`
- 0121 `goldenAdd` and the resulting `Add GoldenInt` instance
- 0137 `golden_fst_add`
- 0138 `golden_snd_add`
- `GoldenInt.ext`
- integer ring arithmetic and Mathlib's `ring` tactic

The proof explicitly unfolds `goldenConj` and uses `ext`, `simp`, and `ring`.

Conceptually,

$$
\text{coordinate conjugation}
+\text{coordinate addition}
\Longrightarrow
\overline{x+y}=\overline{x}+\overline{y}.
$$

## Proof flow

The current proof is very compact:

```lean
by
  ext <;> simp [goldenConj] <;> ring
```

1. `ext` reduces equality of `GoldenInt` values to equality of their `fst` and `snd` coordinates.
2. `simp [goldenConj]` unfolds conjugation and uses the projection simp lemmas for addition.
3. `ring` closes the remaining integer polynomial equalities.

For the first coordinate the residual equality is essentially

$$
(a+c)+(b+d)=(a+b)+(c+d),
$$

while the second coordinate reduces to a form such as

$$
-(b+d)=(-b)+(-d).
$$

Thus the mathematics is linear, while the Lean proof benefits from the coordinate simp API accumulated earlier in the museum sequence.

## Lean-specific processing

`ext` uses the previously declared extensionality theorem `GoldenInt.ext`, converting a structure equality into two integer-coordinate equalities.

The tactical combinator `<;>` applies the following tactic to every generated goal, so

```lean
ext <;> simp [goldenConj] <;> ring
```

runs the same normalization pipeline on both coordinates.

`simp [goldenConj]` not only unfolds the conjugation definition; it also uses `@[simp]` projection theorems such as 0137–0138 to turn `(x + y).fst` and `(x + y).snd` into ordinary integer arithmetic.

Finally, `ring` runs only after the goal has already been reduced from `GoldenInt` to `ℤ`. The brevity of the theorem is therefore partly the payoff of the projection API built earlier in the development.

## Redundancy and duplication

Declaration 0171 `goldenConj_mul` and 0193 `goldenConj_add` prove multiplicative and additive preservation separately. The immediately following theorems `goldenConj_neg` and `goldenConj_sub` continue the same pattern, so the ring-map behavior of conjugation is spread across several named theorems.

Mathematically, one could instead construct `goldenConj` once as a `RingHom GoldenInt GoldenInt`. Addition, multiplication, zero, one, and integer-cast compatibility could then be obtained from the bundled morphism API. Combining that with 0170 `goldenConj_invol` would make a `RingEquiv` formulation natural.

The current design nevertheless has an important auditability advantage: every structural law remains visible as an explicit coordinate theorem. There is therefore a trade-off between reducing duplication through abstraction and preserving transparent coordinate proofs.

## Optimization candidates

1. **Keep the current proof**
   - `ext <;> simp <;> ring` is short and directly auditable against the coordinate model.

2. **Bundle `goldenConj` as a `RingHom`**
   - would expose `map_add`, `map_mul`, and related generic API automatically;
   - could reduce duplication among 0171, 0193, and nearby declarations.

3. **Bundle it as a `RingEquiv`**
   - use 0170 involutivity as the inverse certificate;
   - would also make transport of divisibility and units through conjugation more generic.

4. **Investigate a simp-only proof**
   - because the theorem is linear, a sufficiently strong integer simp normal form might remove the need for `ring`;
   - this is unverified because no Lean build is run in this museum pass.

5. **Generalize conjugation to a quadratic-order abstraction**
   - the coordinate argument is not unique to the golden order and could potentially be factored into a generic quadratic-order conjugation API.

Locally, the theorem is already concise; the principal architectural optimization is bundling the conjugation API rather than shortening this individual proof.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The direct surface required by this theorem consists of:

- structure extensionality
- simp
- commutative-ring normalization via `ring`
- the additive and projection API for `GoldenInt`
- `goldenConj`

The theorem itself does not require advanced number theory, divisibility, or analysis infrastructure. However, the surrounding `GoldenDivisibility.lean` module combines divisibility, norms, units, and relative primality, so the true minimal import set for the complete module is broader than the needs of 0193 alone.

Because this museum pass does not run a Lean build, the exact fine-grained minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Useful contestants include:

- A: current `ext <;> simp [goldenConj] <;> ring`
- B: explicit `apply GoldenInt.ext` followed by separate coordinate proofs
- C: bundle `goldenConj` as a `RingHom` and obtain the theorem from `map_add`
- D: bundle it as a `RingEquiv` and use the generic automorphism API
- E: specialize a generic quadratic-order conjugation theorem

Comparison axes include proof size, visibility of the coordinate implementation, abstraction cost, downstream theorem size, reuse of Mathlib's standard morphism API, and generalizability.

The contrast between A and C is especially useful: A accumulates explicit coordinate theorems, while C invests earlier in a bundled morphism abstraction.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source confirms the sequence

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0194 `goldenConj_neg`**:

```lean
theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

After 0193 records additive preservation, 0194 states preservation of additive inverses,

$$
\overline{-x}=-\overline{x}.
$$

Together with the following `goldenConj_sub`, these declarations complete the basic additive-group compatibility needed to treat conjugation as an additive homomorphism.

# 0224 — `goldenEuclideanSize`

## Lean type

```lean
/-- Euclidean size is the natural absolute value of the golden norm. -/
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

This is a `def`, not a theorem. It defines the natural-number-valued size used to drive Euclidean division on `GoldenInt` as the absolute value of the integer norm `goldenNorm x`.

## Mathematical statement and meaning of the declaration

For a golden integer

$$
x=a+b\varphi,
$$

the norm is

$$
N(x)=a^2+ab-b^2\in\mathbb Z.
$$

`goldenEuclideanSize` discards the sign of this integer-valued norm and uses

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N
$$

as the Euclidean measure.

In Lean, `goldenNorm x : ℤ` is passed to `Int.natAbs`, so the result has type `ℕ`. This is exactly the codomain needed for a convenient well-founded measure. Later declarations prove that the size strictly decreases on the concrete remainder.

## Role in the full proof

By 0220–0223 the construction already has a quotient, a remainder, and the reconstruction law

$$
yq+r=x.
$$

That is not yet enough to build a Euclidean domain: the remainder must also be strictly smaller than the divisor with respect to a well-founded measure.

Declaration 0224 introduces precisely that measure.

The source immediately continues with

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

and then

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

Later, `golden_remainder_size_lt` proves

$$
\operatorname{size}(r)<\operatorname{size}(y),
$$

and the final `goldenEuclideanDomain` instance directly installs this definition through

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
r_wellFounded := (measure goldenEuclideanSize).wf
remainder_lt := golden_remainder_size_lt
```

Thus 0224 is the **measure interface** that turns the previously developed golden norm arithmetic into Mathlib's Euclidean-domain hierarchy.

## Direct dependencies

The direct definitional dependencies are very small:

- `GoldenInt`
- 0164 `goldenNorm`
- `Int.natAbs`

Because this is a definition, there is no proof script and no theorem dependency in the body itself.

Its mathematical usefulness downstream is supported especially by:

- 0174 `goldenNorm_mul`
- 0215 `goldenNorm_ne_zero_of_ne_zero`

The former yields multiplicativity of the size; the latter yields positivity of the size on nonzero elements.

Conceptually the construction is simply

$$
\texttt{goldenNorm}:GoldenInt\to\mathbb Z
\quad\Longrightarrow\quad
\texttt{Int.natAbs}\circ\texttt{goldenNorm}:GoldenInt\to\mathbb N.
$$

## Construction flow

The definition has one step:

```lean
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

1. Accept `x : GoldenInt`.
2. Compute `goldenNorm x : ℤ`.
3. Remove the sign using `Int.natAbs`, producing a natural-number measure.

Mathematically this is just the absolute norm. In Lean, choosing a natural-number codomain delegates well-foundedness to the standard ordering on `ℕ`.

## Lean-specific processing

### 1. `Int.natAbs` changes the codomain to `ℕ`

The norm is genuinely signed; for example, `goldenNorm goldenPhi = -1`. Euclidean descent needs magnitude rather than sign, so `Int.natAbs` is the natural choice.

### 2. Well-foundedness does not need a custom proof

The final instance uses

```lean
(measure goldenEuclideanSize).wf
```

so the development does not construct a bespoke well-founded relation on `GoldenInt`. Supplying a natural-valued measure is enough for Mathlib's general `measure` machinery.

### 3. The signed norm and the Euclidean measure are intentionally separated

`goldenNorm` must retain its sign for conjugation, unit criteria, and arithmetic arguments. Euclidean descent only needs its magnitude. Giving the absolute norm a separate name keeps these two roles explicit.

## Redundancy and duplication

Mathematically, `goldenEuclideanSize x` is only the wrapper `Int.natAbs (goldenNorm x)`. The definition could be removed and the right-hand side repeated downstream.

A dedicated name is nevertheless valuable:

- it makes the Euclidean measure immediately visible in theorem names;
- it separates the signed arithmetic invariant from the termination measure;
- it gives clean APIs such as `goldenEuclideanSize_pos_of_ne_zero`, `goldenEuclideanSize_mul`, and `golden_remainder_size_lt`;
- it can be passed directly to the final `EuclideanDomain` relation and `measure` construction.

So the wrapper is logically thin but useful as an API boundary.

## Optimization candidates

1. **Keep the current definition**
   - simplest design and clearest Euclidean intent.

2. **Use an `abbrev` instead**
   - this would make the alias even more transparent, although the practical advantage over the current definition appears small.

3. **Abstract a generic norm-Euclidean helper**
   - for a ring with an integer-valued multiplicative norm and a remainder contraction theorem, one could potentially construct `Int.natAbs ∘ N` as a reusable size automatically.

4. **Unify an absolute-norm API with the Euclidean size**
   - if downstream number-theory code repeatedly needs the unsigned norm outside Euclidean division, a shared abstraction may reduce duplication. The choice between `ℕ` and `ℤ` as the public codomain would need care.

5. **Bundle the size certificates**
   - positivity, multiplicativity, and remainder decrease could be grouped into a Euclidean certificate structure, making the final instance easier to audit.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This definition alone needs only a very small Mathlib surface:

- `Int.natAbs`
- the basic `ℕ` and `ℤ` types

The surrounding `GoldenEuclidean.lean` module, however, also uses:

- `round` / `abs_sub_round`
- `field_simp`
- `linarith` / `nlinarith`
- `measure`
- `EuclideanDomain`

so the true minimal import set for the complete module is substantially broader.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Natural variants include:

- A: current dedicated definition `Int.natAbs (goldenNorm x)`;
- B: no dedicated name, using the expression directly downstream;
- C: first work with integer absolute value `|goldenNorm x| : ℤ`, then convert to a natural measure;
- D: derive the measure through a generic norm-Euclidean certificate;
- E: bundle quotient, remainder, size, and decrease into one structure.

Useful comparison axes are theorem-surface simplicity, ease of proving well-foundedness, coercion overhead, mathematical readability, generalizability, and the size of the final `EuclideanDomain` instance.

The contrast between A and D is especially useful for measuring how much generalization can be gained without losing the auditability of the explicit-coordinate implementation.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenEuclidean.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this definition immediately after 0223 `golden_quotient_mul_add_remainder`, followed by `goldenEuclideanSize_pos_of_ne_zero`, `goldenEuclideanSize_mul`, the strict remainder-contraction theorem, and finally `goldenEuclideanDomain`.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0225 `goldenEuclideanSize_pos_of_ne_zero`**:

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

Now that 0224 defines the Euclidean size as `|N(x)|`, 0225 proves that every nonzero golden integer has strictly positive size. This becomes a basic certificate for multiplicative size arguments and for the final `mul_left_not_lt` field of the Euclidean-domain instance.

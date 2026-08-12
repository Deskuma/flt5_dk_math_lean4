# 0036 — `body5_eq_add_pow_sub`

## Declaration

```lean
theorem body5_eq_add_pow_sub (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5 := by
  symm
  exact add_pow_five_sub_eq_mul_GN5 g y
```

## Lean type

```lean
body5_eq_add_pow_sub :
  (g y : ℕ) → Body5 g y = (g + y) ^ 5 - y ^ 5
```

For arbitrary natural numbers `g` and `y`, the theorem states that `Body5 g y` equals the fifth-power difference `(g+y)^5-y^5`.

## Mathematical statement

The definition of `Body5` is

$$
Body5(g,y)=g\,GN5(g,y).
$$

The preceding theorem gives

$$
(g+y)^5-y^5=g\,GN5(g,y).
$$

Reversing that equality yields

$$
Body5(g,y)=(g+y)^5-y^5.
$$

Although the right-hand side uses natural-number subtraction, no truncation occurs because $y\le g+y$, hence $y^5\le(g+y)^5$. The proof does not re-establish this order fact; it reuses the already proved theorem `add_pow_five_sub_eq_mul_GN5`.

## Role in the complete proof

The previous article introduced `Body5` only as a named product. This theorem is the first semantic bridge connecting that name to an actual fifth-power difference.

Later one substitutes $g=z-y$ and obtains

$$
Body5(z-y,y)=z^5-y^5.
$$

The Fermat equation then gives $z^5-y^5=x^5$, so that

$$
Body5(z-y,y)=x^5.
$$

Thus this theorem is the first half of a two-stage bridge from the local polynomial body in coordinates `(g,y)` to the original fifth-power equation.

## Direct dependencies

### `Body5`

```lean
def Body5 (g y : ℕ) : ℕ :=
  g * GN5 g y
```

This local definition supplies the meaning of the left-hand side.

### `add_pow_five_sub_eq_mul_GN5`

```lean
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y
```

This is the only substantive dependency. Its right-hand side is definitionally equal to `Body5 g y`, so Lean can close the expected type without an explicit unfold.

## Proof flow

1. The goal is `Body5 g y = (g+y)^5-y^5`.
2. `symm` reverses the equality, producing `(g+y)^5-y^5 = Body5 g y`.
3. Apply `add_pow_five_sub_eq_mul_GN5 g y`.
4. Since `Body5 g y` unfolds definitionally to `g * GN5 g y`, `exact` closes the goal.

No new expansion, `ring`, `omega`, or order proof is required.

## Lean-specific processing

### `symm`

The existing theorem is oriented opposite to the public API desired here, so the goal is reversed.

```lean
symm
```

turns an equality goal `a = b` into `b = a`.

### Definitional equality

The preceding theorem concludes

```lean
(g + y) ^ 5 - y ^ 5 = g * GN5 g y
```

while the reversed goal ends in `Body5 g y`. Because unfolding `Body5` makes these judgmentally equal, `exact` succeeds without `unfold Body5` or `simpa [Body5]`.

### Natural-number subtraction

Subtraction on `Nat` is truncated subtraction. This theorem does not manipulate its safety conditions directly; those obligations were already discharged by the preceding factorization theorem. Reusing that API avoids duplicated proof obligations.

## Redundancy and duplication

Mathematically, the theorem is only the composition of the definition of `Body5` with `add_pow_five_sub_eq_mul_GN5`; it adds no new arithmetic information. It remains valuable as a public lemma because it:

- lets later theorems rewrite `Body5` to a fifth-power difference without unfolding the definition;
- isolates users from the concrete implementation of `Body5`;
- fixes the equality orientation most convenient for later proof flow;
- makes the mathematical meaning “the body is the fifth-power difference” visible in the API name.

This is intentional abstraction rather than removable duplication.

## Optimization candidates

The current two-line proof is already minimal in practice. An alternative one-line proof is:

```lean
  simpa [Body5] using (add_pow_five_sub_eq_mul_GN5 g y).symm
```

The current version avoids an explicit unfold and relies on definitional equality, which better preserves the abstraction boundary.

Adding `[simp]` is another possible design, but automatically rewriting every `Body5` into a difference may be counterproductive in valuation arguments where the product form is preferable. Keeping rewrite direction explicit is safer. This is an unverified design proposal; no full simp-set build audit was performed.

## Required Mathlib imports and import optimization

The generated standalone source uses `import Mathlib`. This theorem itself directly needs only:

- natural numbers, powers, and subtraction;
- the local definition `Body5`;
- the local theorem `add_pow_five_sub_eq_mul_GN5`.

In the actual `BranchB.lean` module, the project imports supplying those declarations are the essential dependencies. Since the proof uses only `symm` and `exact`, no extra algebra-tactic import is required. The exact minimal import set has not been build-tested here.

## Comparator challenge suitability

This is suitable for an introductory-to-intermediate Comparator challenge.

```lean
theorem body5_eq_add_pow_sub_challenge (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5 := by
  -- Reuse the existing factorization theorem and align the equality direction.
  sorry
```

Three proof styles can be compared:

1. the current `symm` plus `exact` proof;
2. a one-line `.symm` plus `simpa [Body5]` proof;
3. an explicit unfolding and rewrite proof such as `unfold Body5; rw [← add_pow_five_sub_eq_mul_GN5]`.

The comparison should evaluate not only length, but also understanding of definitional equality, preservation of abstraction, and clarity of rewrite orientation.

## Evidence versus conjecture

The declaration type, two-line proof body, its placement immediately after `Body5`, and the next declaration `body5_eq_fifth_power_of_fermat` were verified in the generated `DkMath/FLT/Five/BranchB.lean` section of `Flt5DkMath/FLT5StandAlone.lean`.

The existing PDFs provide narrative context for the fifth-power factorization and Branch B route, but the Lean code is the final authority for this theorem’s implementation. Remarks about `[simp]` and the precise minimal import set are unverified design suggestions. No Lean build was run in this task.

## Next declaration to read

The next declaration in source order is

```lean
DkMath.FLT.Five.body5_eq_fifth_power_of_fermat
```

It substitutes $g=z-y$, uses the order hypothesis $y\le z$ to obtain

$$
Body5(z-y,y)=z^5-y^5,
$$

and then applies the Fermat equation to conclude

$$
Body5(z-y,y)=x^5.
$$

It is the second stage that specializes the general gap bridge from this article to a fifth-power normal form directly usable for a counterexample candidate.

# 0029 — `branchB_false_of_GN5_not_fifth_power`

## Declaration

```lean
theorem branchB_false_of_GN5_not_fifth_power
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y)
    (hGN : ¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5) :
    False := by
  exact hGN (branchB_fifth_power_factor_split hPack hBranch).2
```

## Lean type

This theorem takes a positive primitive FLT5 counterexample candidate, the Branch B condition, and an external proof that the corresponding `GN5` is not a perfect fifth power, and returns the contradiction `False`.

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  (¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5) →
  False
```

The third argument `hGN` is not a new arithmetic fact proved inside this theorem. It is a receiver input intended to collide with the perfect-fifth-power conclusion forced by the preceding Branch B reduction.

## Mathematical statement

From `CounterexamplePack x y z` and the Branch B condition

$$
5\nmid z-y,
$$

the previous theorem `branchB_fifth_power_factor_split` gives some $b\in\mathbb N$ such that

$$
GN5(z-y,y)=b^5.
$$

On the other hand, the hypothesis `hGN` says

$$
\neg\exists b\in\mathbb N,
\quad GN5(z-y,y)=b^5.
$$

Thus the same existential proposition is both established and denied, yielding a contradiction.

## Role in the complete proof

This theorem is the **final consumer interface for Branch B**.

By this point, the Reduction layer has converted the counterexample equation into a product of the gap and `GN5`, proved the two factors coprime under Branch B, and split them into separate fifth powers. This theorem extracts only the final output

```lean
∃ b : ℕ, GN5 (z - y) y = b ^ 5
```

and passes it to a non-fifth-power proof supplied by another provider.

Accordingly, this theorem does not itself establish that `GN5` is not a fifth power. A later concrete provider, valuation obstruction, or stronger normal-form/descent argument may supply `hGN`; once it does, Branch B closes in this one line.

## Direct dependencies

1. `CounterexamplePack`
   - Packages positivity, primitivity, and the FLT5 equation.
2. `GN5`
   - The homogeneous degree-four residual kernel after extracting the gap from the fifth-power difference.
3. `branchB_fifth_power_factor_split`
   - Returns separate perfect-fifth-power witnesses for the gap and `GN5` from `hPack` and `hBranch`.
4. The second conjunction projection `.2`
   - Selects only the `GN5` existential proof from the previous theorem's result.
5. Function application for consuming negation
   - In Lean, `¬ P` is `P → False`, so applying `hGN` to the existential proof produces `False`.

## Proof flow

1. Apply `branchB_fifth_power_factor_split hPack hBranch`.
2. Its conclusion is the conjunction

```lean
(∃ a : ℕ, z - y = a ^ 5) ∧
  (∃ b : ℕ, GN5 (z - y) y = b ^ 5).
```

3. Use `.2` to obtain the second component.

```lean
(branchB_fifth_power_factor_split hPack hBranch).2
```

4. Apply the negation hypothesis `hGN` to that existential proof.

```lean
hGN (branchB_fifth_power_factor_split hPack hBranch).2
```

5. The result type of `hGN` is `False`, so the goal closes.

## Lean-specific processing

### Negation is a function type

In Lean,

```lean
¬ P
```

is definitionally

```lean
P → False.
```

Thus `hGN` is both a statement of nonexistence and a function that returns a contradiction when supplied with an existence proof.

### Conjunction projection `.2`

The previous theorem returns two existential statements in a conjunction. This theorem needs only the latter, so it uses `.2` instead of destructuring both components.

```lean
(branchB_fifth_power_factor_split hPack hBranch).2
```

This is shorter than introducing names with `rcases` and avoids bringing the unused gap witness into the context.

### Implicit argument inference

The implicit variables `x y z` of `branchB_fifth_power_factor_split` are inferred from the types of `hPack` and `hBranch`. The target of `hGN` uses the same `z-y` and `y`, so no rewriting or `simpa` is required.

### Term proof

The whole proof is a single term. No tactic-state transformation is needed, and the dependency path is visible directly in the expression.

## Redundancy and duplication

There is no duplicated arithmetic, polynomial expansion, or prime-divisor argument here. This is a thin consumer theorem that feeds the second component of the previous result into a negated hypothesis.

If the same pattern recurs across branches or exponents, it could be abstracted propositionally as

```lean
(P ∧ Q) → ¬ Q → False.
```

However, that abstraction is logically trivial and would hide the FLT5-specific meaning. Keeping this named theorem is valuable because it exposes the public API by which Branch B is closed.

## Optimization candidates

1. The current one-line proof is already close to minimal and has no meaningful shortening opportunity.
2. For pedagogical readability, the existential fact may be named explicitly:

```lean
have hPow : ∃ b : ℕ, GN5 (z - y) y = b ^ 5 :=
  (branchB_fifth_power_factor_split hPack hBranch).2
exact hGN hPow
```

3. The present form more directly displays the provider-to-consumer connection.
4. If the return type of `branchB_fifth_power_factor_split` later becomes a structure, replacing `.2` with a meaningful field name would improve maintainability.
5. One could expose a theorem returning `¬ CounterexamplePack x y z` instead of `False`, but because the Branch B condition and `hGN` are separate inputs, the current contradiction consumer is easier to compose.

## Required Mathlib imports and import optimization

The standalone generated artifact uses `import Mathlib`, but this theorem itself directly needs very little Mathlib functionality.

Its direct needs are mainly:

1. Propositional `False`, negation, existential quantification, and conjunction.
2. Natural-number, power, and divisibility notation.
3. The repository declarations `CounterexamplePack`, `GN5`, and `branchB_fifth_power_factor_split`.

All heavier arithmetic dependencies are hidden behind the previous theorem. Unless `Reduction.lean` is split, transitive imports will provide most requirements. The exact minimal Mathlib module names have not been verified because no Lean build was run.

## Comparator challenge suitability

This is suitable as a small challenge. The difficulty is not arithmetic, but correctly extracting the needed component from the previous theorem and consuming negation as a function.

### Challenge proposal

```lean
{x y z : ℕ}
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
(hGN : ¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5)
⊢ False
```

Possible solutions to compare:

1. The current one-line term proof.
2. A two-step proof naming the perfect-fifth-power fact with `have`.
3. A version using `rcases branchB_fifth_power_factor_split ... with ⟨ha, hb⟩`.
4. A version delegating the final propositional step to `contradiction` or `aesop`.

Evaluation criteria include dependency clarity, avoidance of unused facts, degree of automation, and robustness under changes. The current proof is not only shortest but also the most direct representation of the logical structure.

## Distinguishing evidence from interpretation

The declaration type, proof body, use of the second component of `branchB_fifth_power_factor_split`, and the fact that this is the final declaration of `Reduction.lean` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

Calling it the final consumer interface for Branch B is an interpretation based on the source comment and module boundary. Minimal imports, replacing the conjunction with a structure, and comparisons with a general propositional lemma are unverified proposals. Existing PDFs are treated as supporting narrative material; the Lean source remains authoritative.

## Next theorem to read

```lean
DkMath.FLT.Five.coprime_GN5_y_of_coprime
```

This is the first theorem of the following `NormalForm.lean` module. It derives

$$
\gcd(GN5(g,y),y)=1
$$

from

$$
\gcd(g,y)=1.
$$

It transfers primitivity in gap coordinates to the `GN5` side and prepares the coprimality data retained by the subsequent elementary Branch B normal form.

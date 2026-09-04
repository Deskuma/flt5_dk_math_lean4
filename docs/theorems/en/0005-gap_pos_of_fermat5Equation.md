# 0005 — `gap_pos_of_fermat5Equation`

> This document is an English translation of the Japanese canonical edition. In case of discrepancy, the Japanese edition is authoritative.

## Lean type

```lean
theorem gap_pos_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    0 < z - y := by
  exact Nat.sub_pos_of_lt (right_lt_of_fermat5Equation hx hEq)
```

Its fully qualified name is `DkMath.FLT.Five.gap_pos_of_fermat5Equation`.

## Mathematical statement

Suppose natural numbers $x,y,z$ satisfy the exponent-five Fermat equation

$$
x^5+y^5=z^5
$$

and also satisfy $0<x$. Then the difference between the right-hand base $z$ and the second left-hand base $y$ is positive.

$$
0<z-y
$$

Over the natural numbers, this means more than merely introducing a difference. Lean's natural-number subtraction is truncated subtraction, so `0 < z - y` effectively records `y < z` and guarantees that the later gap coordinate is nondegenerate.

## Role in the complete proof

This theorem supplies the positivity needed to move from the global three-variable equation to the local gap coordinate

$$
g=z-y.
$$

The preceding theorem `right_lt_of_fermat5Equation` proves $y<z$, and this theorem converts that result into $0<z-y$. The positive gap becomes basic input for the later factorization involving `GN5 (z-y) y`, as well as for the primitive and five-adic branches.

The theorem does not establish a new algebraic identity. It re-encodes already available order information in the form required by the later gap-oriented API.

## Direct dependencies

The direct project-local dependencies are:

- `DkMath.FLT.Five.Fermat5Equation`
- `DkMath.FLT.Five.right_lt_of_fermat5Equation`

The proof directly uses the Mathlib theorem:

- `Nat.sub_pos_of_lt`

`right_lt_of_fermat5Equation hx hEq` returns `y < z`, and `Nat.sub_pos_of_lt` converts it into `0 < z - y`.

## Proof flow

The proof has one step:

1. Apply `right_lt_of_fermat5Equation` to `hx` and `hEq` to obtain `y < z`.
2. Apply `Nat.sub_pos_of_lt` to obtain `0 < z - y`.

The Lean term mirrors this structure directly:

```lean
exact Nat.sub_pos_of_lt (right_lt_of_fermat5Equation hx hEq)
```

All arithmetic reasoning, monotonicity of powers, and equation manipulation have already been encapsulated in the preceding theorem.

## Lean-specific processing

Subtraction on `ℕ` differs from integer subtraction: negative results are truncated to zero. Therefore, before treating `z-y` as a positive gap, one must prove `y<z`.

`Nat.sub_pos_of_lt` is the standard theorem crossing this boundary:

```lean
Nat.sub_pos_of_lt : y < z → 0 < z - y
```

This proof uses neither `omega` nor `ring`. It only connects the preceding order theorem to the standard subtraction API, making the dependency boundary especially clear.

The reverse direction can be obtained from `Nat.lt_of_sub_pos`, so over naturals the two forms are interconvertible:

$$
y<z \quad\Longleftrightarrow\quad 0<z-y.
$$

That equivalence is not itself proved by this theorem.

## Redundancy and duplication

`right_lt_of_fermat5Equation` and this theorem carry very closely related mathematical information, so they may appear to duplicate one another at the API level.

Their intended uses differ:

- `right_lt_of_fermat5Equation` supplies an order comparison between bases.
- `gap_pos_of_fermat5Equation` supplies positivity of the concrete difference `z-y`.

When later code treats the gap as a variable, keeping this theorem under a separate name is useful. It is better viewed as a thin bridge exposing a different use-form of the same fact than as unnecessary duplication.

## Optimization candidates

The proof is already essentially minimal, leaving almost no computational optimization opportunity.

Possible API-level improvements include:

- standardizing whether later modules use the order form or the gap-positivity form as their main entry point;
- adding a wrapper theorem from `CounterexamplePack` if gap positivity is repeatedly extracted from that structure;
- constructing the order proof once and reusing it locally when both forms are needed.

Inlining and deleting this theorem could make the later proof's intent less visible, even though the implementation is only one line.

## Required Mathlib imports and import optimization

The standalone file uses `import Mathlib`, so the repository confirms that this theorem is available in the current environment.

The theorem-specific Mathlib dependency is mainly `Nat.sub_pos_of_lt`. However, the preceding `right_lt_of_fermat5Equation` also uses `pow_pos`, `Nat.pow_lt_pow_iff_left`, and `omega`, so the minimum import set for the whole `Basic.lean` module cannot be inferred from this one-line theorem alone.

Import minimization should be performed on the complete module, using tools such as `#min_imports`, followed by a clean build. The exact minimal import names remain unverified in this article.

## Comparator challenge suitability

This theorem is suitable as a beginner-level challenge:

```lean
example {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    0 < z - y := by
  -- fill here
```

Three proof styles can be compared:

1. a one-line proof using `right_lt_of_fermat5Equation` and `Nat.sub_pos_of_lt`;
2. a readability-oriented proof that first states `have hyz : y < z := ...`;
3. a direct proof that unfolds `Fermat5Equation` and repeats the arithmetic argument.

The third style reimplements an existing dependency, so the first or second style is normally preferable. This makes the theorem useful as an API-reuse comparison exercise.

## Next declaration

The next natural declaration is `DkMath.FLT.Five.GN5`.

The proof now has a positive gap $g=z-y$. The definition `GN5 g y` fixes, in local coordinates, the residual factor obtained after extracting `g` from the difference of fifth powers

$$
(g+y)^5-y^5.
$$

This is the entry point to the central factorization kernel of the FLT5 development.

## Evidence and inference

The theorem type, proof term, direct dependencies, use of `Nat.sub_pos_of_lt`, and the source-order transition to `GN5` come directly from the Lean source.

The description of the theorem as an API re-encoding bridge, the wrapper proposal, the Comparator design, and the import-minimization outlook are analysis or unverified proposals. No Lean build was run for this article.

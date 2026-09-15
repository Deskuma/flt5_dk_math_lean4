# 0306 — `GoldenZeroSectorCandidate.square_reconstruction`

## Declaration kind

This declaration is a **`theorem`**.

It appears immediately after 0305 `GoldenZeroSectorCandidate.U_nonneg`, which established nonnegativity of the auxiliary quantity `U`, and records the exact square reconstruction relating `U` to the diagonal coordinate `X` in the zero-sector inversion.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The reconstructed square coordinate is retained exactly. -/
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 := by
  unfold zeroSectorU
  ring
```

The conclusion is the integer equality

```lean
zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2
```

## Mathematical meaning

As recorded in the preceding declaration, the definitions are

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s

def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

Hence

$$
X(r,s)=2r+s,
$$

and

$$
U(r,s)=X(r,s)^2+5s^2.
$$

Subtracting $5s^2$ from the definition gives

$$
U(r,s)-5s^2=X(r,s)^2.
$$

Thus `U` is not merely a nonnegative auxiliary quantity: it is designed so that, after removing the $5s^2$ term, the remainder is **exactly a square**. This theorem exposes that design invariant as a named API fact.

## Role in the full proof

Declaration 0305 `U_nonneg` provided the order statement

$$
U\ge0.
$$

Declaration 0306 gives the stronger exact algebraic reconstruction

$$
U-5s^2=X^2.
$$

The next declaration, 0307 `GoldenZeroSectorCandidate.discriminant_eq`, moves to the quantities `U` and `W=4d^5` and proves the difference-of-squares identity

$$
U^2-W^2=20s^4.
$$

Accordingly, 0306 marks the point where `U` is shown to retain the original square-coordinate information rather than being an opaque auxiliary variable.

There is, however, an important implementation distinction. The current Lean proof of 0307 does not rewrite with 0306 directly; instead it unfolds `zeroSectorU` and performs a `ring` calculation. Thus 0306 is a conceptual and API-level foundation for the later inversion algebra, but it is **not a direct proof dependency of the current implementation of 0307**.

## Direct dependencies

### `zeroSectorU`

This is the definition unfolded directly by the proof.

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

After unfolding, the goal is essentially

```lean
zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2 - 5 * p.s ^ 2 =
  zeroSectorX p.r p.s ^ 2
```

which is a pure ring identity.

### `zeroSectorX`

This is the squared diagonal coordinate occurring inside `zeroSectorU`.

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

The theorem does not need to unfold `zeroSectorX`. For `ring`, the expression `zeroSectorX p.r p.s` may remain an atomic element of the integer ring.

### `ring`

Mathlib's ring-normalization tactic closes the equality after unfolding `zeroSectorU`.

No candidate-specific hypothesis, coprimality statement, positivity fact, parity condition, or five-adic exclusion is used.

## Proof flow

1. `unfold zeroSectorU` expands the left-hand side by definition.
2. The goal becomes, conceptually,

   ```lean
   X ^ 2 + 5 * s ^ 2 - 5 * s ^ 2 = X ^ 2
   ```
3. `ring` normalizes addition, multiplication, subtraction, and powers in `ℤ` and verifies that both sides are the same polynomial expression.
4. The proof finishes without using any field of `GoldenZeroSectorCandidate` other than the coordinates `p.r` and `p.s`.

On paper, this is a one-line substitution-and-cancellation argument.

## Lean-specific processing

The key Lean-specific design choice is to unfold only `zeroSectorU`, leaving `zeroSectorX` abstract:

```lean
unfold zeroSectorU
ring
```

This works because `ring` does not need to know that `zeroSectorX p.r p.s = 2 * p.r + p.s`; it can treat `zeroSectorX p.r p.s` as a ring atom.

This mirrors the proof style of 0305: unfold only the definition needed to expose the relevant algebraic shape. It improves robustness. If the internal formula for `zeroSectorX` changed while `zeroSectorU` retained the form `X² + 5s²`, this proof would still remain valid.

Although the target is simple enough that alternative proofs may exist, the present `unfold` + `ring` formulation is concise and stable.

## Redundancy and duplication

The theorem itself has almost no proof-level redundancy: its proof is only two tactic lines.

Mathematically, however, it is close to a restatement of the definition of `zeroSectorU`. This raises the API-design question of whether such an immediate consequence deserves a separate declaration.

There is a good reason to keep it: later code can refer to the meaningful statement

```lean
p.square_reconstruction
```

instead of repeatedly unfolding `zeroSectorU`. The named theorem therefore acts as an abstraction boundary and communicates the intended interpretation of `U`.

There is also a conceptual duplication with 0307: the current proof of `discriminant_eq` unfolds `zeroSectorU` again rather than using `square_reconstruction`. Whether 0307 can profitably be rewritten around 0306 is a possible refactoring question.

## Optimization candidates

The first natural optimization is the same generalization observed for 0305: the theorem does not actually depend on the candidate hypotheses. One could conceptually introduce

```lean
theorem zeroSector_square_reconstruction (r s : ℤ) :
    zeroSectorU r s - 5 * s ^ 2 = zeroSectorX r s ^ 2 := by
  unfold zeroSectorU
  ring
```

and then make the current theorem a specialization:

```lean
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 :=
  zeroSector_square_reconstruction p.r p.s
```

This would make the candidate-independence explicit in the API and allow reuse outside the candidate namespace.

A second possibility is to investigate whether 0307 `discriminant_eq` becomes clearer if it uses 0306 instead of unfolding `zeroSectorU` again. This is not guaranteed to shorten the proof because 0307 combines a quartic identity with a larger `ring` calculation.

These are **unverified refactoring ideas**. No Lean build was run, and no source code is changed by this museum task.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` is a generated artifact whose manifest lists several `DkMath/FLT/Five/...` source modules. The current standalone environment uses Mathlib broadly.

This theorem directly requires at least:

- the integer ring `ℤ`,
- subtraction, multiplication, and powers,
- the `ring` tactic,
- the definitions `zeroSectorU` and `zeroSectorX`.

Unlike 0305, it does not require the `positivity` tactic. It also does not use `omega`, `linarith`, `norm_num`, or `exact_mod_cast`.

The exact minimal Mathlib import set is **not verified**, because this task explicitly does not run a Lean build. Import optimization should therefore be tested in the original source module by reducing the umbrella imports to the smallest modules that provide the integer-ring infrastructure and ring-normalization tactic.

## Comparator challenge suitability

**Suitable, but at beginner level.**

Given the statement and the definition of `zeroSectorU`, the expected core solution is almost exactly

```lean
unfold zeroSectorU
ring
```

A more useful Comparator challenge would compare proof styles:

- Can the solver see that `zeroSectorX` need not be unfolded?
- Is `ring` or `ring_nf` the more natural choice?
- Can the proof be closed without using any candidate hypothesis?
- How does minimal unfolding compare with fully expanding every auxiliary definition?

The declaration is especially useful for teaching that a function application may remain an atomic ring expression during polynomial normalization.

## Comparison with the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The GitHub connector's normal text-fetch path does not return the body of binary PDFs, so this run could not directly match 0306 to a specific PDF page, section, or equation number. No such location is therefore guessed.

The Lean code, declaration order, direct dependencies, and relation to the following declaration in this explanation are grounded in the repository's `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0307 `GoldenZeroSectorCandidate.discriminant_eq`, also a **`theorem`**.

In the Lean source it immediately follows 0306:

```lean
/-- The diagonal quartic identity becomes a difference of two squares. -/
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4 := by
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq p.r p.s
  rw [p.H_eq_tenth] at hdiag
  unfold zeroSectorU zeroSectorW
  calc
    ...
```

Where 0306 reconstructs the square coordinate through

$$
U-5s^2=X^2,
$$

0307 combines the quartic identity with `H=d^{10}` to obtain

$$
U^2-W^2=20s^4.
$$

This is the entry point to the factorization into the two inversion factors.
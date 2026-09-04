# 0296 — `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`

## Declaration kind

This is a **`theorem`**.

It restores the sign of the visible coordinate `s`: the zero-sector candidate stores an absolute-value tenth-power split, while 0293 `GoldenZeroSectorCandidate.s_neg` has already fixed the sign to be negative. The theorem combines those two pieces into an exact signed equation.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sign removal for the visible coordinate. -/
theorem s_eq_neg_five_pow_mul_tenth (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10) := by
  have habs : (p.s.natAbs : ℤ) =
      (5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10 := by
    exact_mod_cast p.s_natAbs_eq
  have hsabs : (p.s.natAbs : ℤ) = -p.s :=
    Int.ofNat_natAbs_of_nonpos p.s_neg.le
  linarith
```

The conclusion is

$$
p.s=-5^6p.c^{10}.
$$

## Mathematical meaning

0290 `GoldenZeroSectorCandidate` stores the field

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

which corresponds to

$$
|p.s|=5^6p.c^{10}.
$$

Meanwhile, 0293 `p.s_neg` gives

$$
p.s<0.
$$

For a nonpositive integer, $|s|=-s$. Hence

$$
-p.s=5^6p.c^{10},
$$

so

$$
p.s=-5^6p.c^{10}.
$$

Although 0294 `c_pos` supplies mathematically compatible nondegeneracy information, it is not directly used by this Lean proof. Sign removal only needs `s_natAbs_eq` and `s_neg`.

## Role in the full proof

The zero-sector arithmetic layer supplies the split in absolute-value form,

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

This theorem converts the `s` side back into signed arithmetic.

The immediately following 0297 `GoldenZeroSectorCandidate.H_eq_tenth` uses the previously proved positivity $H>0$ to recover

$$
H(r,s)=d^{10}.
$$

Thus 0296 and 0297 form a pair establishing the exact signed data

$$
s=-5^6c^{10},
\qquad
H=d^{10},
$$

which is then consumed by `natAbs_product_eq`, `a_eq_c_mul_d`, `coprime_c_d`, and the later inversion factorization.

## Direct dependencies

### `GoldenZeroSectorCandidate.s_natAbs_eq`

A field of the structure introduced in 0290:

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

This is the theorem's only direct source of magnitude information.

### `GoldenZeroSectorCandidate.s_neg`

The theorem from 0293:

```lean
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0
```

Its `.le` projection weakens the strict inequality to `p.s ≤ 0`, which is the hypothesis needed by the integer absolute-value lemma.

### `Int.ofNat_natAbs_of_nonpos`

From `p.s ≤ 0`, this yields

```lean
(p.s.natAbs : ℤ) = -p.s
```

The cast is important because `natAbs` itself is `ℕ`-valued.

### `exact_mod_cast`

It transports the natural-number equality `p.s_natAbs_eq` to the integer equality

```lean
(p.s.natAbs : ℤ) = (5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10
```

### `linarith`

It combines

```lean
habs  : (p.s.natAbs : ℤ) = (5 : ℤ)^6 * (p.c : ℤ)^10
hsabs : (p.s.natAbs : ℤ) = -p.s
```

and closes the target equality.

## Proof flow

1. Lift `p.s_natAbs_eq` from `ℕ` to `ℤ` with `exact_mod_cast`.
2. Use `p.s_neg.le` and `Int.ofNat_natAbs_of_nonpos` to identify $|s|$ with $-s$.
3. Both equations have the same left-hand side `(p.s.natAbs : ℤ)`, so `linarith` eliminates it and derives $s=-5^6c^{10}$.

Conceptually this is simply “magnitude + sign = signed value”; the zero-sector-specific algebra has already been completed earlier.

## Lean-specific processing

On paper, $s<0$ immediately allows one to write $|s|=-s$. In Lean, however, `Int.natAbs` takes values in `ℕ`, while the target theorem lives in `ℤ`, so a type bridge is necessary.

`exact_mod_cast` transports the stored natural-number split into the integer domain. `Int.ofNat_natAbs_of_nonpos` then directly connects `(s.natAbs : ℤ)` with `-s`. The strict inequality `p.s_neg` is weakened to the required nonpositivity hypothesis with `.le`.

No `ring`, `nlinarith`, `positivity`, `omega`, or `norm_num` call is used in this theorem itself.

## Redundancy and overlap

The theorem is structurally parallel to 0297 `H_eq_tenth`. The difference is the sign direction:

$$
|s|=-s
$$

on the negative side, whereas

$$
|H|=H
$$

on the positive side.

The corresponding Lean lemmas are also different: `Int.ofNat_natAbs_of_nonpos` versus `Int.ofNat_natAbs_of_nonneg`. Abstracting both into a common helper is possible, but may reduce readability because the sign direction is part of the mathematical meaning of each theorem.

The named intermediate equalities `habs` and `hsabs` could be compressed, but retaining them clearly separates the magnitude source from the sign source and is useful pedagogically.

## Optimization candidates

1. `linarith` is solving only a simple equality substitution problem, so it may be replaceable by `rw`, `calc`, or another smaller proof term.
2. One could rewrite `hsabs` into `habs` and finish by symmetry/algebraic rearrangement, potentially reducing tactic dependencies. The exact shortest form is **unverified** because no Lean build was run.
3. A general helper extracting a signed equality from a `natAbs` equality plus a sign hypothesis could serve both 0296 and 0297, but for only two theorems the current explicit proofs keep the proof graph clearer.

The present proof is already short and cleanly separates cast handling from sign removal.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its generated-source boundary identifies this declaration with

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The main facilities directly used by this theorem are:

- `exact_mod_cast`
- `Int.ofNat_natAbs_of_nonpos`
- order projection `.le`
- `linarith`
- `GoldenZeroSectorCandidate.s_neg`

`ring`, `nlinarith`, `positivity`, `omega`, and `norm_num` are not used by this theorem itself.

Per the task constraints, no Lean build was run, so the exact replacement of `import Mathlib` by a minimal set of individual imports is **not verified**. In particular, the smallest combined import set covering `exact_mod_cast`, `linarith`, and the preceding candidate API is not asserted here.

## Comparator challenge suitability

**Suitable.** The difficulty is low to medium.

It tests whether a solver can recognize that `natAbs` is `ℕ`-valued, move the stored equality to `ℤ` with `exact_mod_cast`, discover and reuse the existing `s_neg` theorem, connect it to `Int.ofNat_natAbs_of_nonpos`, and reconstruct the exact signed equation from sign plus magnitude.

A natural challenge shape is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10) := by
  ...
```

with `p.s_natAbs_eq` and `p.s_neg` available.

## Relation to the PDFs

The target branch repository tree contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the GitHub connector does not expose the binary PDF body as analyzable text in this run, so the exact PDF page, section, and matching passage for this theorem are **not confirmed**. The current Lean source `Flt5DkMath/FLT5StandAlone.lean` is therefore treated as the primary source, and no unsupported claim about PDF location is made.

## Next declaration to read

Next is **0297 `GoldenZeroSectorCandidate.H_eq_tenth`**, also a `theorem`.

```lean
/-- Exact sign removal for the positive quartic factor. -/
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  have habs : ((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
      (p.d : ℤ) ^ 10 := by
    exact_mod_cast p.H_natAbs_eq
  rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs
  exact habs
```

Where 0296 removes the absolute value from the negative visible coordinate, 0297 uses the positivity established in 0292 to remove the absolute value from the quartic factor and recover

$$
H(p.r,p.s)=p.d^{10}.
$$
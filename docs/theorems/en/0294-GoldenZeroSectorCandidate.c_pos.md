# 0294 — `GoldenZeroSectorCandidate.c_pos`

## Declaration kind

This declaration is a **`theorem`**.

After 0293 `GoldenZeroSectorCandidate.s_neg` fixes the visible coordinate `s` to be strictly negative, this theorem uses the field `s_natAbs_eq` stored in 0290 `GoldenZeroSectorCandidate`, corresponding to

$$
|s|=5^6c^{10},
$$

to show that the tenth-power base `c` cannot vanish.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The tenth-power base in the visible coordinate is nonzero. -/
theorem c_pos (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  by_contra hc
  have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
  have hsAbsZero : p.s.natAbs = 0 := by
    simpa [hc0] using p.s_natAbs_eq
  have hs0 : p.s = 0 := Int.natAbs_eq_zero.mp hsAbsZero
  have hsneg := p.s_neg
  omega
```

The conclusion is

$$
0<p.c.
$$

Since `p.c : ℕ`, this is the natural-number positivity form of the stronger usable fact that `p.c` is nonzero.

## Mathematical meaning

The candidate stores

$$
|p.s|=5^6p.c^{10}.
$$

From 0293 we already know

$$
p.s<0,
$$

hence in particular

$$
p.s\neq0.
$$

If $p.c=0$, then

$$
|p.s|=5^6\cdot0^{10}=0.
$$

An integer with absolute value zero is zero, so this would imply $p.s=0$, contradicting $p.s<0$.

Therefore

$$
p.c\neq0.
$$

For a natural number, nonzero is equivalent to being positive, so

$$
0<p.c.
$$

## Role in the full proof

The tenth-power split supplied by the zero-sector arithmetic layer is retained in the natural-number form

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

The inversion layer must treat `c` and `d` not as arbitrary natural parameters but as genuine **positive tenth-power scales**.

0293 recovers the sign of `s`; theorem 0294 then rules out the degenerate case `c=0`. The immediately following theorem 0295 `GoldenZeroSectorCandidate.d_pos` performs the symmetric task for the quartic-factor base `d`.

Thus 0294 and 0295 form a small gateway pair certifying that both bases appearing in the absolute-value tenth-power split are nondegenerate quantities available to the later zero-sector inversion.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The structure introduced in 0290. The fields used directly here are

```lean
p.c : ℕ
p.s : ℤ
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

### `GoldenZeroSectorCandidate.s_neg`

Theorem 0293:

```lean
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0
```

This supplies the strict sign information used to contradict `p.s = 0`.

### `Nat.eq_zero_of_not_pos`

After `by_contra hc`, the hypothesis is `¬ 0 < p.c`. For a natural number this lemma converts it to

```lean
p.c = 0
```

### `Int.natAbs_eq_zero`

This converts

```lean
p.s.natAbs = 0
```

back to the integer equality

```lean
p.s = 0
```

### `simpa`

After rewriting by `p.c = 0`, `p.s_natAbs_eq` has right-hand side

```lean
5 ^ 6 * 0 ^ 10
```

which `simpa` reduces to zero.

### `omega`

The final contradiction is purely linear integer arithmetic:

```lean
p.s = 0
p.s < 0
```

and `omega` closes it.

## Proof flow

### 1. Negate positivity

```lean
by_contra hc
```

The goal `0 < p.c` is negated, giving `hc : ¬ 0 < p.c`.

### 2. Force the natural number `c` to zero

```lean
have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
```

A nonpositive natural number can only be zero.

### 3. Use the tenth-power split to obtain `|s| = 0`

```lean
have hsAbsZero : p.s.natAbs = 0 := by
  simpa [hc0] using p.s_natAbs_eq
```

This is simply the stored identity

$$
|s|=5^6c^{10}
$$

with $c=0$ substituted.

### 4. Convert zero absolute value back to `s = 0`

```lean
have hs0 : p.s = 0 := Int.natAbs_eq_zero.mp hsAbsZero
```

The proof returns from the natural-valued absolute value to the original integer coordinate.

### 5. Contradict the strict negativity from 0293

```lean
have hsneg := p.s_neg
omega
```

The equalities `p.s = 0` and `p.s < 0` are incompatible, so the contradiction closes the proof.

## Lean-specific processing

The main Lean-specific point is that the proof moves between `c : ℕ` and `s : ℤ` through `natAbs`, rather than through casts.

The field `p.s_natAbs_eq` is already an equality in `ℕ`, so no `exact_mod_cast` is required. Rewriting `c=0` and simplifying the natural-number powers is delegated to `simpa`.

Then `Int.natAbs_eq_zero.mp` explicitly transports the zero-absolute-value fact back to an equality in `ℤ`, after which `omega` solves the elementary contradiction.

Accordingly, this theorem does not need `ring`, `nlinarith`, `positivity`, `norm_num`, or `exact_mod_cast` in its proof body.

## Redundancy and repetition

### Structural repetition with 0295 `d_pos`

The next theorem has essentially the same proof schema:

- assume `p.d = 0`,
- use `p.H_natAbs_eq` to force the quartic factor's `natAbs` to zero,
- recover equality to zero for the integer quartic factor,
- contradict `p.H_pos`.

This is better viewed as a deliberate symmetric presentation than as harmful duplication. A shared abstraction is possible, but for proofs this short the separate theorems keep the dependency graph and mathematical roles easier to read.

### Explicit `hs0`

A shorter term-style proof might combine `Int.natAbs_eq_zero` and `p.s_neg` more directly. The named intermediate fact

```lean
hs0 : p.s = 0
```

however makes the mathematical contradiction completely explicit.

## Optimization candidates

1. One could first prove `p.c ≠ 0` and then convert nonzeroness to positivity with an appropriate natural-number lemma such as the `Nat.pos_of_ne_zero` family. The current `by_contra` plus `Nat.eq_zero_of_not_pos` form is already compact.
2. The patterns of 0294 and 0295 could potentially be abstracted into a generic statement saying that if `natAbs x = K * n^k` and `x ≠ 0`, then `0 < n`, under suitable positivity assumptions on the exponent and coefficient. The abstraction cost is likely larger than the local duplication.
3. The final `omega` handles only the contradiction between `p.s = 0` and `p.s < 0`; a basic order lemma could likely replace it. The exact shortest API was not verified because no Lean build or API exploration is performed in this task.

The current proof is therefore already close to optimal in clarity and practical size.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and the manifest places this declaration in the generated source module

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The theorem itself directly relies mainly on

- `Nat.eq_zero_of_not_pos`,
- `Int.natAbs_eq_zero`,
- `simpa`,
- `omega`,
- `GoldenZeroSectorCandidate.s_neg`.

It does not itself use `ring`, `nlinarith`, `positivity`, `norm_num`, or `exact_mod_cast`.

Per the task constraints, no Lean build is run, so the exact minimal replacement for `import Mathlib` is **not verified**. In particular, the smallest imports required for `omega` together with all preceding candidate definitions are not asserted here.

## Comparator challenge suitability

**Suitable.**

Despite being short, the theorem tests several useful proof-search skills:

1. recognizing that nonpositivity of a natural number forces zero,
2. rewriting the structure field `s_natAbs_eq`,
3. using `Int.natAbs_eq_zero` to return to the integer domain,
4. discovering the existing theorem `p.s_neg`,
5. closing the final contradiction with arithmetic or order reasoning.

A suitable challenge form is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  ...
```

with use of `s_natAbs_eq` and `s_neg` permitted.

The difficulty is low, but the `Nat`/`Int.natAbs` boundary makes it a useful instructional comparator.

## Relation to the PDFs

The target branch contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, in this run the GitHub connector could not expose the binary PDF bodies as analyzable text, and an external raw-PDF fetch also failed. Therefore the exact PDF page, section, or wording corresponding to this theorem is **not confirmed**. The current Lean source `Flt5DkMath/FLT5StandAlone.lean` is treated as the highest-priority canonical evidence, and no unverified PDF correspondence is inferred.

## Next declaration to read

The next declaration is **0295 `GoldenZeroSectorCandidate.d_pos`**, also a `theorem`:

```lean
/-- The tenth-power base in the quartic factor is nonzero. -/
theorem d_pos (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  by_contra hd
  have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
  have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
    simpa [hd0] using p.H_natAbs_eq
  have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
    Int.natAbs_eq_zero.mp hHAbsZero
  have hHpos := p.H_pos
  omega
```

Where 0294 certifies positivity of the visible-coordinate tenth-power base `c`, 0295 applies the same nondegeneracy pattern to the quartic-factor base `d`. Together they establish positivity of both tenth-power scales required by the inversion layer.
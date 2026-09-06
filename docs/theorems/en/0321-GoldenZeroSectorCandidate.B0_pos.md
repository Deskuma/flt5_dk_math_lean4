# 0321 — `GoldenZeroSectorCandidate.B0_pos`

## Declaration kind

This declaration is a **`theorem`**.

It is the positivity bridge asserting that the natural-number representative $B_0$ of the upper inversion factor, introduced in 0317 `GoldenZeroSectorCandidate.B0`, is not zero but strictly positive. It is the upper-factor counterpart of 0320 `A0_pos`.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

theorem B0_pos (p : GoldenZeroSectorCandidate) : 0 < p.B0 := by
  by_contra hpos
  have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.B0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hBpos := p.B_pos
  omega
```

Its type is

```lean
0 < p.B0
```

with the strict order on `ℕ`. Here `p.B0 : ℕ` is defined as the `natAbs` of the signed upper inversion factor `zeroSectorB p.r p.s p.d : ℤ`.

## Mathematical statement

In 0317 one defines

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

and 0313 `B_pos` has already proved

$$
0<B.
$$

Moreover, 0319 `B0_cast` gives

$$
(B_0:\mathbb Z)=B.
$$

Therefore, if $B_0=0$, casting to the integers forces $B=0$, contradicting $B>0$. Hence

$$
B_0>0.
$$

This theorem records that elementary but necessary fact as a named API theorem for later arithmetic over natural-number factors.

## Role in the full proof

In the zero-sector inversion phase, the signed integer factors

$$
A=U-W,\qquad B=U+W
$$

already satisfy

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

and

$$
0<A<B.
$$

Declarations 0316–0319 build the bridge

$$
A_0=|A|,\qquad B_0=|B|,
$$

$$
(A_0:\mathbb Z)=A,\qquad(B_0:\mathbb Z)=B
$$

from `ℤ` to `ℕ`. Together, 0320 `A0_pos` and the present 0321 `B0_pos` establish

$$
0<A_0,\qquad0<B_0.
$$

The following declaration, 0322 `A0_mul_B0`, transports the signed product identity into the natural-number world and obtains

$$
A_0B_0=4Q^5.
$$

Thus this theorem completes the positivity/nonzeroness preparation for the upper factor immediately before the proof enters natural-number factorization arithmetic.

## Direct dependencies

### `GoldenZeroSectorCandidate.B0`

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

This defines the object appearing in the goal. The current proof does not unfold it directly; instead it uses `B0_cast`.

### `GoldenZeroSectorCandidate.B0_cast`

Proved in 0319:

```lean
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

This is the equality bridge between the natural representative $B_0$ and the signed integer factor $B$.

### `GoldenZeroSectorCandidate.B_pos`

Proved in 0313:

$$
0<B.
$$

The current proof introduces it at the end as `have hBpos := p.B_pos`, and the contradiction with $B=0$ is then discharged by `omega`.

### `Nat.eq_zero_of_not_pos`

This Mathlib lemma turns `¬ 0 < n` into `n = 0` for a natural number. Here it constructs

```lean
have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
```

from the contradiction hypothesis.

## Proof flow

1. `by_contra hpos` assumes `¬ 0 < p.B0`.
2. Since a natural number cannot be negative, `Nat.eq_zero_of_not_pos hpos` yields `p.B0 = 0`.
3. `p.B0_cast` is copied into `hcast`, retaining $(B_0:\mathbb Z)=B$.
4. `rw [hzero] at hcast` rewrites $B_0$ to zero inside that local equality.
5. `norm_num at hcast` simplifies the cast of natural-number zero to the corresponding integer expression, effectively producing $0=B$.
6. `p.B_pos` supplies $0<B$.
7. `omega` closes the contradiction between $B=0$ and $0<B$.

The mathematical argument is tiny, but Lean must explicitly cross the type boundary between positivity on `ℕ` and positivity of the original factor on `ℤ`.

## Lean-specific processing

### `by_contra`

Instead of constructing positivity directly, the proof assumes its negation. On `ℕ`, failure of strict positivity immediately collapses to equality with zero.

### `rw ... at ...`

```lean
rw [hzero] at hcast
```

rewrites only the local hypothesis `hcast`, not the goal. It transports the natural-number equality `B0 = 0` into the integer cast equation.

### `norm_num`

After rewriting, `norm_num` simplifies artifacts such as the cast of `(0 : ℕ)` into `ℤ`. It adds no new number-theoretic content; it merely normalizes the expression for the final arithmetic solver.

### `omega`

By the final step all nonlinear fifth-power and factorization information has been hidden behind theorem APIs. What remains is only the linear order contradiction $B=0$ and $0<B$, which lies in Presburger arithmetic and is closed by `omega`.

## Redundancy and duplication

The proof is almost perfectly symmetric with 0320 `A0_pos`. The substitutions are only

- `A0` ↔ `B0`,
- `A0_cast` ↔ `B0_cast`,
- `A_pos` ↔ `B_pos`.

A generic helper could therefore eliminate code duplication in principle. However, keeping separate named theorems for lower and upper factor positivity has practical API value: later proofs can use dot notation directly, and failures are localized to the relevant factor. The duplication is therefore reasonable as semantic API duplication rather than accidental repetition.

The local alias `have hBpos := p.B_pos` might also be shortened, but the current form keeps the proof phases visually separated: first derive the zero equality through the cast bridge, then introduce signed positivity and close the contradiction.

## Optimization candidates

Because `B0` is literally `natAbs B` and `B_pos` is already known, a Mathlib lemma about positivity or nonzeroness of `Int.natAbs` may permit a shorter proof that bypasses `B0_cast`. Conceptually:

```lean
  unfold B0
  -- derive zeroSectorB ... ≠ 0 from p.B_pos
  -- apply a natAbs positivity lemma
```

This run does not perform a Lean build, so the exact available lemma name, argument order, and import requirements are **unverified**.

Another possibility is to retain the current public API but let `omega` consume `B0_cast` and `B_pos` more directly, perhaps eliminating some of the explicit contradiction plumbing. That too is unverified without compiling.

A direct `natAbs` proof may be shorter, whereas the present proof has the structural advantage of actually consuming the immediately preceding correctness theorem `B0_cast`, keeping the signed-to-natural bridge explicit.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The principal Mathlib features used directly by this theorem are

- `Nat.eq_zero_of_not_pos`,
- the `norm_num` tactic,
- the `omega` tactic,
- coercion from `ℕ` to `ℤ`,
- basic order infrastructure for naturals and integers.

`B0`, `B0_cast`, and `B_pos` are project-local upstream declarations.

For this theorem in isolation, a substantially narrower import set than all of `Mathlib` is likely possible, with `Mathlib.Tactic.Omega`, `Mathlib.Tactic.NormNum`, and modules providing natural/integer casts and order as likely components. However, the **exact minimal import set has not been verified without a Lean build**, especially when considering the dependency closure of the generated standalone file.

## Comparator challenge suitability

**Suitable. It makes a good small-to-medium Lean proof comparator challenge.**

Useful alternatives to compare include:

1. the current `B0_cast` → contradiction → `norm_num` → `omega` route;
2. a direct proof using a `natAbs` positivity lemma;
3. a proof retaining `B0_cast` while reducing the number of tactics;
4. a shared helper abstracting both 0320 `A0_pos` and 0321 `B0_pos`.

Evaluation should consider not only term length but also reuse of the existing API, clarity of the `ℕ`/`ℤ` boundary, coupling to specific Mathlib lemmas, symmetry of the lower/upper factor API, and robustness under future definition changes.

## Cross-check against the PDFs

The target branch contains both existing PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub connector's ordinary text fetch does not return binary PDF contents, so this run could not directly verify the exact page, section, or displayed equation corresponding to 0321 `B0_pos`. Those locations are therefore **unverified**, and no page or equation number is guessed here.

The Lean code, declaration order, dependency on `B0_cast` / `B_pos`, and the following `A0_mul_B0` declaration were checked against the current `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is 0322 `GoldenZeroSectorCandidate.A0_mul_B0`, also a **`theorem`**.

The current Lean source continues immediately with

```lean
/-- Natural product identity inherited from the positive integer factors. -/
theorem A0_mul_B0 (p : GoldenZeroSectorCandidate) :
    p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5 := by
  have hprod := p.factor_product
  rw [← p.A0_cast, ← p.B0_cast] at hprod
  exact_mod_cast hprod
```

With positivity of both $A_0$ and $B_0$ established in 0320–0321, declaration 0322 begins the reconstruction of the signed integer factor identities as natural-number factorization arithmetic.

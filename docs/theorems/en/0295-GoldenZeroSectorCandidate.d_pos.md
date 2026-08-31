# 0295 — `GoldenZeroSectorCandidate.d_pos`

## Declaration kind

This declaration is a **`theorem`**.

Where 0294 `GoldenZeroSectorCandidate.c_pos` establishes positivity of the tenth-power base `c` on the visible-coordinate side, this theorem proves that the quartic-factor base `d` cannot vanish.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

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

The conclusion is

$$
0<p.d.
$$

Since `p.d : ℕ`, the theorem packages nonvanishing of the quartic-factor tenth-power base in the stronger and more useful natural-number form of strict positivity.

## Mathematical meaning

The structure introduced in 0290 stores the quartic factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

through the absolute-value tenth-power identity

$$
|H(p.r,p.s)|=p.d^{10}.
$$

Meanwhile 0292 `GoldenZeroSectorCandidate.H_pos` has already shown

$$
H(p.r,p.s)>0.
$$

If $p.d=0$, then

$$
|H(p.r,p.s)|=0^{10}=0,
$$

hence

$$
H(p.r,p.s)=0.
$$

That contradicts strict positivity. Therefore

$$
p.d\neq0,
$$

and because `p.d` is a natural number,

$$
0<p.d.
$$

## Role in the full proof

The tenth-power split passed from zero-sector arithmetic into the inversion layer is stored in the absolute-value form

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

After 0293 fixes $s<0$ and 0294 proves $c>0$, theorem 0295 establishes $d>0$. Thus both split bases `c` and `d` are certified as nondegenerate.

This is more than bookkeeping. The immediately following theorems 0296 `s_eq_neg_five_pow_mul_tenth` and 0297 `H_eq_tenth` remove the absolute values and recover the exact signed identities

$$
s=-5^6c^{10},
\qquad
H=d^{10}.
$$

Those identities then feed `a_eq_c_mul_d`, `coprime_c_d`, and the later inversion factorization. In this sense, 0294–0295 form the final nondegeneracy gate before the proof moves from absolute-value data to exact signed arithmetic.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The structure introduced in 0290. The fields used directly here are

```lean
p.d : ℕ
p.r : ℤ
p.s : ℤ
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

### `GoldenZeroSectorCandidate.H_pos`

Theorem 0292:

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

This is the main nonvanishing input for the quartic factor.

### `Nat.eq_zero_of_not_pos`

After `by_contra hd`, Lean has

```lean
hd : ¬ 0 < p.d
```

and this lemma turns that into

```lean
p.d = 0.
```

### `Int.natAbs_eq_zero`

It converts

```lean
(goldenFifthSndFactor p.r p.s).natAbs = 0
```

back into the integer equality

```lean
goldenFifthSndFactor p.r p.s = 0.
```

### `simpa`

After rewriting by `p.d = 0`, the stored field `p.H_natAbs_eq` has right-hand side `0 ^ 10`, which simplifies to zero.

### `omega`

The final contradiction is purely order-theoretic integer arithmetic:

```lean
hH0   : goldenFifthSndFactor p.r p.s = 0
hHpos : 0 < goldenFifthSndFactor p.r p.s
```

and `omega` closes it.

## Proof flow

### 1. Negate positivity of `d`

```lean
by_contra hd
```

### 2. Force the natural number `d` to zero

```lean
have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
```

For a natural number, failure of strict positivity means zero.

### 3. Use the tenth-power split to obtain `|H| = 0`

```lean
have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
  simpa [hd0] using p.H_natAbs_eq
```

This is simply

$$
|H|=d^{10}
$$

specialized at $d=0$.

### 4. Convert zero absolute value back to `H = 0`

```lean
have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
  Int.natAbs_eq_zero.mp hHAbsZero
```

### 5. Contradict strict positivity from 0292

```lean
have hHpos := p.H_pos
omega
```

The statements `H=0` and `H>0` are incompatible, so the negated positivity assumption is discharged.

## Lean-specific processing

The proof follows almost exactly the same Lean pattern as 0294 `c_pos`:

1. turn nonpositivity of a natural number into equality with zero using `Nat.eq_zero_of_not_pos`;
2. specialize a stored `natAbs` identity with `simpa`;
3. move from `natAbs = 0` back to an integer equality with `Int.natAbs_eq_zero.mp`;
4. close the contradiction against a strict-positivity theorem using `omega`.

No cast transport is needed. The field `H_natAbs_eq` is already an equality in `ℕ`, while `H_pos` refers directly to the same integer-valued quartic expression.

Accordingly, the proof body does not use `ring`, `nlinarith`, `positivity`, `norm_num`, or `exact_mod_cast`.

## Redundancy and repetition

### Symmetric repetition with 0294 `c_pos`

The previous theorem has the pattern

```text
c=0 → |s|=0 → s=0 → contradiction with s<0
```

whereas the present theorem has

```text
d=0 → |H|=0 → H=0 → contradiction with H>0.
```

A shared abstraction is possible, but the contradiction sources differ: 0294 depends on `s_neg`, while 0295 depends on `H_pos`. Keeping the statements separate therefore makes the proof graph and mathematical roles easier to read.

### Explicit intermediate `hH0`

One could compress the proof by using `Int.natAbs_eq_zero.mp hHAbsZero` directly in the final contradiction. The named fact

```lean
hH0 : goldenFifthSndFactor p.r p.s = 0
```

makes the mathematical failure point explicit and improves readability.

## Optimization candidates

1. One could first prove `p.d ≠ 0` and then derive `0 < p.d` using a natural-number positivity lemma. The current `by_contra` plus `Nat.eq_zero_of_not_pos` proof is already compact.
2. The shared schema of 0294 and 0295 could be abstracted to a generic lemma deriving positivity of `n` from an identity of the form `x.natAbs = n^k` and nonvanishing of `x`. With only two applications, however, the abstraction cost may exceed the benefit.
3. The final `omega` only handles the contradiction between `H=0` and `H>0`; a smaller order lemma could likely replace it. The exact shortest API was not verified because no Lean build or API exploration is performed in this task.

The current proof is therefore already close to optimal for clarity and symmetry.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its manifest places this declaration in

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The theorem itself directly relies mainly on

- `Nat.eq_zero_of_not_pos`,
- `Int.natAbs_eq_zero`,
- `simpa`,
- `omega`,
- `GoldenZeroSectorCandidate.H_pos`.

It does not itself use `ring`, `nlinarith`, `positivity`, `norm_num`, or `exact_mod_cast`.

Per the task constraints, no Lean build is run. Therefore the exact minimal replacement for `import Mathlib` is **not verified**, especially when the imports needed by the preceding zero-sector definitions and the `omega` tactic are taken into account.

## Comparator challenge suitability

**Suitable.**

Although short, the theorem tests several useful capabilities:

1. locating the structure field `H_natAbs_eq`;
2. reducing nonpositivity of a natural number to zero;
3. moving from `natAbs = 0` back to an integer equality;
4. discovering and reusing the existing theorem `H_pos`;
5. recognizing the proof symmetry with 0294.

A suitable challenge form is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  ...
```

with use of `p.H_natAbs_eq` and `p.H_pos` permitted.

The difficulty is low, but the theorem is a clean test of structure-field reuse and the `Nat`/`Int.natAbs` boundary.

## Relation to the PDFs

The target branch contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, in this run the GitHub connector could not expose the binary PDF bodies as analyzable text, and an external raw-PDF fetch also failed. Therefore the exact PDF page, section, or wording corresponding to this theorem is **not confirmed**. The current Lean source `Flt5DkMath/FLT5StandAlone.lean` is treated as the highest-priority canonical evidence, and no unverified PDF correspondence is inferred.

## Next declaration to read

The next declaration is **0296 `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`**, also a `theorem`:

```lean
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

Using the sign information $s<0$ from 0293 together with the stored identity $|s|=5^6c^{10}$, it removes the absolute value and recovers the exact signed equation

$$
s=-5^6c^{10}.
$$
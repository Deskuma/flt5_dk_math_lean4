# 0293 — `GoldenZeroSectorCandidate.s_neg`

## Declaration kind

This declaration is a **`theorem`**.

It combines the strict negativity of the product obtained in 0291 `GoldenZeroSectorCandidate.product_neg` with the nonnegativity of the quartic factor from 0289 `goldenFifthSndFactor_nonneg`, and thereby forces the visible zero-sector coordinate `s` to have negative sign.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The visible zero-sector coordinate has the forced negative sign. -/
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  rcases mul_neg_iff.mp p.product_neg with h | h
  · exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
  · exact h.1
```

The conclusion is exactly

$$
p.s<0.
$$

Writing

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
$$

the available information is

$$
p.s\,H(p.r,p.s)<0,
\qquad
H(p.r,p.s)\ge0,
$$

and this theorem extracts `p.s < 0` from those two facts.

## Mathematical meaning

In an ordered ring such as the integers, a negative product means that its two factors have opposite signs. Lean's `mul_neg_iff` exposes this as an explicit disjunction.

Conceptually,

$$
ab<0
\iff
(a>0\land b<0)\lor(a<0\land b>0).
$$

Here set

$$
a=p.s,
\qquad
b=H(p.r,p.s).
$$

The first possibility,

$$
p.s>0,
\qquad
H(p.r,p.s)<0,
$$

contradicts the already established result from 0289,

$$
H(p.r,p.s)\ge0.
$$

Therefore only the second possibility remains:

$$
p.s<0,
\qquad
H(p.r,p.s)>0.
$$

In particular,

$$
p.s<0.
$$

The immediately preceding theorem 0292 `H_pos` has already proved the stronger statement

$$
H(p.r,p.s)>0,
$$

but the current Lean proof deliberately does not refer to it. Instead it returns to the weaker general theorem 0289 `goldenFifthSndFactor_nonneg` and eliminates the impossible sign branch directly. This is an important point for the redundancy and optimization discussion below.

## Role in the overall proof

The zero-sector inversion must eventually recover signed integer equations from tenth-power data initially recorded through absolute values.

0290 `GoldenZeroSectorCandidate` stores, for the visible coordinate, data corresponding to

$$
|s|=5^6c^{10}
$$

through its field `s_natAbs_eq`. But an absolute-value identity alone does not determine whether

$$
s=+5^6c^{10}
$$

or

$$
s=-5^6c^{10}.
$$

This theorem determines that sign.

The preceding sign chain is

$$
16H=X^4+10X^2s^2+5s^4
\Longrightarrow
H\ge0,
$$

$$
sH=-5^6a^{10}<0,
$$

hence

$$
s<0.
$$

Once the sign is fixed, later declarations can combine it with `s_natAbs_eq` and convert absolute-value information back into a signed equality. The immediately following 0294 `GoldenZeroSectorCandidate.c_pos` first guarantees that $c\neq0$, preparing the tenth-power scale to be used as a positive quantity in the subsequent zero-sector inversion.

Thus 0293 is a **sign-recovery theorem that reconnects unsigned natural-number absolute-value data with the original integer coordinate**.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The `structure` introduced in 0290. This theorem uses its integer coordinates

```lean
p.r : ℤ
p.s : ℤ
```

and theorems attached to the corresponding namespace.

### `GoldenZeroSectorCandidate.product_neg`

The theorem from 0291:

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0
```

This is the main input to the proof and is obtained using dot notation as `p.product_neg`.

### `goldenFifthSndFactor_nonneg`

The theorem from 0289:

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s
```

It excludes the branch in which the quartic factor would be negative.

### `mul_neg_iff`

An order lemma decomposing negativity of a product into the two possible opposite-sign configurations.

The current code applies

```lean
mul_neg_iff.mp p.product_neg
```

and then splits the resulting disjunction with

```lean
rcases ... with h | h
```

### `not_lt_of_ge`

This combines

```lean
0 ≤ goldenFifthSndFactor p.r p.s
```

with the strict negativity of the same quantity obtained in the first branch and derives a contradiction.

### `False.elim` / `.elim`

In

```lean
(not_lt_of_ge (...) h.2).elim
```

the contradiction is converted into the target `p.s < 0`. Lean uses `.elim` as method-style notation for elimination from `False`.

## Proof flow

### 1. Convert the negative product into sign cases

```lean
rcases mul_neg_iff.mp p.product_neg with h | h
```

0291 supplies

```lean
p.product_neg :
  p.s * goldenFifthSndFactor p.r p.s < 0
```

and `mul_neg_iff.mp` turns it into the two conceptual branches

$$
(p.s>0\land H<0)
\lor
(p.s<0\land H>0).
$$

### 2. Eliminate the first branch using nonnegativity of the quartic factor

```lean
· exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
```

In the first branch, `h.2` says that the quartic factor is strictly negative. But 0289 proves that the same factor is nonnegative.

Thus one has simultaneously

$$
H\ge0
\quad\text{and}\quad
H<0,
$$

which is impossible. The branch is closed by eliminating `False`.

### 3. Read `s < 0` directly from the second branch

```lean
· exact h.1
```

In the second branch the first component is already

```lean
h.1 : p.s < 0
```

so the theorem is complete.

## Lean-specific processing

This theorem performs no algebraic expansion and no numerical computation. Its proof is purely about the logical structure of the order API.

First, `mul_neg_iff` returns a **disjunction**, rather than a single directed implication, so `rcases` is used to handle the two sign configurations explicitly.

Second, `product_neg` is not a field of the structure, but because its first argument is `p : GoldenZeroSectorCandidate`, Lean's dot notation allows it to be invoked as

```lean
p.product_neg
```

Third, the impossible first branch does not construct the target `p.s < 0` directly. Instead

```lean
not_lt_of_ge ... h.2
```

produces `False`, and `.elim` closes the branch from that contradiction.

The theorem itself does not require tactics such as `ring`, `nlinarith`, `omega`, `positivity`, `norm_num`, or `exact_mod_cast`.

## Redundancy and duplication

### Logical overlap with 0292 `H_pos`

The most visible redundancy is that the immediately preceding theorem 0292 has already established

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

but this theorem does not use `p.H_pos`; it returns to the weaker 0289 theorem `goldenFifthSndFactor_nonneg`.

Mathematically, 0292 together with 0291 gives

$$
H>0,
\qquad
sH<0,
$$

from which $s<0$ follows immediately.

The current implementation does, however, have a dependency advantage: it does not depend on the strict-positivity API introduced in 0292, and can be proved from the more primitive pair 0289 + 0291. Therefore this is not necessarily harmful duplication; it keeps the dependency graph slightly shallower.

### One branch is impossible in this context

The general `mul_neg_iff` theorem produces two cases, but because $H\ge0$ is already known, only one can survive. If Mathlib provides a dedicated order lemma saying that a negative product with a nonnegative right factor forces the left factor to be negative, the explicit case split could potentially be replaced by a single application.

The exact name and applicability of such a lemma were not verified in this run, so no concrete replacement is asserted.

## Optimization candidates

### 1. Use 0292 `H_pos`

If proof dependencies are intended to follow the immediately preceding theorem, the proof could potentially be rewritten around `p.H_pos`, making the mathematical intention more direct.

The exact order lemma needed for the shortest verified Lean form was not checked, so this remains a candidate rather than a proposed patch.

### 2. Use a lemma specialized to a nonnegative right factor

If Mathlib contains a lemma directly deriving `a < 0` from

- `a * b < 0`, and
- `0 ≤ b`,

then the `rcases mul_neg_iff...` branch split could be eliminated.

Again, the specific lemma name is unverified here.

### 3. Keep the current form for pedagogy

For Comparator and teaching purposes, the current proof is particularly clear because it makes the two sign patterns of a negative product visible and shows exactly why one is impossible. Optimizing purely for line count is therefore not necessarily desirable.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its generated manifest places this declaration in the original module

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The functionality directly needed by this theorem is mainly:

- the linear order on integers `ℤ`,
- `mul_neg_iff`,
- `not_lt_of_ge`,
- conjunction/disjunction elimination,
- `rcases`,
- `False.elim`,
- the existing theorem `GoldenZeroSectorCandidate.product_neg`, and
- the existing theorem `goldenFifthSndFactor_nonneg`.

The theorem itself does not use `ring`, `nlinarith`, `omega`, `positivity`, `norm_num`, or `exact_mod_cast`.

Per the task constraints, no Lean build was run. Therefore the exact reduction of `import Mathlib` to a minimal set of individual Mathlib imports is **unverified**, and no minimal import list is claimed.

## Suitability for a Comparator challenge

**Suitable.**

Although short, it can test several useful skills:

1. obtain product-sign information from `p.product_neg`;
2. understand and split the disjunction returned by `mul_neg_iff`;
3. find the nonnegativity theorem from 0289 and use it to eliminate the impossible branch;
4. extract `p.s < 0` from the surviving branch;
5. compare the current shallower dependency route with an alternative proof using the immediately preceding `H_pos` theorem.

A suitable proof-hole challenge is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  ...
```

with `product_neg` and `goldenFifthSndFactor_nonneg` available.

The proof is small, but its core is order-theoretic API discovery and case analysis, so the verdict is **suitable**.

## Relation to the PDFs

The repository tree on the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

Direct raw PDF access was also attempted in this run, but the available retrieval path did not expose either file as an analyzable PDF resource. Therefore the exact PDF page, section, and wording corresponding to this theorem are **unverified** and are not guessed.

The technical basis of this commentary is the actual declaration in `Flt5DkMath/FLT5StandAlone.lean` on the target branch together with its directly preceding and following declarations.

## Next declaration to read

The next declaration is 0294 `GoldenZeroSectorCandidate.c_pos`, again a **`theorem`**.

The authoritative source places it immediately after `s_neg` with the following opening:

```lean
/-- The tenth-power base in the visible coordinate is nonzero. -/
theorem c_pos (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  by_contra hc
  have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
  have hsAbsZero : p.s.natAbs = 0 := by
    simpa [hc0] using p.s_natAbs_eq
  ...
```

After 0293 fixes the sign of the visible coordinate, 0294 establishes that the tenth-power base `c` cannot vanish, namely

$$
0<p.c.
$$

The retrieved source fragment confirmed the beginning of 0294, but the full theorem body is not reconstructed here beyond what was directly verified.

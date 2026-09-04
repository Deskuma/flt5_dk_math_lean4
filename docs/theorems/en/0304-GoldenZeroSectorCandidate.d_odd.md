# 0304 — `GoldenZeroSectorCandidate.d_odd`

## Declaration kind

This declaration is a **`theorem`**.

It combines the oddness of the quartic second-coordinate factor established by 0303 `GoldenZeroSectorCandidate.H_odd` with the exact tenth-power representation established by 0297 `GoldenZeroSectorCandidate.H_eq_tenth`, and concludes that the tenth-power base `d` itself is odd.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Consequently the tenth-power base `d` is odd. -/
theorem d_odd (p : GoldenZeroSectorCandidate) : Odd p.d := by
  have hH := p.H_odd
  rw [p.H_eq_tenth] at hH
  have hdZ : Odd (p.d : ℤ) :=
    (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
  exact_mod_cast hdZ
```

The conclusion is the parity proposition over the natural numbers

```lean
Odd p.d
```

## Mathematical meaning

By 0303,

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

is odd. By 0297,

$$
H(r,s)=d^{10}.
$$

Therefore

$$
d^{10}\text{ is odd}.
$$

For a nonzero positive exponent, if an integer power is odd then its base is odd, hence

$$
d\text{ is odd}.
$$

Equivalently in congruence form, the theorem extracts

$$
d\equiv1\pmod2
$$

from

$$
d^{10}\equiv1\pmod2.
$$

Thus this theorem is a **parity descent**: it transports the 2-adic unit property established on the quartic factor down to the exact power base `d`.

## Role in the full proof

The pair 0301→0302 performs an analogous descent for the prime five:

$$
5\nmid H(r,s)
\Longrightarrow
5\nmid d.
$$

The pair 0303→0304 performs the parity version:

$$
H(r,s)\text{ odd}
\Longrightarrow
 d^{10}\text{ odd}
\Longrightarrow
 d\text{ odd}.
$$

Thus after 0304 the base `d` is known to satisfy at least

$$
2\nmid d,\qquad 5\nmid d.
$$

These are basic arithmetic constraints used later in the zero-sector inversion. In particular, quantities built from `d`, such as `d^5` and `zeroSectorW p.d`, inherit controlled 2-adic and 5-adic behaviour. While 0303 compresses the parity information of primitive coordinates into the quartic factor, 0304 turns that factor-level fact into a base-level invariant that is easier to reuse in later calculations.

## Direct dependencies

### `GoldenZeroSectorCandidate.H_odd`

The immediately preceding theorem 0303. Conceptually its type is

```lean
p.H_odd : Odd (goldenFifthSndFactor p.r p.s)
```

and it is the sole mathematical source of parity information in this theorem.

### `GoldenZeroSectorCandidate.H_eq_tenth`

Theorem 0297, which identifies the quartic factor exactly as a tenth power:

```lean
p.H_eq_tenth :
  goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

This rewrite converts `H_odd` into oddness of `(p.d : ℤ)^10`.

### `Int.odd_pow'`

A Mathlib lemma connecting oddness of an integer power with oddness of its base. Here it is used as

```lean
(Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
```

which yields

```lean
Odd ((p.d : ℤ) ^ 10) → Odd (p.d : ℤ)
```

once the nonzero exponent condition has been supplied.

### `exact_mod_cast`

This transports

```lean
hdZ : Odd (p.d : ℤ)
```

across the natural-to-integer cast boundary to the final goal

```lean
Odd p.d
```

### `decide`

Used to discharge the closed proposition

```lean
10 ≠ 0
```

required by `Int.odd_pow'`.

## Proof flow

1. Obtain the oddness of the quartic factor with `have hH := p.H_odd`.
2. Rewrite `hH` using `p.H_eq_tenth`, changing the proposition from oddness of the quartic polynomial to oddness of `(p.d : ℤ)^10`.
3. Apply the reverse direction `.mp` of `Int.odd_pow'` for the nonzero exponent `10`, obtaining oddness of the integer-cast base `(p.d : ℤ)`.
4. Use `exact_mod_cast hdZ` to move from integer oddness back to oddness of the natural number `p.d` and close the goal.

The mathematical content is extremely short; most of the Lean proof deals with the type boundary between `ℕ` and `ℤ`.

## Lean-specific processing

The main Lean-specific issue is that the candidate field `d` lives in `ℕ`, whereas `goldenFifthSndFactor p.r p.s` lives in `ℤ`.

Consequently, the exact identity from 0297 has the form

```lean
(p.d : ℤ) ^ 10
```

and after

```lean
rw [p.H_eq_tenth] at hH
```

`hH` is an integer parity proposition. This makes `Int.odd_pow'` directly applicable.

The target theorem, however, asks for

```lean
Odd p.d
```

over the natural numbers. The final `exact_mod_cast` performs this last transport.

Also, `Int.odd_pow'` requires explicit evidence that the exponent is nonzero. For the fixed exponent `10`, Lean supplies this with

```lean
by decide : 10 ≠ 0
```

A paper proof would normally omit this trivial condition, but it appears explicitly because it is part of the Mathlib theorem API.

## Redundancy and overlap

There is no substantial redundancy inside this theorem. The four proof lines have clearly separated roles.

Structurally, however, the theorem strongly resembles 0302 `five_not_dvd_d`. Both follow the same transport pattern:

1. obtain a property of the factor,
2. rewrite the factor as `d^10` using `H_eq_tenth`,
3. descend the property from the power to the base.

This is not harmful code duplication so much as an expression of the proof architecture: the zero-sector inversion processes the prime-five channel and the parity-two channel in parallel. Given how short both theorems are, abstracting this pattern would likely reduce readability rather than improve it.

## Optimization candidates

The current proof is already short and readable. One possible micro-optimization would be to inline the intermediate `hdZ`:

```lean
have hH := p.H_odd
rw [p.H_eq_tenth] at hH
exact_mod_cast (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
```

This may elaborate successfully, but it is **not verified here**, because this museum task explicitly does not run a Lean build.

The named intermediate

```lean
hdZ : Odd (p.d : ℤ)
```

is pedagogically useful because it exposes the exact type boundary being crossed. For a theorem-museum explanation, the current form is arguably preferable to the more compressed version.

## Required Mathlib imports and import optimization

The standalone canonical artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The present theorem directly needs at least functionality from the following areas:

- integer parity (`Odd`, `Int.odd_pow'`),
- casts between `ℕ` and `ℤ`,
- `exact_mod_cast`,
- `decide`,
- the local dependency theorems `H_odd` and `H_eq_tenth`.

However, the standalone artifact does not preserve a per-source-module minimal import set, and this task does not run a Lean build. Therefore the exact minimal Mathlib import set is **not confirmed**.

Import optimization should instead be checked in the original DkMath source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`, where the real import graph can be inspected and a reduction from the umbrella `Mathlib` import to parity/cast/tactic-specific modules can be validated by building. No such change is made by this museum task.

## Comparator challenge suitability

**Yes; this is a good small Comparator challenge.**

Although the proof is short, it requires three distinct skills:

1. reusing the existing theorems `H_odd` and `H_eq_tenth`,
2. selecting the correct direction of `Int.odd_pow'` and supplying its nonzero-exponent hypothesis,
3. transporting `Odd (p.d : ℤ)` back to `Odd p.d` across a cast.

A suitable challenge would provide the statement and the preceding facts `H_odd` / `H_eq_tenth`, then leave the proof body as a hole. It is not merely a one-step `simp` exercise: the solver has to discover the rewrite, parity-power lemma, and cast transport.

The difficulty is roughly late-beginner to early-intermediate Lean, especially useful for learning `exact_mod_cast` in a mathematically natural setting.

## Cross-check against the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`, and
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The ordinary GitHub connector text-fetch path does not return the binary PDF contents, so this run could not directly identify the exact PDF page, section, or equation number corresponding to 0304. No page-level correspondence is therefore guessed.

The technical content, Lean code, dependency relation, and declaration order in this explanation use the repository's `Flt5DkMath/FLT5StandAlone.lean` as the canonical source.

## Next declaration to read

The next declaration is 0305 `GoldenZeroSectorCandidate.U_nonneg`, again a **`theorem`**.

In the Lean canonical source it immediately follows `d_odd`:

```lean
/-- The diagonal sum is nonnegative independently of the candidate hypotheses. -/
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  ...
```

After 0304 has established the basic 2-adic and 5-adic constraints on `d`, 0305 begins the analysis of the zero-sector diagonal quantities `U`, `W`, and `X`. This is the start of the sign and identity control needed for the later difference-of-squares and discriminant factorization steps.

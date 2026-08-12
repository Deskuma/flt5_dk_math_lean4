# 0015 — `CleanGN5Channel`

> This document is the English translation of the Japanese canonical edition.

## Lean type

```lean
structure CleanGN5Channel (g y q : ℕ) : Prop where
  prime : Nat.Prime q
  dvd_GN5 : q ∣ GN5 g y
  not_dvd_gap : ¬ q ∣ g
  noLift : ¬ q ^ 2 ∣ GN5 g y
```

The fully qualified name is `DkMath.FLT.Five.CleanGN5Channel`.

## Mathematical statement

`CleanGN5Channel g y q` is proof data asserting that the prime $q$ occurs locally exactly once in the residual kernel `GN5 g y` and does not occur in the gap $g$.

Its four fields fix the following conditions.

1. $q$ is prime.
2. $q$ divides $GN5(g,y)$.
3. $q$ does not divide the gap $g$.
4. $q^2$ does not divide $GN5(g,y)$.

Thus, in prime-factor valuation language, the exponent of $q$ in the gap is $0$, while its exponent in `GN5` is exactly $1$.

$$
v_q(g)=0,\qquad v_q(GN5(g,y))=1
$$

The structure itself does not use valuation notation; the displayed formula is the mathematical interpretation of its four fields.

## Role in the complete proof

By the preceding factorization theorem, the fifth-power-difference body is

$$
(g+y)^5-y^5=g\,GN5(g,y).
$$

`CleanGN5Channel` designates a local certificate for a prime factor in this product that cannot lift to a fifth power.

Because $q$ divides `GN5`, it divides the body. Because it does not divide the gap and does not occur squared in `GN5`, its square cannot divide the body either. But if a prime divides a natural fifth power, its prime-factor exponent is at least $5$. This mismatch is the contradiction core later used by `not_fifth_power_GN5_of_clean` and `not_fifth_power_body_of_clean`.

The structure does not prove the general obstruction by itself. Instead, it explicitly packages the local conditions that each provider must supply. As the source comment states, the fields are intentionally exposed so that prime providers remain auditable.

## Direct dependencies

The direct dependencies are:

- `DkMath.FLT.Five.GN5`
- `Nat.Prime` and natural-number divisibility `Dvd.dvd`

The structure declaration itself contains no proof tactic. The preceding factorization theorems and concrete evaluation lemmas are not required merely to form the type.

## Proof flow

This is a `Prop`-valued structure rather than a theorem, so it has no proof script. A constructor must provide evidence in the following order.

1. Supply the primality of $q$ to `prime`.
2. Supply $q∣GN5(g,y)$ to `dvd_GN5`.
3. Supply $q∤g$ to `not_dvd_gap`.
4. Supply $q^2∤GN5(g,y)$ to `noLift`.

A consumer projects these fields as `h.prime`, `h.dvd_GN5`, `h.not_dvd_gap`, and `h.noLift`, using primality, divisibility, coprimality, and square non-divisibility separately.

## Lean-specific processing

Because the declaration is `structure ... : Prop`, a value of `CleanGN5Channel g y q` is proof data rather than computational data. Every field is itself a proposition and is subject to proof irrelevance.

`¬ q ∣ g` parses as `¬ (q ∣ g)`, while `¬ q ^ 2 ∣ GN5 g y` parses as `¬ (q^2 ∣ GN5 g y)`. Lean's operator precedence gives the intended types in the source notation.

The `noLift` field records “exponent less than two” through square non-divisibility, avoiding a valuation API. Together with `dvd_GN5`, it gives the exact local exponent one needed by later proofs.

## Redundancy and duplication

The fields `prime`, `dvd_GN5`, `not_dvd_gap`, and `noLift` are used independently by later theorems, so there is no obvious redundant field at this stage.

From `prime` and `not_dvd_gap`, one can repeatedly derive `Nat.Coprime q g`. Storing that as a fifth field would be possible, but it would duplicate derivable information and increase construction and consistency obligations. The present minimal package is therefore natural.

Another design could replace `noLift` with a valuation equation such as `padicValNat q (GN5 g y) = 1`, but that would introduce a heavier API and additional nonzero side conditions. The current structure is well suited to direct divisibility arguments.

## Optimization candidates

1. Add a derived lemma `CleanGN5Channel.coprime_gap : Nat.Coprime q g` if it is used frequently.
2. Audit whether `dvd_body` and `not_sq_dvd_body` should be exposed through `[simp]` or a narrower dedicated API.
3. Consider a helper constructor for concrete providers that combines value rewriting with `norm_num`.
4. Add conversion lemmas to the valuation layer so that the square-nondivisibility and `padicValNat = 1` formulations do not develop duplicated proofs.

These are unverified design proposals. No Lean build was run.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The structure declaration itself requires natural numbers, powers, divisibility, `Nat.Prime`, and the preceding local definition `GN5`.

A narrower import around `Mathlib.Data.Nat.Prime.Basic`, together with the local module providing `GN5`, may suffice. However, the actual `CleanChannel.lean` file immediately continues with coprimality and divisibility theorems, so the minimal file-level import may be broader than the structure alone requires. The exact minimum remains unverified because no build was performed.

## Comparator challenge suitability

The structure itself is not a tactic-comparison theorem, but both its construction and consumption make good Comparator challenges.

1. Construct the concrete case $(g,y,q)=(1,1,31)$ by reusing `GN5_one_one`.
2. Construct the same case by direct computation with `norm_num [GN5]` and compare dependencies and readability.
3. Compare short proofs deriving `Nat.Coprime q g` from `prime` and `not_dvd_gap`.
4. Compare deriving `noLift` from a valuation-one equation with proving it directly by factorization or numeric normalization.

Useful comparison axes are proof-term transparency, provider auditability, required imports, generalizability, and reuse of concrete evaluation lemmas.

## Next theorem to read

The next declaration is `DkMath.FLT.Five.CleanGN5Channel.dvd_body`.

It lifts `h.dvd_GN5` to the right factor of the product and obtains

$$
q∣g\,GN5(g,y).
$$

This is the first projection theorem that sends the local information packaged by the structure into the fifth-power body.

## Sources versus interpretation

The structure type, its four fields, declaration order, module comments, and immediately following consumer theorem were verified in `Flt5DkMath/FLT5StandAlone.lean`, which contains the generated source of `DkMath/FLT/Five/CleanChannel.lean`. The valuation interpretation, design assessment, import minimization, optimization candidates, and Comparator proposals include explanatory analysis or unverified suggestions. Existing PDFs are treated as supplementary narrative sources and do not override Lean declarations. No Lean build was run.
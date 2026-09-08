# 0346 — `GoldenZeroSectorFactorArithmeticExclusion`

## Declaration kind

This declaration is an **`abbrev`**.

```lean
/-- The raw arithmetic contract, repeated here to preserve the acyclic dependency
 direction from inversion to factorization. -/
abbrev GoldenZeroSectorFactorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

It is not a `theorem` or an ordinary `def`; it gives a short reducible name to the proposition saying that the raw zero-sector arithmetic data leads to contradiction.

## Lean type

The declaration itself has type

```lean
GoldenZeroSectorFactorArithmeticExclusion : Prop
```

After unfolding, it is a universally quantified implication chain. For arbitrary

```lean
r s : ℤ

a b : ℕ
```

it assumes positivity, coprimality, non-divisibility by five, the golden-norm condition, the signed product identity, coordinate coprimality, and the tenth-power splitting condition, and concludes `False`.

Thus

```lean
h : GoldenZeroSectorFactorArithmeticExclusion
```

can be used as a function that receives the complete raw arithmetic candidate data and its hypotheses and eventually returns a contradiction.

## Mathematical meaning

This contract states the zero-sector factorization obstruction without first packaging the data into a certified packet.

On the natural-number side it assumes

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1,\qquad 5\nmid b.
$$

It then requires the golden norm to agree with $b$ up to sign:

$$
\operatorname{goldenNorm}(r,s)=b
\quad\text{or}\quad
\operatorname{goldenNorm}(r,s)=-b.
$$

It also assumes the signed fifth-power factorization identity

$$
s\,\operatorname{goldenFifthSndFactor}(r,s)
=-5^6 a^{10},
$$

and the primitive-coordinate condition

$$
\gcd(|r|,|s|)=1.
$$

Finally, it assumes that there exist $c,d\in\mathbb N$ such that

$$
|s|=5^6c^{10},
\qquad
|\operatorname{goldenFifthSndFactor}(r,s)|=d^{10}.
$$

The proposition says that no raw arithmetic configuration satisfying all of these conditions can exist.

## Role in the full proof

0345 `GoldenZeroSectorFactorExclusion` introduced the compressed certified-level contract

```lean
GoldenZeroSectorFactorPacket → False
```

which excludes every completed exact factor packet.

0346 provides the receiving interface for expressing the same obstruction at the raw arithmetic level.

Conceptually the proof architecture is

$$
\text{raw arithmetic data}
\longrightarrow
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}
\longrightarrow
\bot.
$$

This `abbrev` does not yet perform those conversions. The next theorem, `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`, constructs the present raw arithmetic exclusion from the packet-level exclusion of 0345.

Accordingly, 0346 is the **arithmetic API boundary** through which the factorization layer exposes its contradiction to the higher zero-sector closure layer.

## Direct dependencies

The project definitions directly referenced by the right-hand side are mainly:

- `goldenNorm`
- `goldenFifthSndFactor`

On the Lean / Mathlib side it uses:

- `ℤ`, `ℕ`
- `Nat.Coprime`
- `Int.natAbs`
- divisibility `∣`
- existential quantification `∃`
- conjunction `∧`
- disjunction `∨`
- `False`

By contrast, 0345 `GoldenZeroSectorFactorExclusion`, `GoldenZeroSectorCandidate`, `GoldenZeroSectorInversionPacket`, and `GoldenZeroSectorFactorPacket` are not directly mentioned in this `abbrev`. They appear in the following bridge theorem that implements this raw contract.

## Construction flow

There is no tactic proof in this declaration; it directly defines a proposition.

Its logical structure is:

1. Choose arbitrary integer coordinates `r s` and natural parameters `a b`.
2. Assume positivity of `a` and `b`.
3. Assume `a` and `b` are coprime.
4. Assume `5 ∤ b`.
5. Assume the golden norm is `±b`.
6. Assume the signed product identity.
7. Assume `r.natAbs` and `s.natAbs` are coprime.
8. Assume the prescribed tenth-power decomposition of `s` and the second factor.
9. Require `False` as the conclusion.

The final existential hypothesis is deliberately packaged as

```lean
∃ c d : ℕ,
  s.natAbs = 5 ^ 6 * c ^ 10 ∧
  (goldenFifthSndFactor r s).natAbs = d ^ 10
```

The following theorem can therefore `rcases` this hypothesis into `c`, `d`, and the two equalities and feed them directly to `goldenZeroSectorCandidate_of_raw`.

## Lean-specific processing

### Transparent contract via `abbrev`

As in 0345, the declaration is an `abbrev`, so Lean can readily unfold the name to the long universal function type.

Consequently the next theorem can start directly with

```lean
intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
```

without an explicit

```lean
unfold GoldenZeroSectorFactorArithmeticExclusion
```

step.

### Mixing `ℤ` and `ℕ`

The coordinates `r,s` are integers, while `a,b,c,d` are naturals.

Therefore the norm condition explicitly casts

```lean
(b : ℤ)
```

to the integer side, whereas

```lean
r.natAbs
s.natAbs
```

moves integer coordinates back to naturals for `Nat.Coprime` and power decompositions.

This integer/natural boundary is an important part of the Lean bookkeeping in the zero-sector factorization pipeline.

### Sign and power syntax

The product hypothesis is written as

```lean
s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10
```

with explicit casts of both `5` and `a` to `ℤ`.

Lean parses `-(5 : ℤ) ^ 6` as `-((5 : ℤ) ^ 6)`. Since the exponent is even, its numerical value is `-15625`; the minus sign records the signed orientation of the product identity.

### `natAbs`

`Int.natAbs` returns the absolute value directly as a natural number. This lets the proof use the natural-number coprimality and perfect-power APIs without an additional cast layer from integer absolute values.

## Redundancy and duplication

This contract intentionally repeats a collection of raw arithmetic assumptions that substantially overlaps with the fields of `GoldenZeroSectorCandidate`.

In particular, the following data is repeated in raw form:

- positivity of `a` and `b`
- `Nat.Coprime a b`
- `¬ 5 ∣ b`
- the norm equality up to sign
- the signed product equality
- coordinate coprimality
- the power decompositions of `s` and the second factor

However, the source comment explicitly explains why the raw contract is repeated here: it preserves the acyclic dependency direction from inversion to factorization.

Thus replacing the raw argument list with `GoldenZeroSectorCandidate → False` may reintroduce an unwanted module dependency cycle. The apparent duplication cannot safely be removed merely on the basis of code length.

## Optimization candidates

The most obvious structural optimization would be to package the raw assumptions into a helper structure, for example

```lean
structure GoldenZeroSectorRawArithmeticData where
  r s : ℤ
  a b : ℕ
  ...
```

and then define an exclusion contract on that structure.

However, the placement of such a structure would have to respect the module dependency graph. Without checking that graph, this refactoring could defeat the exact acyclic design documented by the source comment.

Locally, the current argument order is already well chosen: it matches the `intro` order of the bridge theorem and the constructor order expected by `goldenZeroSectorCandidate_of_raw`.

One could also replace

```lean
(∃ c d : ℕ, P c ∧ Q d) → False
```

with a universally quantified continuation-style form, but if the upstream theorem naturally produces an existential package, the present formulation is cleaner.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the whole generated development.

The Mathlib functionality needed by this declaration itself is broadly limited to:

- integers and naturals
- `Nat.Coprime`
- `Int.natAbs`
- divisibility
- powers

The project modules defining `goldenNorm` and `goldenFifthSndFactor` may already import everything needed transitively.

Therefore a real module-level import minimization should begin from the modules providing those definitions rather than from `Mathlib` as a monolithic import.

No Lean build is performed in this task, so the exact minimal Mathlib import set has not been verified and is not asserted here.

## Comparator challenge suitability

**Yes; it can form a better intermediate challenge than 0345.**

A basic version could ask the learner to reconstruct the long proposition type:

```lean
abbrev Challenge : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    ... →
    False
```

A more meaningful Comparator challenge is the next bridge theorem:

```lean
variable
  (hFactor : GoldenZeroSectorFactorExclusion)

example : GoldenZeroSectorFactorArithmeticExclusion := by
  -- receive the raw assumptions, build the candidate,
  -- then connect inversion packet → factor packet → contradiction
```

This tests several Lean proof-engineering skills at once:

- `intro` over a long implication chain
- `rcases` of an existential package
- candidate construction with `let`
- composition of dependent packet APIs
- application of an exclusion contract

## Next declaration to read

The next declaration is

```lean
/-- Excluding the three exact factor packets excludes every original zero-sector
candidate.  `SignedGoldenClosure` identifies this contract definitionally with its
public zero-sector arithmetic exclusion. -/
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
  rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
  let source := goldenZeroSectorCandidate_of_raw r s a b
    ha hb hab h5b hNorm hProduct hrs c d hsAbs hHAbs
  exact hFactor (goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket source))
```

Its declaration kind is **`theorem`**.

Where 0346 only defines the *type* of the raw arithmetic exclusion, the next theorem actually inhabits that type from the packet-level exclusion of 0345.

This is the point where the complete pipeline

$$
\text{raw arithmetic assumptions}
\to
\text{candidate}
\to
\text{inversion packet}
\to
\text{factor packet}
\to
\bot
$$

is closed in a single proof.

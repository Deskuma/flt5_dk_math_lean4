# 0400 `GoldenZeroSectorArithmeticExclusion`

## Declaration kind

`abbrev`

This declaration exposes the zero-sector arithmetic exclusion condition as a single `Prop` that can be consumed by the later closure / receiver layer.

Up through 0399 `goldenZeroSectorCandidate_false`, the development has shown that once a concrete `GoldenZeroSectorCandidate` can be built, infinite descent yields a contradiction. Declaration 0400 rearranges the raw arithmetic assumptions needed to build such a candidate into a public contract that does not expose the internal structure type.

## Lean code

```lean
/--
The zero-sector Diophantine proposition exposed by the certified primitive and
tenth-power splits.
-/
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
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

## Lean type

The declaration itself has type

```lean
GoldenZeroSectorArithmeticExclusion : Prop
```

After unfolding the abbreviation, it is a higher-order proposition saying that for arbitrary integer coordinates `r s` and natural-number parameters `a b`, the listed arithmetic assumptions imply `False`.

In simplified logical notation,

$$
\forall r,s\in\mathbb Z,\;\forall a,b\in\mathbb N,
\quad
\mathcal H(r,s,a,b)\to\bot,
$$

where $\mathcal H$ packages positivity, coprimality, exclusion of the prime five, the golden norm condition, the signed zero-sector product equation, coordinate primitivity, and the tenth-power split.

Thus the mathematical content is that there is no tuple

$$
(r,s,a,b,c,d)
$$

satisfying all of these zero-sector arithmetic conditions simultaneously.

## Mathematical statement

Reading the hypotheses in order makes the zero-sector structure explicit.

First one requires

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1,\qquad 5\nmid b.
$$

Next the golden norm is required to equal $b$ up to sign:

$$
N(r,s)=b
\quad\text{or}\quad
N(r,s)=-b,
$$

with `goldenNorm ⟨r,s⟩` representing $N(r,s)$ in Lean.

The signed second-coordinate product relation is then assumed:

$$
s\,H(r,s)=-5^6a^{10},
$$

where

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s).
$$

The coordinates themselves must be primitive:

$$
\gcd(|r|,|s|)=1.
$$

Finally, the certified tenth-power split requires witnesses $c,d\in\mathbb N$ such that

$$
|s|=5^6c^{10},
$$

and

$$
|H(r,s)|=d^{10}.
$$

The proposition named by 0400 states that all of these conditions together are impossible.

A crucial point is that 0400 does not prove this impossibility by itself. As an `abbrev`, it merely names **the exact proposition that must be established to close the zero-sector arithmetic layer**.

## Role in the full proof

The descent layer through 0399 uses internal representations such as `GoldenZeroSectorCandidate` and `GoldenZeroSectorDescentPacket`.

By contrast, the upstream signed-golden sector naturally provides separate equations, divisibility facts, positivity facts, and coprimality statements.

0400 is the **public receiver contract** between those two layers.

Schematically,

$$
\text{raw zero-sector arithmetic}
\longrightarrow
\texttt{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\text{zero-sector exclusion}
\longrightarrow
\text{unit-sector closure}.
$$

This means later code does not need to know the internal details of the infinite-descent machinery. It only needs one hypothesis of type `GoldenZeroSectorArithmeticExclusion`.

Architecturally, this is an important abstraction boundary: the details of the descent remain internal, while the external interface exposes only the arithmetic assumptions and the final contradiction.

## Correspondence with 0399

The hypotheses of 0400 correspond almost field-by-field with `GoldenZeroSectorCandidate`.

The candidate contains, schematically,

```lean
r : ℤ
s : ℤ
a : ℕ
b : ℕ
c : ℕ
d : ℕ
a_pos : 0 < a
b_pos : 0 < b
coprime_a_b : Nat.Coprime a b
five_not_dvd_b : ¬ 5 ∣ b
norm_eq_or_eq_neg : ...
product_eq : ...
coprime_coords : ...
s_natAbs_eq : ...
H_natAbs_eq : ...
```

In 0400, only `c,d` are bundled existentially; the remaining data are taken directly as arguments and hypotheses.

Accordingly, 0400 can be viewed as the **logical, unstructured form** of the candidate structure.

Where 0399 has the shape

$$
\mathrm{GoldenZeroSectorCandidate}\to\bot,
$$

0400 defines the public proposition

$$
\text{raw hypotheses sufficient to build a candidate}\to\bot.
$$

## Direct dependencies

Because 0400 is an `abbrev`, it does not invoke proof lemmas. The formation of its type directly relies mainly on:

- the pair representation `⟨r, s⟩` of `GoldenInt`,
- `goldenNorm`,
- `goldenFifthSndFactor`,
- `Nat.Coprime`,
- `Int.natAbs`,
- powers, divisibility, order, and existential quantification over naturals and integers.

0399 `goldenZeroSectorCandidate_false` does not occur syntactically in the type of 0400. Semantically, however, it is the key contradiction theorem that will later discharge this raw contract.

Likewise, `GoldenZeroSectorCandidate` does not appear in the Lean type of 0400. That omission is intentional and forms the abstraction boundary.

## Construction and use flow

Since an `abbrev` has no proof body, the appropriate question is how the proposition is used rather than how it is proved locally.

1. Receive `r s : ℤ` and `a b : ℕ` from the upstream zero-sector arithmetic.
2. Supply positivity of $a$ and $b$.
3. Supply $\gcd(a,b)=1$.
4. Supply $5\nmid b$.
5. Supply `goldenNorm ⟨r,s⟩ = ±b`.
6. Supply the signed product

   $$
   sH(r,s)=-5^6a^{10}.
   $$

7. Supply coordinate primitivity $\gcd(|r|,|s|)=1$.
8. Supply witnesses `c d` for the tenth-power split of $|s|$ and $|H|$.
9. An implementation of `GoldenZeroSectorArithmeticExclusion` consumes all of these hypotheses and returns `False`.

The next declaration, 0401 `signedGoldenZeroSectorExclusion_of_arithmetic`, performs exactly the bridge from this contract to `SignedGoldenZeroSectorExclusion`.

## Lean-specific processing

### Why `abbrev` rather than `def`

The declaration uses `abbrev` instead of `def`.

An abbreviation is comparatively transparent to elaboration and reduction. That is appropriate here because the purpose is not to introduce an opaque new mathematical object, but simply to give a readable name to a long proposition of the form `∀ ... → False`.

### A receiver contract in `Prop`

0400 is not a data packet. It is a proposition designed to be passed as a single hypothesis:

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

This lets later theorems depend on the public contract without exposing the internal descent structures.

### Right associativity of `→`

Lean parses

```lean
A → B → C → False
```

as

```lean
A → (B → (C → False))
```

so clients can apply a value of this contract to the listed hypotheses one by one until the final `False` is obtained.

### Why only `c,d` are existentially bundled

The values `c,d` are witnesses produced by the certified tenth-power split. Keeping them under

```lean
∃ c d : ℕ, ...
```

matches upstream existential theorems such as the tenth-power splitting result directly and avoids forcing the receiver interface to choose them in advance.

## Redundancy and duplicated material

The hypothesis list in 0400 substantially duplicates the fields of `GoldenZeroSectorCandidate`.

That duplication is nevertheless architecturally meaningful: the public contract does not expose the internal structure type and instead states only the mathematical assumptions required by downstream users.

The clearest duplicated items are:

- `a_pos`,
- `b_pos`,
- `coprime_a_b`,
- `five_not_dvd_b`,
- `norm_eq_or_eq_neg`,
- `product_eq`,
- `coprime_coords`,
- `s_natAbs_eq`,
- `H_natAbs_eq`.

The last two are merely repackaged under the existential `∃ c d` in 0400.

The trade-off is maintenance: if the candidate structure changes, this external contract may also need to be kept in sync.

## Optimization candidates

### 1. Isolate the raw-contract-to-candidate bridge

A helper theorem or definition that receives the hypotheses of 0400 and constructs `GoldenZeroSectorCandidate` makes the later exclusion proof short and auditable.

The repository already contains `goldenZeroSectorCandidate_of_raw`, so the codebase already follows this direction. A clean public-contract → candidate → 0399 route is therefore natural.

### 2. Bundle the tenth-power split

One could introduce a dedicated structure such as

```lean
structure GoldenZeroSectorTenthSplit where
  c d : ℕ
  s_eq : s.natAbs = 5 ^ 6 * c ^ 10
  H_eq : ... = d ^ 10
```

if the witness package is reused extensively.

For the present single-purpose receiver interface, however, the existing `∃ c d, ... ∧ ...` form is lighter and connects directly to existential splitting theorems.

### 3. Abstract the signed norm condition

The pattern

```lean
goldenNorm gamma = b ∨ goldenNorm gamma = -b
```

occurs in several places. With enough reuse it could become a named predicate such as `SignedNormAbs gamma b`.

The drawback is that an additional name hides the exact arithmetic equation, so the current explicit form remains attractive for proof auditing.

### 4. Keep `abbrev`

There is no clear benefit to replacing the abbreviation with an opaque `def`. The purpose of this declaration is readability and interface naming, not computational hiding.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

0400 itself invokes no tactics. Its type requires only functionality around:

- `Nat.Coprime`,
- integers `ℤ`,
- `Int.natAbs`,
- divisibility `∣`,
- powers `^`,
- order `<`,
- and the local definitions providing `goldenNorm` and `goldenFifthSndFactor`.

Therefore the source module likely does not need all of `Mathlib` solely because of 0400.

The exact minimal Mathlib module set cannot be certified without actually reducing imports and running Lean. Since no Lean build is performed here, the precise minimized import list remains unverified.

## Suitability for a Comparator challenge

**Possible, but 0400 by itself is primarily a type-design challenge rather than a proof challenge.**

As a standalone task, a model could be asked to reconstruct the exact proposition interface from a skeleton such as

```lean
abbrev ZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    ... →
    False
```

and correctly fill in the casts, `natAbs`, coprimality conditions, signed norm alternative, and existential tenth-power split.

That would test precise Lean API design but little proof search.

A stronger Comparator task would combine 0400 with the following receiver theorem and the bridge to 0399, requiring the model to implement

$$
\text{raw hypotheses}
\to
\text{candidate construction}
\to
\text{descent contradiction}.
$$

Such a task would exercise structure construction, existential elimination, natural/integer casts, and composition of previously proved APIs.

## Next declaration to read

The next declaration is **0401 `signedGoldenZeroSectorExclusion_of_arithmetic`**, of kind `theorem`.

In the canonical source it immediately follows 0400 and has the schematic type

```lean
theorem signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion := by
  ...
```

Where 0400 exposes the raw arithmetic as a named proposition, 0401 invokes that proposition using an actual `SignedGoldenRamifierStrippedPacket` together with a zero-sector fifth-power equation.

Thus the dependency order continues as

$$
\text{0399 candidate contradiction}
\longrightarrow
\text{0400 public arithmetic contract}
\longrightarrow
\text{0401 zero-sector receiver bridge}.
$$

# 0334 — `GoldenZeroSectorFactorData`

## Declaration kind

This declaration is not a theorem but a **dependent `inductive`** type.

It is indexed by a `GoldenZeroSectorInversionPacket` and packages, for each of the three two-adic branches arising after zero-sector inversion, the certified fifth-power factorization data: coprimality, parity, ownership, and the branch-specific difference equation.

```lean
/-- Exact factor data in the three two-adic branches.  The enclosing packet
retains the complete inversion source and hence its norm and square reconstruction. -/
inductive GoldenZeroSectorFactorData
    (p : GoldenZeroSectorInversionPacket) : Type
  | odd
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 2 * e ^ 5)
      (B_eq : p.source.B0 = 2 * f ^ 5)
      (ownership : e * f = zeroSectorQ p.source.c)
      (difference : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5)
  | evenLeftLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_even : Even f)
      (A_eq : p.source.A0 = 8 * e ^ 5)
      (B_eq : p.source.B0 = 16 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5)
  | evenRightLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_even : Even e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 16 * e ^ 5)
      (B_eq : p.source.B0 = 8 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5)
```

## Lean type

Conceptually, the declaration has type

```lean
GoldenZeroSectorFactorData :
  GoldenZeroSectorInversionPacket → Type
```

Hence, for a fixed

```lean
p : GoldenZeroSectorInversionPacket
```

Lean obtains

```lean
GoldenZeroSectorFactorData p : Type
```

This is the essential difference from the preceding `GoldenZeroSectorFactorBranch`. The previous declaration was merely a three-constructor label type. The present one depends on `p`, and the equations in each constructor refer directly to

```lean
p.source.A0
p.source.B0
p.source.c
p.source.d
```

Thus a factor datum is not free-floating arithmetic information: it is a **certificate for one specific inversion packet**.

## Mathematical meaning

The declaration organizes the two-adic structure of the natural factors $A_0,B_0$ obtained from zero-sector inversion into three exact fifth-power normal forms.

### `odd` branch

Here

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5,
$$

with both $e$ and $f$ odd.

It also records

$$
\gcd(e,f)=1,
\qquad
\gcd(ef,d)=1,
$$

and the ownership identity

$$
ef = Q,
\qquad
Q := \operatorname{zeroSectorQ}(c).
$$

The branch-specific difference equation is

$$
e^5 + 4d^5 = f^5.
$$

This is exactly the shape accepted by the preceding theorem `eleven_dvd_d_of_fifth_add_four_fifth`, exposing the mod-$11$ channel of the odd branch.

### `evenLeftLow` branch

In this branch the left factor carries the lower two-adic exponent:

$$
A_0 = 8e^5,
\qquad
B_0 = 16f^5.
$$

The parity information is

$$
e\text{ odd},
\qquad
f\text{ even},
$$

while ownership becomes

$$
2ef = Q.
$$

The normalized difference equation is

$$
e^5 + d^5 = 2f^5.
$$

### `evenRightLow` branch

This is the left-right reversed branch:

$$
A_0 = 16e^5,
\qquad
B_0 = 8f^5,
$$

$$
e\text{ even},
\qquad
f\text{ odd},
$$

and again

$$
2ef = Q.
$$

The normalized difference equation is

$$
2e^5 + d^5 = f^5.
$$

Thus the three branches differ not merely by a label, but simultaneously by the placement of powers of $2$, the parity of $e,f$, the ownership relation with `zeroSectorQ`, and the final fifth-power equation exposed to downstream proofs.

## Role in the overall proof

This declaration is the central **proof-data type** of the zero-sector factorization phase.

The preceding `GoldenZeroSectorInversionPacket` retained information such as

- positivity of $A_0,B_0$,
- the factor product identity,
- the factor difference identity,
- coprimality of $c,d$,
- `zeroSectorQ`, and
- square reconstruction data.

Those facts are still too raw for branch-specific descent. The present type records the result of the two-adic analysis after $A_0,B_0$ have been normalized into explicit fifth-power forms.

Downstream theorems therefore do not need to reconstruct the factorization repeatedly. Pattern matching on

```lean
.odd ...
.evenLeftLow ...
.evenRightLow ...
```

immediately exposes the exact equations and proof witnesses for the selected branch.

In this sense `GoldenZeroSectorFactorData p` is a **certified normal form** sitting between the inversion phase and the descent phase.

## Direct dependencies

### `GoldenZeroSectorInversionPacket`

This is the index type of `p`. Every constructor refers to `p.source`.

In particular,

```lean
p.source.A0
p.source.B0
p.source.c
p.source.d
```

occur directly in the factorization and ownership equations.

### `zeroSectorQ`

This appears in every ownership field.

For the odd branch:

```lean
ownership : e * f = zeroSectorQ p.source.c
```

For both even branches:

```lean
ownership : 2 * (e * f) = zeroSectorQ p.source.c
```

### `Nat.Coprime`

Each constructor stores

```lean
coprime_e_f : Nat.Coprime e f
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

### `Odd` / `Even`

These propositions encode the branch-specific parity pattern.

The declaration itself does not invoke preceding theorems. Those theorem dependencies appear when an inhabitant of this inductive family is constructed. It is therefore important to distinguish direct declaration dependencies from proof dependencies of the constructor-producing theorem that comes later.

## Construction flow

There is no `by` proof script in the declaration. Its construction logic is embodied by the constructor arguments.

### 1. Fix the inversion packet as an index

```lean
(p : GoldenZeroSectorInversionPacket)
```

pins the factor data to its exact source packet at the type level.

### 2. Introduce the fifth-power bases

Every branch stores

```lean
(e f : ℕ)
```

### 3. Record nondegeneracy through positivity

All branches carry

```lean
e_pos : 0 < e
f_pos : 0 < f
```

### 4. Record prime ownership separation by coprimality

The common payload contains

```lean
coprime_e_f : Nat.Coprime e f
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

### 5. Record branch-specific parity

The odd branch stores `Odd e` and `Odd f`; `evenLeftLow` stores `Odd e` and `Even f`; `evenRightLow` stores `Even e` and `Odd f`.

### 6. Record the exact fifth-power forms of $A_0,B_0$

The coefficient pairs are

$$
(2,2),\ (8,16),\ (16,8)
$$

for the three branches respectively.

### 7. Record ownership of `zeroSectorQ`

The odd branch stores $ef=Q$, while the even branches store $2ef=Q$.

### 8. Record the branch-specific fifth-power equation

This gives downstream proofs a fully normalized equation without having to resubstitute the factorization identities.

## Lean-specific processing

### Source locking via a dependent inductive family

Because `p` is an index, factor data constructed from two different inversion packets cannot be mixed accidentally.

This is stronger than merely putting

```lean
source : GoldenZeroSectorInversionPacket
```

inside an ordinary structure: the source identity is visible in the type `GoldenZeroSectorFactorData p` itself.

### Constructors act as both branch tags and proof payloads

Each constructor identifies the branch and simultaneously carries all certificates needed for that branch.

Pattern matching therefore performs branch selection and proof-witness extraction at once.

### Constructor elimination rather than uniform field projection

Unlike a structure, this inductive does not automatically provide a uniform projection such as `data.e`, because `e,f` are constructor payloads.

The intended use is instead `cases` or pattern matching, which exposes the branch-specific equations together.

### Computational and propositional data are stored together

`e f : ℕ` are computational data, whereas `e_pos`, `coprime_e_f`, `A_eq`, and the other invariants are proof data. Lean's dependent type system allows both kinds to live in a single certified constructor.

## Redundancy and duplication

The three constructors share a substantial common prefix:

```lean
(e f : ℕ)
(e_pos : 0 < e) (f_pos : 0 < f)
(coprime_e_f : Nat.Coprime e f)
(coprime_ef_d : Nat.Coprime (e * f) p.source.d)
```

The roles of `A_eq`, `B_eq`, `ownership`, and `difference` are also common; only their formulas vary by branch.

So there is real syntactic duplication.

However, this duplication makes every branch invariant visible directly in the constructor signature. In particular, the two-adic coefficients and parity pattern are baked into the type, which makes the post-`cases` proof state explicit and auditable.

## Optimization candidates

### 1. Extract the common payload into an inner structure

The data $e,f$, positivity, and the coprimality fields could be grouped into a shared structure, leaving only branch-specific facts in the constructors.

This would reduce repetition but introduce an additional projection layer for every use. At the current scale, the explicitness of the existing design has significant value.

### 2. Index by `GoldenZeroSectorFactorBranch`

One could instead define something conceptually like

```lean
GoldenZeroSectorFactorData p b
```

with the branch label as a second index.

That would move branch equality into the type, but existential use of “some branch factor data” would then require a sigma type. The current code instead defines `GoldenZeroSectorFactorData.branch` immediately afterward, showing a deliberate separation between the lightweight branch label and the heavyweight certificate.

### 3. Abstract the parity/coefficient correspondence

The relation between coefficient pairs $(2,2)$, $(8,16)$, $(16,8)$ and the parity patterns could be factored into a separate definition.

That would reduce literal repetition, but at this stage auditability matters: exposing the coefficients in the constructor signatures makes the branch normal forms easy to inspect.

### 4. Retain `Type` rather than collapsing the result to `Prop`

The family stores existential witnesses $e,f$ as usable data. A disjunction of propositions would hide this constructive payload and make downstream extraction more cumbersome. The present `Type`-valued certificate is therefore appropriate.

## Required Mathlib imports and import optimization

The standalone source imports

```lean
import Mathlib
```

The present declaration directly relies mainly on

- `Nat.Coprime`,
- `Odd`,
- `Even`,
- natural-number exponentiation, multiplication, and order,
- the preceding `GoldenZeroSectorInversionPacket`, and
- `zeroSectorQ`.

Therefore a standalone extraction of this declaration could probably use a significantly smaller import set than all of `Mathlib`.

However, the import closure of `GoldenZeroSectorInversionPacket` and `zeroSectorQ` must also be included. Since no Lean build is performed here, the exact minimal Mathlib import set is not verified.

The containing standalone file also uses `omega`, `norm_num`, divisibility APIs, and many other facilities in later proofs, so this declaration alone does not imply that the whole file's `import Mathlib` can safely be reduced.

## Comparator challenge suitability

**High.**

This declaration is a strong dependent-API-design comparison problem rather than a tactic-level theorem proving problem.

Useful competing designs include:

1. the current three-constructor dependent `inductive`,
2. a common `structure` plus a branch-specific proposition,
3. an indexed family `GoldenZeroSectorFactorData p b`,
4. three separate branch structures combined by a sum type,
5. a purely existential/disjunctive proposition describing the factorization result.

Relevant evaluation criteria are:

- how much branch-specific invariant information appears in the type,
- simplicity of the proof state after pattern matching,
- accessibility of common fields,
- `simp` ergonomics,
- prevention of source-packet mixups,
- readability of downstream descent theorem types, and
- maintainability if new branches are introduced.

The current design deliberately accepts some field duplication in exchange for exposing each complete mathematical normal form directly in the constructor signature. That tradeoff makes it particularly suitable for a Comparator challenge.

## Next declaration to read

The next declaration in the canonical source is

```lean
/-- Branch label of an exact factor datum. -/
def GoldenZeroSectorFactorData.branch
    {p : GoldenZeroSectorInversionPacket} :
    GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
  | .odd .. => .odd
  | .evenLeftLow .. => .evenLeftLow
  | .evenRightLow .. => .evenRightLow
```

Therefore the next sequence number is **0335 `GoldenZeroSectorFactorData.branch`**.

It is not a theorem but a **`def`**. It projects the heavy certified factor datum introduced here onto the lightweight `GoldenZeroSectorFactorBranch` label defined in 0333.

Thus 0334 is the branch-specific proof payload, while 0335 is the observation function that reads only its branch label.
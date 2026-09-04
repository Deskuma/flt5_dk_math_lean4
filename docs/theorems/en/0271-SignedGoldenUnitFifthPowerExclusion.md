# 0271 — `SignedGoldenUnitFifthPowerExclusion`

## Declaration kind

This declaration is not a `theorem`; it is an **`abbrev`**.

In the canonical Lean source, it fixes as a `Prop` abbreviation the reusable exclusion proposition that the unit-sector arithmetic is ultimately expected to provide.

## Lean type

```lean
/--
The reusable packet exclusion produced by the sector arithmetic: no packet's
`beta` can be a unit times a fifth power.
-/
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

Read as a logical formula, the type says that for arbitrary natural parameters `u v w`, any ramifier-stripped packet `p`, and arbitrary golden integers `epsilon` and `gamma`, a contradiction `False` follows whenever

1. `epsilon` is a `GoldenUnit`, and
2. `p.beta` is represented as `epsilon * gamma^5`.

Mathematically this is the exclusion contract

$$
\epsilon\in\mathcal O^\times,
\qquad
\beta=\epsilon\gamma^5
\quad\Longrightarrow\quad
\bot,
$$

stating that a packet's $\beta$ cannot be a unit times a fifth power.

## Mathematical meaning of the declaration

Viewing `GoldenInt` as the coordinate model of the golden integer ring, `GoldenUnit epsilon` states that `epsilon` has a two-sided inverse.

Thus `SignedGoldenUnitFifthPowerExclusion` excludes, **simultaneously for every unit $\epsilon$ and every $\gamma$**, the possibility that the distinguished packet element `beta` has the form

$$
\beta=\epsilon\gamma^5.
$$

The important point is that this declaration does not itself prove the exclusion. An `abbrev` only says, “from now on, call this proposition by this name.” A later theorem supplies an actual proof term inhabiting the proposition.

This lets downstream code depend only on a single value such as

```lean
hExclude : SignedGoldenUnitFifthPowerExclusion
```

without knowing the internal sector-by-sector arithmetic used to construct it.

## Role in the overall proof

Declarations 0264–0268 computed the second coordinate of the five representative unit sectors

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

when `gamma^5 = A + Bφ`, obtaining

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B.
$$

0269 `golden_neg_unit_mul_fifth_snd` reduced negative unit representatives to sign reversal, while 0270 `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` transported the packet's stored exact five-adic coordinate

$$
\operatorname{snd}(\beta)=-5^7a^{10}
$$

into a finite-sector representation.

0271 sits at the point where these calculations are packaged into the **type of the public interface** handed to later stages.

Conceptually, the proof layer is compressed as

$$
\text{sector coordinate arithmetic}
\longrightarrow
\text{all unit sectors are impossible}
\longrightarrow
\texttt{SignedGoldenUnitFifthPowerExclusion}.
$$

The following theorem `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector` combines the classification of units modulo fifth powers with the zero-sector exclusion and constructs an actual inhabitant, i.e. a proof, of this `Prop`.

So 0271 adds no new number-theoretic computation. Its role is to provide an **abstraction boundary that folds a long sector-elimination argument into one reusable theorem contract**.

## Direct dependencies: definitions and lemmas

The objects that occur directly on the right-hand side of the `abbrev` are the following.

### `SignedGoldenRamifierStrippedPacket`

```lean
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  ...
  beta : GoldenInt
  ...
```

This is the packet obtained after removing the visible ramifier from the exceptional branch. The present declaration concerns its field `p.beta`.

### `GoldenInt`

This is the project-side coordinate type representing golden integers $a+b\varphi$. Both `epsilon` and `gamma` have this type.

### `GoldenUnit`

In the canonical source it is defined as the following two-sided inverse predicate.

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

Thus this declaration takes the project-side concrete unit predicate as its interface rather than placing Mathlib's abstract `IsUnit` directly in the type.

### `goldenMul`

This is the project-side multiplication API on `GoldenInt`; it forms the product in

```lean
p.beta = goldenMul epsilon (goldenPow gamma 5)
```

### `goldenPow`

This is the natural-power API on `GoldenInt`. Here the exponent is fixed at `5`, representing `gamma^5`.

### `False`

The conclusion is a contradiction rather than data. An inhabitant of this `Prop` can therefore be used as an eliminator showing that no such representation can occur.

The individual declarations 0264–0270 do not appear by name in the type of this `abbrev`. They belong to the internal implementation used later to **prove** the contract.

## Proof or construction flow

There is no `:= by ...` proof script in this declaration.

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ...
```

merely gives a name to the proposition on its right-hand side.

Its construction flow is therefore best read as follows.

1. Universally quantify implicit parameters `u v w : ℕ`.
2. Take the corresponding packet `p`.
3. Take arbitrary `epsilon gamma : GoldenInt`.
4. Receive the assumption that `epsilon` is a unit.
5. Receive the representation hypothesis `p.beta = epsilon * gamma^5`.
6. Require a function that returns `False` from those two assumptions.

Under the Curry–Howard correspondence, a proof of the `Prop` has the schematic form

```lean
fun p epsilon gamma hepsilon hbeta =>
  -- derive False
```

The following theorem does exactly this with `intro`, classifies the unit into a finite sector, and constructs the contradiction.

## Lean-specific processing

### `abbrev` and definitional transparency

An `abbrev` is a lightweight abbreviation for the right-hand side rather than an opaque theorem body. Lean can therefore unfold

```lean
SignedGoldenUnitFifthPowerExclusion
```

into the full universally quantified implication chain when needed.

Consequently a following theorem whose conclusion is this name can begin immediately with

```lean
intro u v w p epsilon gamma hepsilon hbeta
```

without an explicit user-written unfolding step.

### Implicit and explicit quantification

In

```lean
∀ {u v w : ℕ} (p : ...) (epsilon gamma : GoldenInt), ...
```

only `u v w` are implicit because they are enclosed in `{...}`. The packet `p` and the two golden integers are explicit arguments.

This makes the API infer `u v w` from the packet's type while leaving the packet, unit, and fifth-power base as explicit elimination inputs.

### Curried implication chain

```lean
GoldenUnit epsilon →
p.beta = ... →
False
```

is a proposition-level curried two-argument function. It would also be mathematically possible to define the exclusion via

```lean
¬ ∃ epsilon gamma, ...
```

but the present curried form is convenient when downstream code already has concrete `epsilon`, `gamma`, `hepsilon`, and `hbeta` available for direct application.

## Redundancy and duplication

The declaration body is short and has almost no internal redundancy.

Mathematically,

```lean
∀ ...,
  GoldenUnit epsilon →
  p.beta = ... →
  False
```

is close in content to

```lean
¬ ∃ epsilon gamma,
  GoldenUnit epsilon ∧
  p.beta = ...
```

but the current form has practical advantages:

- witnesses do not need to be repackaged into an existential;
- downstream code can apply the exclusion directly to concrete `epsilon` and `gamma`;
- proof construction by `intro` is natural.

A nearby pure-fifth-power exclusion, if used through an interface such as `SignedGoldenPureFifthPowerExclusion`, may in principle be derivable from the unit exclusion by specializing to `epsilon = 1`. However, changing that dependency direction would alter the proof architecture, so this is only an **API-design candidate** here; this document does not claim that the nearby declaration is redundant or equivalent without a full use-site audit.

## Optimization candidates

### 1. Keep the `abbrev`

Its main value is that the result of a large sector proof can be handled under a short contract name. Removing it and expanding the proposition throughout downstream code would reduce abstraction rather than improve it.

### 2. A `¬`-existential form is not automatically better

For example, one could write

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w} (p : SignedGoldenRamifierStrippedPacket u v w),
    ¬ ∃ epsilon gamma,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

But if downstream unit classification already produces concrete witnesses, the present curried interface requires fewer conversions. Whether such a change is beneficial should be decided only after auditing all call sites.

### 3. Generalizing the exponent is unnecessary here

It is formally possible to introduce a generic `UnitPowerExclusion n`, but this development is specifically driven by five-adic valuation and `Fin 5` unit classes. Keeping the exponent `5` visible in the type preserves the mathematical meaning of the FLT5 proof.

## Required Mathlib imports and import-optimization candidates

The verified standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its generated manifest identifies the source section containing this declaration as `DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean`.

The `abbrev` itself directly needs only lightweight infrastructure, principally

- `Nat`;
- propositions, universal quantification, and implication;
- project-side `GoldenInt`;
- `SignedGoldenRamifierStrippedPacket`;
- `GoldenUnit`;
- `goldenMul` and `goldenPow`.

The declaration itself uses no tactics such as `ring`, `omega`, or `norm_num`.

However, the repository's `FLT5StandAlone.lean` is a generated artifact concatenating many original modules, and the original standalone `import` lines of `SignedGoldenSectorArithmetic.lean` are not available here. Therefore the minimal Mathlib import set cannot be stated with certainty from this repository snapshot alone.

An import optimization would first narrow project dependencies to the ramifier-stripped packet, unit-class, and golden fifth-power coordinate APIs, and then remove Mathlib imports under an actual module build. This task explicitly performs no Lean build, so that minimal set has not been verified.

## Comparator challenge suitability

**Yes, although this declaration alone is low in implementation difficulty.**

As a hole-filling task it mostly tests proposition/API design rather than theorem-proving search. It is more useful for comparing whether a system can explain:

1. the distinct roles of `abbrev`, `def`, and `theorem`;
2. the difference between an existential negation and a curried contradiction form;
3. the purpose of implicit parameters `{u v w}`;
4. why a downstream theorem can begin with `intro` against this contract without an explicit unfolding step.

A stronger Comparator challenge is to provide this declaration as the specification and ask for the following theorem

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

because that proof requires unit classification, sector normalization, and a zero/nonzero sector split, making differences in proof planning much more visible.

## Correspondence with the PDFs

The target branch contains the following PDFs:

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

Direct retrieval of the PDF body did not succeed in this run. Therefore the precise page/section corresponding to 0271, or a one-to-one match with wording about “unit times fifth power exclusion” in the PDFs, has not been verified.

No PDF content is guessed here. The Lean type, dependencies, and architectural role described in this document are grounded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is the theorem

```lean
theorem signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
    (hClasses : GoldenUnitClassesModFifth)
    (hZero : SignedGoldenZeroSectorExclusion) :
    SignedGoldenUnitFifthPowerExclusion := by
  ...
```

Where 0271 defines the **type** of the contract saying what must ultimately be excluded, the next theorem constructs an actual proof of that contract by

- classifying an arbitrary unit using `GoldenUnitClassesModFifth`,
- sending the zero sector to `SignedGoldenZeroSectorExclusion`, and
- excluding nonzero sectors with the sector arithmetic developed immediately before this point.

It is therefore the natural next declaration in dependency order.

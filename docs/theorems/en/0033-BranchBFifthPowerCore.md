# 0033 — `BranchBFifthPowerCore`

## Declaration

```lean
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {a b y : ℕ},
    0 < a →
    0 < y →
    Nat.Coprime a y →
    ¬ 5 ∣ a →
    GN5 (a ^ 5) y = b ^ 5 →
    False
```

## Mathematical statement

For arbitrary natural numbers $a,b,y$, the following conditions cannot all hold:

$$
a>0,\qquad y>0,
$$

$$
\gcd(a,y)=1,\qquad 5\nmid a,
$$

$$
GN5(a^5,y)=b^5.
$$

Equivalently, excluding every perfect-fifth-power representation of `GN5` under these hypotheses closes the arithmetic kernel that remains after the elementary Branch-B reduction.

## Role in the complete proof

`BranchBFifthPowerCore` is not itself a proved theorem. It is the **consumer interface** that later arithmetic must provide. The preceding theorem `exists_branchB_fifthPowerNormalForm` constructs $a,b$ and a complete normal-form packet from a Branch-B counterexample candidate. This declaration extracts only the inputs genuinely needed to derive the final contradiction from that packet.

A notable design feature is that it does not require all twelve fields of `BranchBFifthPowerNormalForm`. It keeps only `a_pos`, `pack.hy`, `coprime_a_y`, `five_not_dvd_a`, and `GN_eq`. The coordinates $x,z$, the Branch-B assumption itself, the equations $x=ab$ and $z=y+a^5$, positivity of $b$, and the other coprimality facts are omitted from the interface.

Thus this abbreviation forms a minimal boundary between the Reduction/NormalForm layer and the later square/golden, golden-integer, and descent arguments.

## Direct dependencies

The direct repository-level dependencies are:

- `GN5`
- propositions, divisibility, powers, and coprimality over natural numbers

No previously proved theorem is invoked syntactically. The main types and notation in the right-hand side of the abbreviation are:

- `ℕ`
- `Nat.Coprime`
- divisibility notation `∣`
- function arrows `→`
- universal quantification `∀`
- `False`

## Logical flow

The declaration itself contains no proof term. Its logical shape is a sequence of five inputs:

1. $a$ is positive.
2. $y$ is positive.
3. $a$ and $y$ are coprime.
4. The exceptional prime $5$ does not divide $a$.
5. `GN5 (a^5) y` equals $b^5$.

A consumer of this interface must return `False` after receiving these hypotheses.

Viewed as a Lean function type, it is a curried interface: the contradiction becomes available only after all hypotheses, including the final equation, have been supplied in order.

## Lean-specific processing

### `abbrev` and transparency

`abbrev` introduces a transparent abbreviation. During elaboration and reduction, Lean can readily unfold it to the proposition on the right-hand side. It does not create a new data structure; it gives a short name to a long higher-order proposition.

### Implicitly quantified variables

```lean
∀ {a b y : ℕ}, ...
```

uses braces, so `a`, `b`, and `y` are implicit arguments. At application sites Lean can infer them from the subsequent hypotheses, especially from the type of `GN5 (a ^ 5) y = b ^ 5`.

### Parsing `¬ 5 ∣ a`

Lean reads `¬ 5 ∣ a` as `¬ (5 ∣ a)`, namely `(5 ∣ a) → False`. It is one hypothesis in the chain of function arrows.

### An API returning `False`

The conclusion is `False`, rather than a negated existential statement. This allows a caller that has already constructed a normal-form packet to pass the required fields directly and in sequence. The next theorem, `branchB_false_of_fifthPowerCore`, uses exactly this shape.

## Redundancy and duplication

The declaration contains no duplicated proof work. Its interface is deliberately much narrower than the information stored by `BranchBFifthPowerNormalForm`; this is dependency reduction rather than an omission.

It is nevertheless worth noting that positivity of $b$ is not required. It may be derivable from `GN5(a^5,y)=b^5` together with $a,y>0$ whenever needed, and the current downstream proof evidently does not require it as an explicit input. Whether this omission was an explicitly documented design decision is not established beyond the source comment, so this is partly interpretive.

## Optimization candidates

The following are unverified design alternatives.

1. A consumer could receive the entire normal-form structure directly:

```lean
∀ {x y z a b}, BranchBFifthPowerNormalForm x y z a b → False
```

This would introduce unnecessary dependencies. The current core is more reusable for later arithmetic.

2. The proposition could be expressed as a negated existential:

```lean
¬ ∃ a b y : ℕ,
  0 < a ∧ 0 < y ∧ Nat.Coprime a y ∧
  ¬ 5 ∣ a ∧ GN5 (a ^ 5) y = b ^ 5
```

The current curried form is convenient for applying fields from a provider packet; the negated-existential form is often easier to read mathematically. Their adapters are suitable for comparison.

3. One could abstract $a^5$ as a new variable $A$, but this would discard the fifth root $a$ and the hypothesis $5\nmid a$. If those data are essential to the later golden-integer analysis, the current form should be retained.

## Required Mathlib imports and import optimization

The verified standalone artifact uses `import Mathlib`. This declaration alone needs only natural numbers, powers, divisibility, `Nat.Coprime`, and basic logic.

The individual import line of the original split source `NormalForm.lean` was not available in the branch material retrieved for this article. Possible finer-grained imports are therefore unverified suggestions:

- `Mathlib.Data.Nat.GCD.Basic`
- a basic module providing natural-number powers and divisibility
- the preceding DkMath `GN5` module

This declaration itself does not require `omega` or `ring`. Neighboring theorems in the same file may still require them, so file-level import minimization must be checked by a Lean build. No Lean build was run for this museum update.

## Comparator challenge suitability

This declaration is well suited to Comparator challenges because it is short and exposes an interface-design choice clearly.

1. **Beginner** — prove equivalence between the curried form and the negated-existential form.
2. **Intermediate** — write an adapter that projects the five required facts from `BranchBFifthPowerNormalForm` and obtains `False` from a core hypothesis.
3. **Design comparison** — compare the current minimal interface with variants that additionally require `0<b` or `Nat.Coprime b y`, and determine which assumptions later proofs actually use.

## Verified facts versus interpretation

The declaration type, its use of `abbrev`, and the fact that `branchB_false_of_fifthPowerCore` follows immediately afterward were verified in the generated repository source `Flt5DkMath/FLT5StandAlone.lean`.

The design interpretation concerning omission of `b_pos`, the proposed import split, and the alternative negated-existential interface are unverified interpretations or suggestions.

## Next declaration

```text
DkMath.FLT.Five.branchB_false_of_fifthPowerCore
```

This theorem projects exactly the five facts required by the core from the complete normal form produced by `exists_branchB_fifthPowerNormalForm`, applies the core, and thereby refutes any Branch-B `CounterexamplePack`.

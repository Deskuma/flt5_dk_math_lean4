# 0325 — `goldenZeroSectorInversionPacket`

## Declaration kind

This is not a theorem but a **`def`**.

It constructs the `GoldenZeroSectorInversionPacket` structure defined immediately before it. For every `GoldenZeroSectorCandidate`, it fills each packet field with facts already proved about that candidate, thereby producing a certified inversion packet.

## Lean type

```lean
/-- Every raw zero-sector candidate deterministically yields its inversion packet. -/
def goldenZeroSectorInversionPacket (p : GoldenZeroSectorCandidate) :
    GoldenZeroSectorInversionPacket where
  source := p
  H_pos := p.H_pos
  s_neg := p.s_neg
  c_pos := p.c_pos
  d_pos := p.d_pos
  s_eq := p.s_eq_neg_five_pow_mul_tenth
  H_eq := p.H_eq_tenth
  a_eq := p.a_eq_c_mul_d
  coprime_c_d := p.coprime_c_d
  five_not_dvd_d := p.five_not_dvd_d
  d_odd := p.d_odd
  discriminant_eq := p.discriminant_eq
  factor_product := p.A0_mul_B0
  factor_difference := p.B0_eq_A0_add
  factor_sum := p.factor_sum
  square_reconstruction := p.square_reconstruction
  W_pos := p.W_pos
  A_pos := p.A_pos
  A_lt_B := p.A_lt_B
  B_pos := p.B_pos
  A0_cast := p.A0_cast
  B0_cast := p.B0_cast
  A0_pos := p.A0_pos
  B0_pos := p.B0_pos
```

Its type is equivalently

```lean
goldenZeroSectorInversionPacket :
  GoldenZeroSectorCandidate → GoldenZeroSectorInversionPacket
```

## Mathematical meaning

This definition proves no new number-theoretic proposition by itself. Its purpose is to repackage the invariants already established for a zero-sector candidate `p` as one certified object.

In particular, the packet retains data such as

$$
s=-5^6c^{10},
$$

$$
H=d^{10},
$$

$$
a=cd,
$$

$$
\gcd(c,d)=1,
$$

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5,
$$

as well as positivity, ordering, and cast equations for the signed and natural factors.

Thus this `def` is the deterministic map that converts the output of the zero-sector inversion phase into a form directly consumable by the downstream factorization phase.

## Role in the full proof

0324 defined only the schema of the packet. This 0325 declaration shows that the schema is not merely an ideal interface: every `GoldenZeroSectorCandidate` can actually be turned into such a packet.

The proof architecture therefore becomes

```text
GoldenZeroSectorCandidate
        ↓
goldenZeroSectorInversionPacket
        ↓
GoldenZeroSectorInversionPacket
        ↓
SignedGoldenZeroSectorFactorization
```

The downstream factorization development no longer needs to replay the long chain of candidate-level proofs. It can consume packet projections directly.

## Direct dependencies

### `GoldenZeroSectorCandidate`

This is the input type.

### `GoldenZeroSectorInversionPacket`

This is the output type. The definition fills every field of the structure introduced in 0324.

### Upstream theorems and definitions used

The fields correspond one-to-one to the following established API:

- `p.H_pos`
- `p.s_neg`
- `p.c_pos`
- `p.d_pos`
- `p.s_eq_neg_five_pow_mul_tenth`
- `p.H_eq_tenth`
- `p.a_eq_c_mul_d`
- `p.coprime_c_d`
- `p.five_not_dvd_d`
- `p.d_odd`
- `p.discriminant_eq`
- `p.A0_mul_B0`
- `p.B0_eq_A0_add`
- `p.factor_sum`
- `p.square_reconstruction`
- `p.W_pos`
- `p.A_pos`
- `p.A_lt_B`
- `p.B_pos`
- `p.A0_cast`
- `p.B0_cast`
- `p.A0_pos`
- `p.B0_pos`

The definition introduces no separate auxiliary lemma of its own.

## Construction flow

1. Store the original candidate with `source := p`.
2. Copy the sign data `H_pos`, `s_neg`, `c_pos`, and `d_pos`.
3. Store the reparameterizations `s_eq`, `H_eq`, and `a_eq`.
4. Store the arithmetic constraints `coprime_c_d`, `five_not_dvd_d`, and `d_odd`.
5. Store the discriminant, product, difference, sum, and square-reconstruction identities.
6. Store positivity and ordering of the signed factors.
7. Store the cast equations and positivity of `A0` and `B0`.

Every field is supplied by an already existing proof term, so no new tactic proof is performed here.

## Lean-specific processing

### Structure literal

The syntax

```lean
GoldenZeroSectorInversionPacket where
  ...
```

constructs the dependent record directly.

### Reuse of proof terms

For example,

```lean
factor_product := p.A0_mul_B0
```

does not re-prove the factor-product theorem. It places the already existing proof term into the corresponding structure field.

### Dependent typing

Once `source := p` is fixed, every subsequent field is required to refer to that same `p`. Lean's type checker therefore prevents facts proved for a different candidate from being mixed into the packet.

### Namespace and generated-source boundary

Immediately after this `def`, the `DkMath.FLT.Five` namespace is closed and the generated source `SignedGoldenZeroSectorInversion.lean` ends. The next generated source, `SignedGoldenZeroSectorFactorization.lean`, begins by consuming the packet. This makes the declaration the practical exit point of the inversion module.

## Redundancy and duplication

Most assignments have the simple form

```lean
field := p.corresponding_theorem
```

so the constructor is mechanically repetitive.

That repetition is intentional. It mirrors the explicit API schema from 0324, making both the meaning and provenance of every packet field visible.

The maintenance cost is that adding or removing a structure field requires the constructor to be updated in sync.

## Optimization candidates

Possible alternatives include:

1. storing only `source` and deriving the remaining facts through namespace theorems when needed;
2. splitting the packet into smaller nested packets and composing them;
3. retaining the current explicit field-by-field constructor to optimize downstream proof simplicity.

The current design follows option 3 and gives excellent provenance and module-boundary clarity. Determining which fields could safely be removed would require checking all downstream uses and rebuilding Lean; therefore any shrinking proposal remains **unverified** in this run.

## Required Mathlib imports and possible import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

This `def` itself introduces no sophisticated tactic or new Mathlib machinery. It primarily relies on

- structure construction,
- projections of already established project theorems,
- and types involving `Nat`, `Int`, `Odd`, `Nat.Coprime`, divisibility, order, and powers.

However, the output structure has a broad dependency closure. The exact minimal Mathlib import set is **not confirmed**, because no Lean build or import minimization experiment was performed in this run.

## Suitability for a Comparator challenge

It is **not especially suitable as a tactic-proof Comparator challenge, but it is well suited as an API-construction design Comparator**.

Useful variants to compare would be:

- the current explicit structure literal,
- a nested-packet constructor,
- a source-only wrapper with derived theorem API,
- or helper constructors for groups of fields.

Relevant evaluation criteria are readability, dependency transparency, maintenance cost, downstream proof length, and ease of tracking field provenance.

## Cross-check against the PDFs

The repository tree of the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub connector does not return binary PDF bodies as text, so direct verification of specific pages, sections, or equation numbers is **not confirmed** in this run. No unsupported page or section references have been inferred.

## Next declaration to read

The next generated source is `SignedGoldenZeroSectorFactorization.lean`, whose first declaration is the private theorem

```lean
private theorem coprime_of_odd_of_no_common_odd_prime
    {m n : ℕ} (hm : Odd m)
    (hodd : ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) :
    Nat.Coprime m n := by
  ...
```

It states that if `m` is odd and there is no common prime divisor other than possibly `2`, then `m` and `n` are coprime. In museum dependency order, the natural next entry is **0326 `coprime_of_odd_of_no_common_odd_prime`**.

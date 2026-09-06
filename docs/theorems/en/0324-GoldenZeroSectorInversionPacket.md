# 0324 — `GoldenZeroSectorInversionPacket`

## Declaration kind

This declaration is not a theorem but a **`structure`**.

It packages, as one certified record, the sign conditions, ownership relations, product/difference identities, square reconstruction, and positivity facts that were established individually on `GoldenZeroSectorCandidate` through declarations 0314–0323.

## Lean type

```lean
/--
Certified output of zero-sector inversion.  It keeps the complete source candidate
and all signs, ownership, factor identities, and positivity facts needed downstream.
-/
structure GoldenZeroSectorInversionPacket where
  source : GoldenZeroSectorCandidate
  H_pos : 0 < goldenFifthSndFactor source.r source.s
  s_neg : source.s < 0
  c_pos : 0 < source.c
  d_pos : 0 < source.d
  s_eq : source.s = -((5 : ℤ) ^ 6 * (source.c : ℤ) ^ 10)
  H_eq : goldenFifthSndFactor source.r source.s = (source.d : ℤ) ^ 10
  a_eq : source.a = source.c * source.d
  coprime_c_d : Nat.Coprime source.c source.d
  five_not_dvd_d : ¬ 5 ∣ source.d
  d_odd : Odd source.d
  discriminant_eq :
    zeroSectorU source.r source.s ^ 2 - zeroSectorW source.d ^ 2 =
      20 * source.s ^ 4
  factor_product :
    source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
  factor_difference :
    source.B0 = source.A0 + 8 * source.d ^ 5
  factor_sum :
    zeroSectorA source.r source.s source.d +
        zeroSectorB source.r source.s source.d =
      2 * zeroSectorU source.r source.s
  square_reconstruction :
    zeroSectorU source.r source.s - 5 * source.s ^ 2 =
      zeroSectorX source.r source.s ^ 2
  W_pos : 0 < zeroSectorW source.d
  A_pos : 0 < zeroSectorA source.r source.s source.d
  A_lt_B :
    zeroSectorA source.r source.s source.d <
      zeroSectorB source.r source.s source.d
  B_pos : 0 < zeroSectorB source.r source.s source.d
  A0_cast : (source.A0 : ℤ) = zeroSectorA source.r source.s source.d
  B0_cast : (source.B0 : ℤ) = zeroSectorB source.r source.s source.d
  A0_pos : 0 < source.A0
  B0_pos : 0 < source.B0
```

Its type is `GoldenZeroSectorInversionPacket : Type`. It is a dependent record containing one `GoldenZeroSectorCandidate` together with proof terms already established for that same candidate.

## Mathematical meaning

Let `source` be the candidate produced by zero-sector inversion. The structure stores all information needed downstream for that candidate.

Its principal mathematical contents are:

- the sign conditions $H>0$, $s<0$, $c>0$, $d>0$;
- the ownership/reparameterization identities $s=-5^6c^{10}$, $H=d^{10}$, and $a=cd$;
- the arithmetic conditions $\gcd(c,d)=1$, $5\nmid d$, and oddness of $d$;
- the discriminant identity

$$
U^2-W^2=20s^4;
$$

- for the positive natural factors $A_0,B_0$,

$$
A_0B_0=4Q^5
$$

and

$$
B_0=A_0+8d^5;
$$

- the signed-factor sum, square reconstruction, positivity, and ordering;
- the cast identifications between `A0`,`B0` and their signed factors.

Thus the structure does not express inversion success as one proposition. Instead, it materializes the successful inversion result as an API that downstream factorization can consume directly.

## Role in the whole proof

This declaration is the boundary between the `GoldenZeroSectorCandidate` phase and the factorization phase.

Declarations 0314–0323 established candidate-level facts such as

$$
0<A<B,
$$

$$
A_0B_0=4Q^5,
$$

and

$$
B_0=A_0+8d^5.
$$

The present structure freezes those facts as fields so that later proofs do not need to replay the same chain.

The immediately following declaration `goldenZeroSectorInversionPacket` constructs this structure deterministically from any `GoldenZeroSectorCandidate`. The subsequent `SignedGoldenZeroSectorFactorization` source then takes `GoldenZeroSectorInversionPacket` as input and proceeds to exclusion of common odd prime divisors, two-adic branch classification, and fifth-power splitting.

Accordingly, this declaration adds no new algebraic identity by itself. Its importance is architectural: it packages already-proved invariants at the module boundary.

## Direct dependencies: definitions and lemmas

The structure itself has no tactic proof, but the types of its fields fix the upstream API.

### `GoldenZeroSectorCandidate`

This is the type of the `source` field. Every other field depends on coordinates and derived data of the same source, such as `source.r`, `source.s`, `source.c`, `source.d`, `source.A0`, and `source.B0`.

### Main upstream theorems

In the immediately following constructor `goldenZeroSectorInversionPacket`, the fields are filled from:

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

This one-to-one mapping makes the structure an aggregation point for the theorem museum accumulated upstream.

## Construction flow

Because this is a structure schema rather than a theorem, there is no tactic proof inside the declaration.

The logical organization is:

1. Store `source : GoldenZeroSectorCandidate`.
2. Store the sign information of the source.
3. Store the reparameterizations of $s,H,a$.
4. Store coprimality of $c,d$, non-divisibility by 5, and oddness.
5. Store discriminant, product, difference, sum, and square-reconstruction identities.
6. Store positivity and ordering of the signed factors.
7. Store cast equations and positivity of `A0`,`B0`.

Downstream code can therefore recover facts using projections such as `p.factor_product`, `p.factor_difference`, and `p.coprime_c_d`.

## Lean-specific processing

### Dependent fields

The type of each proof field depends on the preceding `source` field. For example,

```lean
factor_product :
  source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
```

is tied to exactly the same source candidate stored in the packet. Lean's type system therefore prevents accidentally mixing proofs belonging to different candidates.

### Proofs as data

In Lean, proof terms can be stored as ordinary structure fields. Here sign conditions and equalities are not comments or external obligations; they become values available to later theorems by field projection.

### A module-boundary API

Immediately after the constructor, the namespace closes and the generated source `SignedGoldenZeroSectorFactorization.lean` begins. The packet therefore acts as an interface between the inversion and factorization modules in the standalone source as well as logically in the proof.

## Redundancy and duplication

The structure repeats many facts that already exist as candidate theorems, so it is intentionally redundant at the source-text level. This is API materialization rather than accidental duplication.

Some fields, such as `A_pos`, `B_pos`, `A_lt_B`, `A0_pos`, and `B0_pos`, may appear partly derivable from one another together with the cast equations. Keeping them nevertheless allows downstream proofs to use the exact fact they need without re-establishing bridging lemmas.

The trade-off is maintenance cost: adding or changing an upstream invariant may require updating the packet constructor as well.

## Optimization candidates

Three design directions are plausible.

1. Split the fields into smaller semantic structures, then compose them into the packet.
2. Store only a minimal invariant basis and rederive inexpensive consequences downstream.
3. Keep the current flat, convenience-oriented packet even when some fields are derivable.

The current code follows option 3. Given that the factorization module directly projects many of these fields, the choice is reasonable.

For example, `A0_pos` could in principle be reconstructed from `A_pos` and `A0_cast`, but storing it avoids repeating the same `ℕ`/`ℤ` bridge proof downstream.

Exactly how far the packet can be minimized without worsening later proofs has not been verified here because this run does not perform a Lean build. The alternatives above are therefore **unverified design candidates**.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

The structure declaration itself directly relies mainly on basic facilities:

- `structure`
- `Nat` and `Int`
- `Nat.Coprime`
- `Odd`
- divisibility `∣`
- order `<`
- exponentiation `^`

However, its field types reference many project definitions whose transitive dependency closure is substantially larger. The exact minimal Mathlib import set has **not been verified** because no Lean build is performed in this task.

## Comparator challenge suitability

**It is not a good standalone theorem-proof challenge, but it is an excellent API-design Comparator challenge.**

Useful comparison designs include:

1. the current flat structure;
2. nested structures separating signs, arithmetic conditions, factor identities, and cast facts;
3. a minimal-invariant packet;
4. a design where consequences remain namespace theorems over `source` rather than stored fields.

Evaluation criteria would be:

- downstream proof length;
- amount of duplicated information;
- constructor maintenance cost;
- clarity of the dependency on the source candidate;
- stability as a module boundary.

## Comparison with the PDFs

The target branch contains the existing PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The GitHub connector does not return binary PDF bodies as text, and retrieval of the raw PDF also failed in this run. Consequently, a direct comparison against specific PDF pages, sections, or equation numbers is **unverified**, and no such location is guessed here.

The technical content of this explanation is grounded in the current `Flt5DkMath/FLT5StandAlone.lean` on the target branch, including the structure itself, its immediately following constructor, and the downstream factorization code.

## Next declaration to read

The next declaration is **0325 `goldenZeroSectorInversionPacket`**.

Its kind is **`def`**, not theorem.

```lean
def goldenZeroSectorInversionPacket (p : GoldenZeroSectorCandidate) :
    GoldenZeroSectorInversionPacket where
  source := p
  H_pos := p.H_pos
  s_neg := p.s_neg
  ...
  A0_pos := p.A0_pos
  B0_pos := p.B0_pos
```

Where 0324 defines the packet schema, 0325 deterministically constructs that packet from an arbitrary `GoldenZeroSectorCandidate` by filling every field with the corresponding upstream theorem.
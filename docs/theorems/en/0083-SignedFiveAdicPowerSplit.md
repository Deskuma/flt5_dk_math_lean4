# 0083 — `SignedFiveAdicPowerSplit`

## Lean type

```lean
structure SignedFiveAdicPowerSplit
    (u v w : ℕ) : Type where
  fiveAdic : SignedFiveAdicPacket u v w
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  carrier_eq : fiveAdic.carrier = 5 ^ 4 * a ^ 5
  residual_eq : fiveAdic.residual = 5 * b ^ 5
  distinguished_eq : fiveAdic.distinguished = 5 * a * b
```

This is not a theorem but a `structure ... : Type` that lifts the information in a five-adic packet to an exact fifth-power split. In dependency order it appears immediately after 0082 `signedFiveAdicPacket_gcd_eq_five`, and the following theorems consume its fields directly, so it must be documented as its own declaration.

## Mathematical statement

The structure stores that the carrier, residual, and distinguished terms of a `SignedFiveAdicPacket u v w` have the form

$$
carrier=5^4a^5,
$$

$$
residual=5b^5,
$$

$$
distinguished=5ab
$$

for positive coprime natural numbers $a,b$.

It also stores

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1.
$$

The preceding article established

$$
\gcd(carrier,residual)=5.
$$

The present structure packages the corresponding normal form obtained by removing that unique common factor $5$ and organizing the remaining parts into coprime fifth powers.

## Role in the full proof

`SignedFiveAdicPacket` was the common five-adic layer carrying mod-$25$ information, $5$-adic valuations, and the carrier/residual factorization. The present structure converts that packet into a fifth-power shape suitable for the later algebraic-integer and golden quadratic-form stages.

In particular, later declarations use it as follows:

- `five_not_dvd_b` proves $5\nmid b$.
- `coprime_scaled_a20_b5` proves coprimality of $5^{15}a^{20}$ and $b^5$.
- `nonempty_signedFiveAdicPowerSplit_of_packet` constructs an inhabitant from any five-adic packet.
- `signedFiveAdicPowerSplit_of_packet` and `signedFiveAdicPowerSplit_of_normalForm` provide chosen splits to downstream code.

Thus this structure is the API boundary between five-adic information and the exact power split.

## Direct dependencies

The declaration itself has a thin dependency surface:

- `SignedFiveAdicPacket u v w`
- `Nat.Coprime`
- multiplication and exponentiation on natural numbers

Mathematically, the immediately preceding theorem `signedFiveAdicPacket_gcd_eq_five` is a major input used to construct inhabitants, but the structure definition itself does not contain that theorem as a field. This separates specification from construction.

## Construction flow

The structure itself has no proof script. Instead, its fields fix the exact split specification step by step.

1. `fiveAdic` retains the original `SignedFiveAdicPacket`.
2. `a` and `b` are stored as the bases of the fifth-power parts.
3. `a_pos` and `b_pos` exclude degenerate zero bases.
4. `coprime_a_b` guarantees that no common factor other than the already assigned factor $5$ survives.
5. `carrier_eq` fixes the carrier's five-adic load to exactly $5^4$, with a fifth-power remainder.
6. `residual_eq` fixes the residual's five-adic load to exactly $5$, again with a fifth-power remainder.
7. `distinguished_eq` fixes the fifth-power base on the right-hand side to $5ab$.

These equalities are consistent with the packet identity

$$
carrier\cdot residual=distinguished^5,
$$

because

$$
(5^4a^5)(5b^5)=5^5a^5b^5=(5ab)^5.
$$

## Lean-specific processing

Because this is a `structure ... : Type`, it is data rather than a proposition. Downstream proofs can use projections such as `s.carrier_eq` and `s.residual_eq` directly.

The field `fiveAdic : SignedFiveAdicPacket u v w` preserves the complete source packet, so later proofs can still access information such as `residual_mod_twentyFive` and `source`. This is a refinement-layer design that adds information without discarding earlier facts.

The positivity and coprimality facts are stored as fields rather than re-derived theorems, allowing later proofs to consume them without replaying the construction.

## Redundancy and duplication

The structure contains deliberate redundancy. Given `carrier_eq`, `residual_eq`, and the original packet's `factor_eq`, one can in principle re-derive `distinguished_eq` using injectivity of fifth powers under the relevant positivity conditions.

Likewise, `coprime_a_b` is derived during construction from the gcd information established in 0082, so it could theoretically be exposed as a derived theorem instead of a field.

However, if downstream proofs use these facts repeatedly, storing them as fields is a reasonable proof cache. At this stage there is not enough evidence to conclude that the redundancy should be removed.

## Optimization candidates

The first candidate is a two-layer core/derived design. A core structure could store only `fiveAdic`, `a`, `b`, `carrier_eq`, and `residual_eq`, while positivity, coprimality, and `distinguished_eq` are exposed as projection theorems.

A second candidate is to retain the current fat record but centralize its construction in a single constructor helper. The facts proved by `nonempty_signedFiveAdicPowerSplit_of_packet` would then be assembled in one place while the downstream API remains simple.

A third candidate is to generalize from the hard-coded exponents $4$ and $1$ to a ramified prime $p$ with a parameterized exponent split. For the FLT5-specific development, however, that abstraction may cost more than it saves and is best treated as a Comparator design experiment for now.

## Required Mathlib imports and import optimization

The generated standalone source on the target branch uses `import Mathlib`. The structure itself only needs basic natural numbers, multiplication, powers, and `Nat.Coprime`.

So the declaration in isolation could likely use a much smaller import set. The surrounding `SignedFiveAdicPowerSplit.lean` file also uses gcd, divisibility, `omega`, `ring`, and `ZMod`, so a file-level minimal import set will necessarily be larger than the needs of this structure alone. The exact minimal set is unverified because no Lean build was run.

## Relation to the existing PDFs

Mathematically, this corresponds to the stage where the exceptional five-adic factor $5$ is assigned exactly between carrier and residual, after which the remaining parts are split into coprime fifth powers.

The repository Lean source is the primary authority for the type and its fields. I could not establish an exact theorem or page number in the existing Japanese and English PDFs corresponding one-to-one with this structure, so no PDF-specific numbering or quotation is supplied by inference.

## Comparator challenge suitability

This is well suited to a Comparator challenge, but primarily as an API-design comparison rather than a theorem-proving challenge.

Useful variants include:

- the current fat record,
- a minimal core plus derived projection theorems,
- separate structures for the carrier/residual split with `distinguished` reconstructed later,
- a generalized prime/exponent split interface.

Evaluation criteria should include downstream proof length, field reuse frequency, construction complexity, dependence on internal representation, and error locality.

## Next theorem to read

The next declaration is

```lean
theorem SignedFiveAdicPowerSplit.five_not_dvd_b
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) : ¬ 5 ∣ s.b := by
  ...
```

It combines

`residual_eq : residual = 5*b^5`

with the original packet fact

$$
residual\bmod25=5
$$

to show that if $5\mid b$, then $25\mid residual$, a contradiction. It is the first theorem confirming that no five-adic factor remains in the base $b$ after the power split.
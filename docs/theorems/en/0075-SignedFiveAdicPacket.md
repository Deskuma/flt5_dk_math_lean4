# 0075 — `SignedFiveAdicPacket`

## Lean type

```lean
structure SignedFiveAdicPacket (u v w : ℕ) : Type where
  normal : SignedBranchANormalForm u v w
  carrier : ℕ
  residual : ℕ
  distinguished : ℕ
  source : SignedFiveAdicSource u v w carrier residual distinguished
  factor_eq : carrier * residual = distinguished ^ 5
  carrier_pos : 0 < carrier
  residual_pos : 0 < residual
  distinguished_pos : 0 < distinguished
  five_dvd_carrier : 5 ∣ carrier
  five_dvd_distinguished : 5 ∣ distinguished
  residual_mod_twentyFive : residual % 25 = 5
  residual_shape : ∃ M : ℕ, residual = 5 + 25 * M
  residual_padicValNat : padicValNat 5 residual = 1
  carrier_padicValNat_shape :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

The source is the declaration in the `DkMath.FLT.Five` namespace contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch.

This article covers a `structure ... : Type` declaration rather than a theorem. It nevertheless has to be read here in dependency order: it consumes the preceding `SignedFiveAdicSource`, and the immediately following theorem `nonempty_signedFiveAdicPacket_of_normalForm` constructs an inhabitant of this structure.

## Mathematical statement

`SignedFiveAdicPacket u v w` is a record type collecting the common five-adic information that can be extracted from either signed Branch A orientation.

Mathematically it chooses three natural numbers

$$
carrier,\quad residual,\quad distinguished
$$

and records the factorization

$$
carrier\cdot residual=distinguished^5,
$$

positivity

$$
carrier>0,\qquad residual>0,\qquad distinguished>0,
$$

divisibility by five

$$
5\mid carrier,\qquad 5\mid distinguished,
$$

the precise residue class of the residual modulo $25$

$$
residual\equiv5\pmod{25},
$$

hence an explicit shape for some $M\in\mathbb N$

$$
residual=5+25M,
$$

the exact residual valuation

$$
v_5(residual)=1,
$$

and the carrier valuation shape

$$
\exists m\in\mathbb N,\qquad v_5(carrier)=4+5m.
$$

The `source` field additionally preserves the provenance of the common triple, recording whether it arose from the difference orientation or the sum orientation.

## Role in the full proof

Articles 0052–0056 establish the signed Branch A orientations and normal form. Articles 0059–0073 then build the sum residual machinery, modulo-$25$ information, the exact residual $5$-adic valuation, and the carrier valuation shape. Article 0074 packages the difference/sum provenance as `SignedFiveAdicSource`.

Article 0075 is the boundary at which those results are sealed into **one five-adic API that later layers can consume without reproving them**.

The source comment explicitly states the design intent: the packet records

- `residual ≡ 5 (mod 25)`,
- `v_5(residual)=1`, and
- `v_5(carrier) ≡ 4 (mod 5)`,

so later layers never have to reopen the residue proof.

The immediately following `nonempty_signedFiveAdicPacket_of_normalForm` constructs

```lean
Nonempty (SignedFiveAdicPacket u v w)
```

from `SignedBranchANormalForm u v w`, folding both the difference and sum branches into this common packet.

## Direct dependencies

The principal declarations that occur directly in the type are:

- `SignedBranchANormalForm`
- `SignedFiveAdicSource`
- `padicValNat`
- natural numbers `ℕ`
- multiplication, powers, order, divisibility, and remainder on `Nat`

From the perspective of constructing the fields in the following theorem, the practical proof dependencies also include the preceding lemmas:

- `GN5_cast_mod25_eq_five`
- `SumGN5_cast_mod25_eq_five`
- `mod_twentyFive_eq_five_of_zmod_eq_five`
- `eq_five_add_twentyFive_mul_of_mod_eq_five`
- `five_dvd_of_eq_five_add_twentyFive_mul`
- `not_twentyFive_dvd_of_mod_eq_five`
- `padicValNat_five_eq_one_of_dvd_not_sq`
- `padicValNat_carrier_shape_of_mul_eq_fifth`

Not all of these names occur literally in the structure type; they are proof dependencies for building an inhabitant of the packet.

## Declaration flow

There is no tactic proof body. Instead, the fields specify the contract of the common invariant in order.

1. `normal` retains the original `SignedBranchANormalForm u v w`.
2. `carrier`, `residual`, and `distinguished` store the three orientation-independent numbers.
3. `source` stores their difference/sum provenance.
4. `factor_eq` fixes the common fifth-power factorization.
5. The three `_pos` fields retain positivity in a form that is convenient for nonzero arguments.
6. `five_dvd_carrier` and `five_dvd_distinguished` record the explicit load of the prime 5.
7. `residual_mod_twentyFive` and `residual_shape` record that the residual is not merely divisible by 5 but lies exactly in residue class 5 modulo 25.
8. `residual_padicValNat` caches $v_5(residual)=1$.
9. `carrier_padicValNat_shape` stores, with an existential witness, that the carrier valuation is $4\pmod5$.

Thus the structure itself is a specification for the result of normalizing a signed orientation into common five-adic invariants.

## Lean-specific processing

### `structure ... : Type`

Unlike the preceding `SignedFiveAdicSource : Prop`, this declaration lives in `Type`. It is therefore not merely a proposition: it is a dependent record that stores numerical fields `carrier`, `residual`, and `distinguished` together with proofs about them.

### Mixing data and proofs

A field such as `carrier : ℕ` and a proof such as `carrier_pos : 0 < carrier` coexist in the same structure. Once a packet is available, Lean projections give direct access to both the arithmetic data and their guarantees.

### Relation to `Nonempty`

The following theorem does not return a `SignedFiveAdicPacket u v w` directly; it returns `Nonempty (...)`. This suggests that the packet is primarily used as a proof container asserting the existence of an inhabitant satisfying the common invariant, rather than as computational data to be extracted later.

### Existential fields

`residual_shape` and `carrier_padicValNat_shape` store witnesses inside the structure:

```lean
∃ M : ℕ, residual = 5 + 25 * M
```

and

```lean
∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

This preserves arithmetic witnesses that can later be unpacked directly with `rcases`, rather than keeping only congruence statements.

## Redundancy and duplication

The packet intentionally stores logically overlapping information.

For example,

```lean
residual_mod_twentyFive : residual % 25 = 5
```

implies `residual_shape` by Euclidean division. From `% 25 = 5`, one can also derive `5 ∣ residual` and `¬ 25 ∣ residual`, then reconstruct `residual_padicValNat = 1` using article 0072.

Likewise, `% 25 = 5` implies that the residual is nonzero, so over natural numbers `residual_pos` is derivable as well.

Finally, `carrier_padicValNat_shape` can be reconstructed from `factor_eq`, positivity/nonzeroness, and `residual_padicValNat` using article 0073.

Therefore a logically minimal record could contain fewer fields. The current design instead acts as a **proof cache**, prioritizing the ability of downstream code to consume established bridges without rerunning them. This redundancy is an important design feature rather than accidental duplication.

## Optimization candidates

1. `residual_shape` could be moved from a stored field to a projection theorem derived from `residual_mod_twentyFive`.
2. `residual_padicValNat` could likewise become a derived projection from `% 25 = 5`; keeping it cached may still be preferable if it is used frequently downstream.
3. `residual_pos` is derivable from `residual_mod_twentyFive`, so it is a candidate for removal if the goal is a smaller logical core.
4. `carrier_padicValNat_shape` is the result of applying article 0073 and could be theoremized instead of stored. This trades cheaper packet construction against a less convenient downstream API.
5. The relation between `five_dvd_carrier` and `carrier_padicValNat_shape` is also worth auditing. The latter normally implies divisibility by 5 because the valuation is at least 4, but an explicit field may be much easier to use than repeatedly converting through the `padicValNat` API.
6. A two-layer design—a minimal core structure plus a derived/cache layer—would be a strong Comparator candidate.

These are design candidates from source inspection only; no Lean build was run to validate them.

## Required Mathlib imports and import optimization candidates

The standalone artifact on the target branch begins with

```lean
import Mathlib
```

The structure itself directly needs Mathlib support for naturals, order, divisibility, remainder, powers, and `padicValNat`. Repository-local dependencies include `SignedBranchANormalForm` and `SignedFiveAdicSource`.

`import Mathlib` is therefore a confirmed safe import for the generated standalone artifact but is likely much broader than this declaration requires in isolation. The exact import lines of the split source module `DkMath/FLT/Five/SignedFiveAdic.lean` were not available on this branch during this run, so a minimal list of individual Mathlib modules remains **unverified and inferential**.

A safe import optimization pass would first identify the Mathlib module providing `padicValNat` and the repository modules providing `SignedBranchANormalForm` / `SignedFiveAdicSource`, then shrink `import Mathlib` incrementally.

## Comparator challenge suitability

**Low suitability as a proof-search challenge, high suitability as an API/design challenge.**

A useful task is: “Design the best Lean API for common five-adic invariants extracted from two signed orientations.”

Candidates include:

- the current fat record caching all derived facts,
- a thin record containing only minimal invariants plus projection theorems,
- a two-layer core/derived structure,
- branch-specific packets wrapped in a sum type, with a common interface supplied by a typeclass or coercion.

Good evaluation axes are downstream proof length, number of repeated derivations, constructor complexity, transparency of dependencies, rewrite ergonomics, and future generalizability.

## Next theorem to read

The next declaration in the Lean source is

```lean
private theorem nonempty_signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    Nonempty (SignedFiveAdicPacket u v w) := by
```

Article 0075 specifies the **shape** of the packet but has not yet proved that an inhabitant exists. The next theorem splits the `SignedBranchANormalForm` into its `differenceGap` and `sumGap` cases and actually assembles the packet from the modulo-$25$, divisibility, and valuation lemmas developed so far.

Therefore the next declaration in dependency order is `DkMath.FLT.Five.nonempty_signedFiveAdicPacket_of_normalForm`.

## Sources and notes

- The structure itself and the immediately following construction theorem were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.
- All three entry README files existed and were nonempty, with Japanese/English entries complete through 0074, so no initialization was needed.
- GitHub code search returned a 502 upstream error during this run; the known standalone Lean source on the target branch was fetched directly instead.
- A concrete page correspondence for this structure in the existing Japanese/English PDFs could not be verified during this run. No PDF-specific explanation or page number has therefore been invented.
- No Lean build was run. Optimization candidates remain unverified.

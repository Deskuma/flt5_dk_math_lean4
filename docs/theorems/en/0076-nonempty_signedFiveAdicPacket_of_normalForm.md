# 0076 — `nonempty_signedFiveAdicPacket_of_normalForm`

## Lean type

```lean
private theorem nonempty_signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    Nonempty (SignedFiveAdicPacket u v w) := by
  ...
```

This theorem states that whenever `SignedBranchANormalForm u v w` is available, there exists at least one inhabitant of the `SignedFiveAdicPacket u v w` structure introduced in the previous article. The theorem is `private`; it is an internal construction lemma used immediately by the canonical choice defined after it.

## Mathematical statement

`SignedBranchANormalForm` normalizes a hypothetical exponent-five counterexample into two signed Branch A orientations. For each orientation one can choose suitable values of `carrier`, `residual`, and `distinguished` so that

$$
carrier\cdot residual=distinguished^5,
$$

and simultaneously

$$
5\mid carrier,\qquad 5\mid distinguished,
$$

$$
residual\equiv5\pmod{25},
$$

$$
v_5(residual)=1,
$$

$$
v_5(carrier)=4+5m.
$$

The concrete choices are:

- difference orientation:
  `carrier = w - v`, `residual = GN5 (w - v) v`, `distinguished = u`;
- sum orientation:
  `carrier = u + v`, `residual = SumGN5 u v`, `distinguished = w`.

Thus the theorem is a packet constructor that merges two different factorizations into one common five-adic interface.

## Role in the full proof

Article 0075 declared the common specification `SignedFiveAdicPacket`, but it did not yet provide a value of that type. This theorem case-splits `SignedBranchANormalForm` and fills every packet field in both the difference and sum branches.

Immediately afterwards, the source defines

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

so this theorem sits exactly at the boundary between an existence proof and concrete data that can be selected and consumed by later code.

## Direct dependencies

The main direct dependencies are:

- `SignedBranchANormalForm`
- `SignedFiveAdicPacket`
- `SignedFiveAdicSource`
- `right_lt_of_fermat5Equation`
- `gap_pos_of_fermat5Equation`
- `Body5`
- `body5_eq_fifth_power_of_fermat`
- `GN5`
- `GN5_cast_mod25_eq_five`
- `SumGN5`
- `add_mul_sumGN5_eq_add_pow_five`
- `SumGN5_cast_mod25_eq_five`
- `mod_twentyFive_eq_five_of_zmod_eq_five`
- `eq_five_add_twentyFive_mul_of_mod_eq_five`
- `five_dvd_of_eq_five_add_twentyFive_mul`
- `not_twentyFive_dvd_of_mod_eq_five`
- `padicValNat_five_eq_one_of_dvd_not_sq`
- `sumGN5_pos`
- `padicValNat_carrier_shape_of_mul_eq_fifth`

The difference branch also uses `CounterexamplePack.hxy`: from `5 ∣ u`, assuming `5 ∣ v` would contradict coprimality, so it derives `¬ 5 ∣ v`.

## Proof flow

### Difference orientation

The proof first decomposes `hNF` as `⟨hPack, hOrientation⟩`, then handles the case `differenceGap h5u h5gap`.

From the Fermat equation it obtains $v\le w$ and $0<w-v$. Using `hPack.hxy` together with `h5u : 5 ∣ u`, it proves `¬ 5 ∣ v`.

From `body5_eq_fifth_power_of_fermat` it gets

$$
(w-v)\,GN5(w-v,v)=u^5.
$$

Then `GN5_cast_mod25_eq_five h5gap h5v` fixes the residual to 5 in `ZMod 25`. The bridge lemmas from articles 0068–0071 convert this successively into

$$
GN5(w-v,v)\bmod25=5,
$$

$$
GN5(w-v,v)=5+25M,
$$

$$
5\mid GN5(w-v,v),\qquad25\nmid GN5(w-v,v).
$$

Article 0072 then gives residual valuation one, and article 0073 gives the carrier valuation shape $4+5m$.

Finally every field of `SignedFiveAdicPacket` is filled with a record literal and returned as the witness of `Nonempty`.

### Sum orientation

For `sumGap h5w h5sum`, the proof chooses

$$
carrier=u+v,
$$

$$
residual=SumGN5(u,v),
$$

$$
distinguished=w.
$$

Using `add_mul_sumGN5_eq_add_pow_five` together with the Fermat equation it proves

$$
(u+v)\,SumGN5(u,v)=w^5.
$$

`SumGN5_cast_mod25_eq_five hPack.hxy h5sum` fixes the residual to 5 modulo 25, and from that point the proof follows the same bridge sequence as the difference branch.

Positivity comes from `Nat.add_pos_left hPack.hx v` and `sumGN5_pos hPack.hx hPack.hy`. The resulting facts are packed into the same `SignedFiveAdicPacket` structure.

## Lean-specific processing

Several Lean-specific moves are particularly visible here.

1. `rcases hNF with ⟨hPack, hOrientation⟩` followed by `cases hOrientation` explicitly decomposes the structure and its inductive provenance.
2. In the difference branch, the proof establishes `v ≤ w` and positivity first so that natural-number subtraction `w - v` is safe to use.
3. `simpa [Body5] using ...` reshapes an existing fifth-power factorization into the exact field type expected by the packet.
4. Equality in `ZMod 25` is translated back to a natural-number remainder equality and then to a witness-bearing representation `5 + 25*M`. Articles 0068–0071 localize this representation shift.
5. Terms such as `hcarrierPos.ne'`, `hresPos.ne'`, and `hPack.hx.ne'` project nonzeroness from positivity before calling article 0073.
6. The final `exact ⟨{ ... }⟩` nests a structure constructor inside the constructor of `Nonempty`.

## Redundancy and duplication

The largest duplication lies in the second half of the difference and sum branches. Once `hmod` has been established, both branches repeat essentially the same chain:

```text
hmod
→ hshape
→ h5res
→ h25res
→ hresVal
→ hcarrierShape
→ packet fields
```

In addition, `residual_shape`, information equivalent to residual divisibility by 5, and `residual_padicValNat` are mutually related facts that are stored or reconstructed separately. This is the proof-cache design already visible in article 0075: it trades a longer constructor for easier downstream use.

## Optimization candidates

The most natural refactoring is to extract the common second half into a helper. For example:

```lean
private theorem mkSignedFiveAdicPacket
    ...
    (hfactor : carrier * residual = distinguished ^ 5)
    (hmod : residual % 25 = 5)
    ... :
    SignedFiveAdicPacket u v w := ...
```

With such a helper, each orientation would only need to construct its `carrier`, `residual`, `distinguished`, factorization, and mod-25 input.

A second possibility is to split `SignedFiveAdicPacket` into core facts and derived facts. That could shorten construction while exposing derived fields through theorems afterwards.

These are design proposals only: no Lean build was run here, so downstream usage should be checked before changing the API.

## Required Mathlib imports and import optimization

The standalone artifact available on the museum branch uses `import Mathlib`. Its manifest records the original module for this region as `DkMath/FLT/Five/SignedFiveAdic.lean`.

However, that split source file could not be fetched from the same path on this branch, so the exact minimal imports for this theorem alone remain unverified.

From the proof body, the visible external ingredients are mainly natural-number arithmetic and divisibility, `ZMod`, `padicValNat`, `omega`, and `norm_num`. A safe import optimization pass should first restore or inspect the actual imports of `SignedFiveAdic.lean` and compare them with the umbrella `Mathlib` import.

## Relation to the existing PDFs

The Lean source in the repository is used as the final authority. In this inspection, no concrete page in the existing Japanese or English PDFs was identified as a one-to-one presentation of this private helper. Therefore no PDF-specific page number or explanation is inferred here.

## Comparator challenge suitability

**Suitable.** Two challenge forms are especially natural.

The first is a proof-refactoring challenge: compare the current duplicated two-branch implementation with a version that extracts a shared constructor helper. Useful metrics include LOC, dependency count, proof-state locality, and resilience to later packet-field additions.

The second is an API challenge: compare the current fat packet with a thin packet plus derived lemmas, or a two-layer core/derived design.

The interesting comparison is not the elementary arithmetic itself, but how the same five-adic invariant is normalized from two orientations into a common interface.

## Next declaration

The next declaration is

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

This article proves `Nonempty (SignedFiveAdicPacket u v w)`; the next declaration applies `Classical.choice` to select an actual packet. The API therefore moves from “a five-adic packet exists” to “a canonical packet is available for direct downstream use.”
# 0082 — `signedFiveAdicPacket_gcd_eq_five`

## Lean type

```lean
theorem signedFiveAdicPacket_gcd_eq_five
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nat.gcd p.carrier p.residual = 5 := by
  apply Nat.dvd_antisymm
  · cases p.source with
    | difference hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hgapV : Nat.Coprime (w - v) v :=
          coprime_gap_y_of_counterexamplePack p.normal.pack
        have hDcopV : Nat.Coprime (Nat.gcd (w - v) (GN5 (w - v) v)) v :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hgapV
        have hDcopV4 := Nat.Coprime.pow_right 4 hDcopV
        apply hDcopV4.dvd_of_dvd_mul_right
        exact dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    | sum hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hsumU : Nat.Coprime (u + v) u :=
          Nat.coprime_self_add_left.mpr p.normal.pack.hxy.symm
        have hDcopU : Nat.Coprime (Nat.gcd (u + v) (SumGN5 u v)) u :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hsumU
        have hDcopU4 := Nat.Coprime.pow_right 4 hDcopU
        apply hDcopU4.dvd_of_dvd_mul_right
        exact dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  · have h5res : 5 ∣ p.residual := by
      rcases p.residual_shape with ⟨M, hM⟩
      use 1 + 5 * M
      omega
    exact Nat.dvd_gcd p.five_dvd_carrier h5res
```

## Mathematical statement

For every `SignedFiveAdicPacket u v w`, the greatest common divisor of its carrier and residual is exactly $5$:

$$
\gcd(p.carrier,p.residual)=5.
$$

The proof establishes the two divisibilities

$$
\gcd(p.carrier,p.residual)\mid5,
\qquad
5\mid\gcd(p.carrier,p.residual)
$$

separately and combines them with `Nat.dvd_antisymm`.

## Role in the full proof

By 0081, both the sum orientation and the difference orientation have matching gcd-control lemmas. This theorem unifies them under the provenance split carried by `SignedFiveAdicSource` and proves that the packet factors share exactly one exceptional five-adic factor.

The subsequent `SignedFiveAdicPowerSplit` construction divides both carrier and residual by $5$ and proves that the resulting quotients are coprime. This theorem is the entry point to that step.

## Direct dependencies

- `SignedFiveAdicPacket`
- `SignedFiveAdicSource`
- `coprime_gap_y_of_counterexamplePack`
- `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`
- `dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5`
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, `Nat.dvd_gcd`
- `Nat.Coprime.of_dvd_left`, `Nat.Coprime.pow_right`, `Nat.Coprime.dvd_of_dvd_mul_right`
- `Nat.coprime_self_add_left`
- `Nat.dvd_antisymm`

It also directly consumes the packet fields `p.normal.pack.hxy`, `p.five_dvd_carrier`, and `p.residual_shape`.

## Proof flow

1. Split equality with `Nat.dvd_antisymm` into two divisibility goals.
2. For the upper bound `gcd ∣ 5`, case-split on `p.source` into the difference and sum orientations.
3. In the difference branch, rewrite carrier and residual as `w-v` and `GN5 (w-v) v`.
4. Obtain `Coprime (w-v) v` from the primitive counterexample. Hence the gcd is coprime to $v$, and therefore to $v^4$.
5. Apply the existing difference gcd-control lemma with the gcd itself as `q`. It shows that the gcd divides $5v^4$. Coprimality removes the $v^4$ factor, leaving `gcd ∣ 5`.
6. In the sum branch, construct `Coprime (u+v) u`, apply 0081 to the gcd, obtain divisibility by $5u^4$, and remove $u^4$ by coprimality.
7. For the lower bound `5 ∣ gcd`, reconstruct `5 ∣ residual` from `p.residual_shape : ∃ M, residual = 5 + 25*M`.
8. Combine this with `p.five_dvd_carrier` using `Nat.dvd_gcd`.
9. Finish by antisymmetry of divisibility.

## Lean-specific processing

After `cases p.source`, the constructor equalities `hcarrier` and `hresidual` allow the abstract packet fields to be rewritten back into their concrete `GN5` or `SumGN5` forms.

`Nat.Coprime.of_dvd_left` lowers coprimality from the full carrier to its gcd with the residual, because that gcd divides the carrier. `pow_right 4` then lifts the statement to the fourth power.

The crucial cancellation step is `dvd_of_dvd_mul_right`: if the gcd divides $5x^4$ and is coprime to $x^4$, then it must divide $5$.

On the lower-bound side, the proof derives `5 ∣ residual` from the stored shape via `use 1 + 5 * M; omega`. The packet also stores `residual_padicValNat = 1`, but this proof deliberately uses the more direct shape field.

## Redundancy and duplication

The difference and sum branches are highly symmetric. They differ only in the concrete carrier/residual formulas, the way coprimality with the base is obtained, and the final gcd-control lemma that is called.

`SignedFiveAdicPacket` also stores overlapping information about the residual: mod-$25$ data, a shape equation, and a valuation. This theorem reconstructs `5 ∣ residual` from `residual_shape`. A dedicated `five_dvd_residual` field or projection theorem would shorten the lower-bound part, at the cost of additional API redundancy.

## Optimization candidates

The first candidate is a common gcd-upper-bound helper for the shared pattern

$$
D\mid5x^4,\quad \gcd(D,x)=1
\Longrightarrow D\mid5.
$$

The second is a projection theorem exposing `5 ∣ residual` from the packet without forcing downstream code to depend on the chosen representation field.

The third is an orientation interface packaging the carrier, residual, base coprimality, and gcd-control lemma uniformly across difference and sum sources. Whether that abstraction is worthwhile is not yet verified; it may cost more than the duplicated proof it removes.

## Required Mathlib imports and import optimization

The generated standalone file on this branch uses `import Mathlib`. This theorem directly relies mainly on natural-number gcd/coprimality, divisibility, and `omega`.

A narrower import set should likely be possible around the natural-number gcd/coprime API and the `omega` tactic. However, the exact import graph of the split source module `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` was not independently verified on this branch, so the minimal import set remains unverified.

## Relation to the existing PDFs

Mathematically, this is the point where the proof establishes that the only common five-adic factor of the two packet factors is $5$, and that $5$ actually occurs in both.

The repository Lean source is the primary source for the precise theorem type and proof script. A one-to-one theorem number or page correspondence in the existing Japanese and English PDFs was not established in this run, so no PDF-specific numbering or quotation is inferred.

## Comparator challenge suitability

This theorem is very suitable for a Comparator challenge. Candidate approaches include:

- the current source case split plus two gcd-control lemmas,
- a version with a common gcd-upper-bound helper,
- a valuation-only proof of `gcd = 5`,
- a stronger packet API exposing `five_dvd_residual` directly.

Useful evaluation criteria are not only proof length, but also symmetry between the two orientations, dependence on packet internals, downstream reuse in the power split, and locality of error messages.

## Next declaration to read

The next declaration is the immediately following structure

```lean
structure SignedFiveAdicPowerSplit
    (u v w : ℕ) : Type where
  fiveAdic : SignedFiveAdicPacket u v w
  a : ℕ
  b : ℕ
  ...
```

This theorem supplies

$$
\gcd(p.carrier,p.residual)=5,
$$

which is then used to strip the unique common factor $5$ from carrier and residual and package the resulting coprime fifth-power data into the next record.
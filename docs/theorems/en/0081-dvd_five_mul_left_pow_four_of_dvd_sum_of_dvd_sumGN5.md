# 0081 — `dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5`

## Lean type

```lean
private theorem dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
    {u v q : ℕ} (hqsum : q ∣ u + v) (hqres : q ∣ SumGN5 u v) :
    q ∣ 5 * u ^ 4 := by
  have hsumZ : (u : ZMod q) + (v : ZMod q) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff (u + v) q).2 hqsum
  have hvZ : (v : ZMod q) = -(u : ZMod q) :=
    eq_neg_of_add_eq_zero_right hsumZ
  have hresZ : (SumGN5 u v : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (SumGN5 u v) q).2 hqres
  apply (ZMod.natCast_eq_zero_iff (5 * u ^ 4) q).1
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub h] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ
  · have huv : u ≤ v := Nat.le_of_not_ge h
    rw [SumGN5, if_neg h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub huv] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ
```

## Mathematical statement

For natural numbers $u,v,q$, if $q$ divides both the carrier $u+v$ and the residual `SumGN5 u v`, then

$$
q\mid 5u^4.
$$

The core argument works modulo $q$: from $u+v\equiv0$ we obtain $v\equiv-u$, and evaluating `SumGN5 u v` modulo $q$ reduces it to the same residue as $5u^4$. Since $q\mid\mathrm{SumGN5}(u,v)$, that residue vanishes, hence $q\mid5u^4$.

The lemma does not yet state that the gcd is $5$. It is an intermediate result constraining any common divisor $q$ to the factor $5u^4$.

## Role in the overall proof

By 0080 the common five-adic packet has been constructed and routed back to the Branch-B contradiction interface. This lemma opens the `SignedFiveAdicPowerSplit.lean` layer, where the common factors of the packet's carrier and residual are analyzed further.

In the sum-source branch of the immediately following `signedFiveAdicPacket_gcd_eq_five`, the lemma is used as

```lean
exact dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
  (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
```

with $q=\gcd(u+v,\mathrm{SumGN5}(u,v))$. That gcd is also coprime to $u$, so the $u^4$ factor can be removed and the gcd is shown to divide $5$. The difference source uses the corresponding earlier lemma `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`.

Thus this lemma is the local algebraic bridge that supplies the gcd upper bound $\gcd(carrier,residual)\mid5$ in the sum orientation.

## Direct dependencies

- `SumGN5`
- `ZMod.natCast_eq_zero_iff`
- `eq_neg_of_add_eq_zero_right`
- `Nat.cast_add`
- `Nat.cast_sub`
- `Nat.le_of_not_ge`
- `push_cast`
- `ring_nf`

Its direct downstream user is `signedFiveAdicPacket_gcd_eq_five`.

Mathematically, only `q ∣ u+v` and `q ∣ SumGN5 u v` are needed. `CounterexamplePack`, the Fermat equation, coprimality, and five-adic valuations do not occur in the assumptions, so the lemma is strongly localized.

## Proof flow

1. Convert `hqsum : q ∣ u + v` to the equality

   $$
   u+v=0
   $$

   in `ZMod q`.
2. Deduce

   $$
   v=-u.
   $$
3. Convert `hqres : q ∣ SumGN5 u v` to

   $$
   \mathrm{SumGN5}(u,v)=0\quad\text{in }\mathrm{ZMod}(q).
   $$
4. Convert the goal $q\mid5u^4$ to the modular equality $5u^4=0$.
5. Since `SumGN5` is piecewise and contains natural-number subtraction, split on `v ≤ u`.
6. In each branch, use `Nat.cast_sub` with the appropriate order proof and substitute $v=-u$.
7. Use `ring_nf` to normalize the residual expression and $5u^4$ to the same polynomial normal form; the resulting goal is exactly `hresZ`.

## Lean-specific processing

The main Lean-specific issue is that `SumGN5` is a piecewise definition over `Nat` and contains natural subtraction. Over an integer or ring polynomial one could simply substitute $v=-u$, but `Nat.cast_sub` requires a proof that the subtraction is valid as an actual difference.

Therefore the proof performs `by_cases h : v ≤ u`. In the first branch it uses `Nat.cast_sub h`; in the second it derives `huv : u ≤ v` and uses `Nat.cast_sub huv`.

`ZMod.natCast_eq_zero_iff` is the key bridge between divisibility and modular vanishing, used both at the entrance and the exit. `push_cast` moves the natural-number expressions into ring expressions over `ZMod q`, and `ring_nf` performs the final polynomial normalization.

It is also notable that the proof does not separately assume or handle `q > 0`. The existing `ZMod q` and `ZMod.natCast_eq_zero_iff` APIs support the general statement, so the script does not need a special $q=0$ branch.

## Redundancy and duplication

The two branches are nearly isomorphic; only the unfolded branch of `SumGN5` and the order proof passed to `Nat.cast_sub` differ.

There is also a broader duplication with the difference-orientation lemma

```lean
dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
```

Both implement the same gcd-control pattern: a common divisor of carrier and residual is forced into five times a fourth power.

Thus there is local branch duplication and a wider difference/sum pattern duplication. However, because `GN5` and `SumGN5` have different defining forms, it is not yet verified that abstracting them would actually simplify the code.

## Optimization candidates

The first candidate is to separate a congruence lemma for `SumGN5`:

$$
q\mid u+v
\Longrightarrow
\mathrm{SumGN5}(u,v)\equiv5u^4\pmod q.
$$

Then the present lemma would become a thin wrapper combining that congruence with `hqres` to recover divisibility.

A second possibility is to factor the repeated `push_cast`, substitution, and `ring_nf` pattern out of the two order branches. The benefit may be too small to justify an extra API lemma, however.

A third candidate is a common abstract gcd-control lemma shared with the difference orientation. This depends on what abstraction level is chosen for the `GN5` and `SumGN5` residual polynomials, so for now it remains a design proposal rather than a verified simplification.

## Required Mathlib imports and import optimization candidates

The generated standalone `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses `import Mathlib`. The Mathlib features directly used here are mainly `ZMod`, natural-number casts, `push_cast`, `ring_nf`, and elementary order lemmas.

Conceptually, imports around `Mathlib.Data.ZMod.Basic`, cast support, and ring normalization should dominate. However, the exact import graph of the split source `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` has not been verified on the museum branch in this run, so the minimal import set remains unverified. Reducing `import Mathlib` should be checked by compiling the split module separately, which is outside this museum run.

## Relation to the existing PDFs

Mathematically, the lemma is a local gcd argument: a common divisor of $u+v$ and the sum residual is used to reduce that residual modulo the common divisor and constrain the divisor to $5u^4$. The Lean source on the target branch is the primary source for the exact type and proof script.

No one-to-one theorem number or page corresponding to this private helper was established in the existing Japanese and English PDFs during this run. Therefore no PDF-specific numbering, wording, or page mapping has been inferred.

## Comparator challenge suitability

This is a strong candidate. At least the following approaches can be compared:

- the current `ZMod q` + case split + `ring_nf` proof;
- a proof centered on `Nat.ModEq`;
- a proof that first establishes a general congruence for `SumGN5` and then converts it back to divisibility;
- an API that abstracts the difference/sum gcd-control pattern together.

Evaluation should consider not only proof length but also handling of natural subtraction, automatic treatment of the $q=0$ edge case, error quality, and reuse from `signedFiveAdicPacket_gcd_eq_five`.

## Next theorem to read

The next declaration is

```lean
theorem signedFiveAdicPacket_gcd_eq_five
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nat.gcd p.carrier p.residual = 5 := by
  ...
```

It dispatches on the packet source, uses this lemma in the sum orientation and the earlier gcd-control lemma in the difference orientation to prove

$$
\gcd(p.carrier,p.residual)\mid5,
$$

while `five_dvd_carrier` and `residual_shape` stored in the packet give

$$
5\mid\gcd(p.carrier,p.residual).
$$

Antisymmetry then fixes the gcd exactly at $5$. This is the first major theorem of the `SignedFiveAdicPowerSplit` layer.
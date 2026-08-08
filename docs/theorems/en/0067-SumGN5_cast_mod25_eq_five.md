# 0067 — `SumGN5_cast_mod25_eq_five`

## Lean type

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5 := by
  have h5u : ¬ 5 ∣ u :=
    five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
  have h5v : ¬ 5 ∣ v :=
    five_not_dvd_right_of_coprime_of_dvd_add hcop h5sum
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    subst u
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * v = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (v : ZMod 25) = 5 * (k : ZMod 25) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod 25)) hcarrier
      simpa using hcast
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (v : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5v with ⟨q, hq⟩
    simp only [Nat.add_sub_cancel_left]
    push_cast
    rw [hdZ, hq]
    ring_nf
    rw [hq]
    ring_nf
    simp only [show (25 : ZMod 25) = 0 by decide,
      show (50 : ZMod 25) = 0 by decide,
      show (250 : ZMod 25) = 0 by decide,
      show (625 : ZMod 25) = 0 by decide,
      mul_zero, add_zero, sub_zero]
  · rw [SumGN5, if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
    subst v
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * u = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (u : ZMod 25) = 5 * (k : ZMod 25) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod 25)) hcarrier
      simpa using hcast
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (u : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5u with ⟨q, hq⟩
    simp only [Nat.add_sub_cancel_left]
    push_cast
    rw [hdZ, hq]
    ring_nf
    rw [hq]
    ring_nf
    simp only [show (25 : ZMod 25) = 0 by decide,
      show (50 : ZMod 25) = 0 by decide,
      show (250 : ZMod 25) = 0 by decide,
      show (625 : ZMod 25) = 0 by decide,
      mul_zero, add_zero, sub_zero]
```

This declaration is `private`. Inside `SignedFiveAdic.lean`, it fixes the sum-orientation residual `SumGN5` to the residue 5 modulo 25.

## Mathematical statement

For natural numbers `u,v`, if they are coprime and

$$
5\mid(u+v),
$$

then

$$
\operatorname{SumGN5}(u,v)\equiv5\pmod{25}.
$$

`SumGN5` is defined piecewise in order to avoid unsafe use of `Nat.sub`. In the branch `v ≤ u`, write `u=v+d`. Then the carrier condition becomes

$$
u+v=d+2v=5k,
$$

hence in `ZMod 25`,

$$
d=5k-2v.
$$

Substituting this into the `SumGN5` polynomial reduces the essential surviving term modulo 25 to the fourth power of `v`. Coprimality together with `5∣u+v` implies `5∤v`, and article 0065 gives

$$
v^4=1+5q\quad\text{in }\mathrm{ZMod}\ 25.
$$

The whole polynomial therefore collapses to 5. The `u ≤ v` branch is exactly symmetric, using `5∤u` and `u^4=1+5q` instead.

## Role in the whole proof

Article 0066 fixes the difference-orientation residual `GN5` to 5 modulo 25. This theorem supplies the same exact five-adic information for the sum orientation.

In the `sumGap` branch of `nonempty_signedFiveAdicPacket_of_normalForm`, the theorem is called directly as

```lean
have hcast : (SumGN5 u v : ZMod 25) = 5 :=
  SumGN5_cast_mod25_eq_five hPack.hxy h5sum
```

and then converted back to

$$
\operatorname{SumGN5}(u,v)\bmod25=5.
$$

From this, the proof obtains

$$
5\mid\operatorname{SumGN5}(u,v),\qquad
25\nmid\operatorname{SumGN5}(u,v),
$$

and finally

$$
v_5(\operatorname{SumGN5}(u,v))=1.
$$

Thus the difference and sum orientations become indistinguishable to later layers: both expose the common interface `residual_mod_twentyFive = 5`.

## Direct dependencies

- `SumGN5` — 0059
- `five_not_dvd_left_of_coprime_of_dvd_add` — 0062
- `five_not_dvd_right_of_coprime_of_dvd_add` — 0063
- `fourth_power_zmod25_decomposition` — 0065
- `Nat.exists_eq_add_of_le`
- `Nat.le_of_not_ge`
- `Nat.add_sub_cancel_left`
- `congrArg`
- `eq_sub_of_add_eq`
- `omega`
- `push_cast`
- `ring_nf`
- `simp only`
- `ZMod 25`

The essential mathematical dependencies are 0062 and 0063, which ensure that neither component is divisible by 5, and 0065, which lifts the fourth power of a nonzero residue to a `1+5q` form modulo 25.

## Proof flow

1. Use 0062 and 0063 to obtain `h5u : 5 ∤ u` and `h5v : 5 ∤ v`.
2. Split with `by_cases h : v ≤ u`, matching the piecewise definition of `SumGN5`.
3. In the `v ≤ u` branch, write `u=v+d` and extract a witness `k` from `5∣u+v`.
4. Use `omega` to derive `d+2v=5k`.
5. Cast this natural-number equality into `ZMod 25` with `congrArg`, then rewrite it as `d=5k-2v`.
6. Apply 0065 to `v` and obtain `v^4=1+5q`.
7. Eliminate `Nat.sub` with `Nat.add_sub_cancel_left`, then move the polynomial into `ZMod 25` with `push_cast`.
8. Substitute `hdZ` and `hq`, and normalize twice with `ring_nf`.
9. Explicitly simplify the coefficients `25,50,250,625` to zero in `ZMod 25`, yielding 5.
10. In the other branch, derive `u ≤ v` and perform the exact symmetric argument with `u` and `v` interchanged.

## Lean-specific processing

The main Lean-specific feature is that `SumGN5` is piecewise because `Nat.sub` is truncated subtraction. Mathematically one would prefer to regard the expression as a single symmetric polynomial identity, but the current proof mirrors the order split of the definition.

Introducing the nonnegative difference `d` with `Nat.exists_eq_add_of_le` allows `Nat.sub` to disappear via `Nat.add_sub_cancel_left`, after which ordinary polynomial algebra applies.

The proof also concretizes the divisibility witness from `h5sum` and uses `omega` before crossing from natural-number arithmetic to `ZMod` algebra. `congrArg` is the explicit bridge for that cast.

## Redundancy and duplication

The two branches are almost perfect mirror images under exchange of `u` and `v`. The constructions of `hcarrier`, `hcarrierZ`, `hdZ`, the application of 0065, `push_cast`, the two `ring_nf` calls, and the final `simp only` are duplicated.

As in 0066, the explicit simplification of `25,50,250,625` by separate `show ... = 0 by decide` facts is mechanical.

The sequence `rw [hq]; ring_nf; rw [hq]; ring_nf` uses the same fourth-power equality twice because normalization recreates a fourth-power occurrence. This is understandable operationally but does not expose the mathematical intent very clearly.

## Optimization candidates

The first candidate is a shared local lemma. A statement such as “if `a=b+d`, `d+2b=5k`, and `5∤b`, then the relevant residual polynomial is 5 in `ZMod 25`” would reduce both piecewise branches to argument placement.

The second candidate is to prove symmetry of `SumGN5` first and make only one order branch mathematically substantive. If `SumGN5 u v = SumGN5 v u` is available in a convenient form, most of the duplicated branch can disappear.

A third candidate is a dedicated `ZMod 25` residual lemma extracting only the first five-adic term from `u+v≡0 (mod 5)`. Since the theorem needs mod-25 information, merely using a mod-5 equation is insufficient; retaining a multiple-of-5 witness as the current proof does is therefore structurally reasonable.

A fourth candidate is to factor out the generic fact that multiples of 25 vanish in `ZMod 25`, eliminating the concrete `show` list.

## Required Mathlib imports and import optimization

The generated `Flt5DkMath/FLT5StandAlone.lean` that was verified uses `import Mathlib`. In isolation, this theorem needs at least natural-number order and subtraction, `Nat.Coprime`, `ZMod`, `omega`, `push_cast`, `ring_nf`, `simp`, and `decide`.

The exact import line of the source module `DkMath/FLT/Five/SignedFiveAdic.lean` was not directly available on the target museum branch, so exact minimal module names are unverified and this part is explicitly speculative.

Import optimization should separate the `ZMod` and tactic dependencies, then trace the origins of the `Nat.Coprime`, order, and subtraction lemmas. A Lean build would be required to certify the resulting import set; no Lean build was run in this article.

## Comparator challenge suitability

This theorem is highly suitable. The mathematical target is compact while the Lean implementation admits several distinct architectures:

- Current: prove both piecewise branches directly.
- Candidate A: factor both branches through a common local lemma.
- Candidate B: use symmetry of `SumGN5` and prove only one branch.
- Candidate C: introduce a specialized `ZMod 25` residual lemma.
- Candidate D: replace concrete coefficient elimination by generic `ZMod` API.

Useful comparison axes are proof length, left/right duplication, visibility of mathematical symmetry, dependence on `Nat.sub`, tactic dependence, hard-coding of modulus 25, and future generalizability.

## Evidence and speculation

The theorem name, type, full proof body, and its downstream consumer were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The same source shows that the `sumGap` branch of `nonempty_signedFiveAdicPacket_of_normalForm` calls this theorem directly and transforms the resulting `ZMod 25` equality into natural-number mod 25, divisibility by 5, non-divisibility by 25, and finally `padicValNat = 1`.

GitHub code search returned a transient upstream 502 during this run, so repository-wide search for the split source file and PDFs could not be completed through search. The precise PDF pages corresponding to this theorem remain unverified, and no page number or PDF wording has been guessed.

## Next theorem to read

```lean
private theorem mod_twentyFive_eq_five_of_zmod_eq_five
    {n : ℕ} (h : (n : ZMod 25) = 5) :
    n % 25 = 5
```

Articles 0066 and 0067 establish equalities in `ZMod 25`; this next bridge converts them back into the natural-number remainder equation `n % 25 = 5` required by the downstream packet construction. Both orientations converge at this point, so it is the natural next declaration in dependency order.

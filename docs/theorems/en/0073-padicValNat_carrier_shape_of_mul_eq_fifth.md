# 0073 — `padicValNat_carrier_shape_of_mul_eq_fifth`

## Lean type

```lean
theorem padicValNat_carrier_shape_of_mul_eq_fifth
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (_hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 5)
    (hrVal : padicValNat 5 residual = 1) :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow :
      padicValNat 5 (distinguished ^ 5) =
        5 * padicValNat 5 distinguished := by simp
  have hmul :
      padicValNat 5 (carrier * residual) =
        padicValNat 5 carrier + padicValNat 5 residual := by
    simpa using (padicValNat.mul (p := 5) hc0 hr0)
  have hvalEq :
      5 * padicValNat 5 distinguished = padicValNat 5 carrier + 1 := by
    calc
      5 * padicValNat 5 distinguished =
          padicValNat 5 (distinguished ^ 5) := hpow.symm
      _ = padicValNat 5 (carrier * residual) := by rw [hEq]
      _ = padicValNat 5 carrier + padicValNat 5 residual := hmul
      _ = padicValNat 5 carrier + 1 := by rw [hrVal]
  have hdValPos : 0 < padicValNat 5 distinguished := by
    have : 0 < 5 * padicValNat 5 distinguished := by
      rw [hvalEq]
      exact Nat.succ_pos _
    exact Nat.pos_of_mul_pos_left this
  have hcVal :
      padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 :=
    Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat 5 distinguished - 1, ?_⟩
  have hsplit :
      (padicValNat 5 distinguished - 1) + 1 = padicValNat 5 distinguished :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hdValPos)
  calc
    padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 := hcVal
    _ = 5 * ((padicValNat 5 distinguished - 1) + 1) - 1 := by rw [hsplit]
    _ = 4 + 5 * (padicValNat 5 distinguished - 1) := by omega
```

The source of record is the `DkMath/FLT/Five/SignedFiveAdic.lean` section embedded in the generated `Flt5DkMath/FLT5StandAlone.lean` on branch `docs/flt5-theorem-museum`.

## Mathematical statement

Let `carrier`, `residual`, and `distinguished` be natural numbers satisfying

$$
carrier\cdot residual=distinguished^5.
$$

Assume `carrier` and `residual` are nonzero and

$$
v_5(residual)=1.
$$

Then there exists $m\in\mathbb N$ such that

$$
v_5(carrier)=4+5m.
$$

Equivalently,

$$
v_5(carrier)\equiv4\pmod5.
$$

The core calculation is additivity of valuation. The product equation gives

$$
v_5(carrier)+v_5(residual)=5v_5(distinguished).
$$

Substituting $v_5(residual)=1$ yields

$$
v_5(carrier)+1=5v_5(distinguished),
$$

so the carrier valuation is one less than a multiple of five and therefore lies in the residue class $4\pmod5$.

## Role in the full proof

Article 0072 `padicValNat_five_eq_one_of_dvd_not_sq` fixes the residual valuation at exactly one. The present theorem combines that fact with the fifth-power product

$$
carrier\cdot residual=distinguished^5
$$

to force the five-adic load of the other factor into the exact shape

$$
4+5m.
$$

This conclusion is stored immediately afterward in the `SignedFiveAdicPacket` field

```lean
carrier_padicValNat_shape :
  ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

and `nonempty_signedFiveAdicPacket_of_normalForm` calls the theorem directly in both the difference and sum orientations. Later layers can therefore consume the packet without reopening the mod-25 argument.

## Direct dependencies

The main Lean declarations used directly by the proof are:

- `padicValNat`
- `padicValNat.mul`
- `Fact (Nat.Prime 5)`
- `Nat.eq_sub_of_add_eq`
- `Nat.sub_add_cancel`
- `Nat.succ_le_of_lt`
- `Nat.pos_of_mul_pos_left`
- `omega`
- `simp` for `padicValNat 5 (distinguished ^ 5) = 5 * padicValNat 5 distinguished`

At the theorem-museum dependency level, `hEq` and `hrVal` are the immediate mathematical inputs, with article 0072 supplying the latter shape.

## Proof flow

1. Install a local `Fact (Nat.Prime 5)` instance.
2. Rewrite the valuation of the fifth power as

   $$
   v_5(distinguished^5)=5v_5(distinguished).
   $$
3. Use `padicValNat.mul` to obtain

   $$
   v_5(carrier\cdot residual)=v_5(carrier)+v_5(residual).
   $$
4. Combine `hEq` and `hrVal` to derive

   $$
   5v_5(distinguished)=v_5(carrier)+1.
   $$
5. Since the right-hand side is positive, deduce $v_5(distinguished)>0$.
6. Safely rearrange in natural numbers to

   $$
   v_5(carrier)=5v_5(distinguished)-1.
   $$
7. Choose

   $$
   m=v_5(distinguished)-1.
   $$
8. Close the arithmetic identity

   $$
   5(m+1)-1=4+5m
   $$

   with `omega`.

## Lean-specific processing

### `Fact (Nat.Prime 5)`

The multiplication theorem for `padicValNat` expects primality of the base through typeclass machinery, so the proof installs

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

locally. Mathematically this is only the statement that 5 is prime, but the instance is required by the API.

### Nonzero hypotheses

`padicValNat.mul` directly consumes `hc0` and `hr0`. In contrast, `_hd0 : distinguished ≠ 0` is not used by the proof body. Positivity of the distinguished valuation is recovered from `hvalEq` instead.

### Natural-number subtraction

The witness is chosen as `padicValNat 5 distinguished - 1`. Since natural subtraction truncates, the proof first establishes `hdValPos` and then uses `Nat.sub_add_cancel`. This bookkeeping would disappear over integers, so it is specifically a Nat/Lean concern.

## Redundancy and duplication

The clearest redundancy is the unused `_hd0` hypothesis. The current proof obtains all required positivity from `hEq`, `hrVal`, `hc0`, and `hr0`, so `_hd0` appears removable from the theorem type. That observation is source-level only here; no Lean build is performed in this museum run.

The proof also names several intermediate equations (`hpow`, `hmul`, `hvalEq`, `hdValPos`, `hcVal`, `hsplit`). This is excellent for auditability, though some of them could be merged into longer `calc` blocks if concision were preferred.

## Optimization candidates

1. Test whether `_hd0` can be removed from the theorem statement. It is unused in the current proof, but this remains unverified without a build.
2. Generalize to a lemma of the form: if $v_p(r)=k$ and $cr=d^e$, then $v_p(c)\equiv-k\pmod e$. The present theorem is the special case $p=e=5$ and $k=1$.
3. Extract the Nat arithmetic transformation from `5 * t = c + 1` to `c = 4 + 5 * (t - 1)` so that valuation reasoning and truncated-subtraction bookkeeping are separated.
4. If the surrounding five-adic section can share the primality instance, repeated `Fact (Nat.Prime 5)` boilerplate can be reduced.

## Required Mathlib imports and import optimization

The generated standalone artifact is verified to use

```lean
import Mathlib
```

and contains this theorem under that umbrella import. Its manifest identifies the original module as `DkMath/FLT/Five/SignedFiveAdic.lean`, but that split source file is not present on `docs/flt5-theorem-museum`, so its exact import list could not be checked.

A minimized version would need the module providing `padicValNat` and `padicValNat.mul`, together with the import that provides the `omega` tactic. The exact minimal module names are **inferred, not verified** from the material available on this branch. Determining them exactly would require the split source or an import-reduction build in another worktree.

## Comparator challenge suitability

**High.**

A compact challenge can take

```lean
carrier * residual = distinguished ^ 5
padicValNat 5 residual = 1
```

and target

```lean
∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

Useful comparison variants include:

- the current `padicValNat.mul` plus Nat-arithmetic proof,
- a congruence-first proof,
- a proof through a generalized valuation-congruence lemma,
- a minimal-hypothesis version with `_hd0` removed.

The most informative metrics are transparency of nonzero assumptions, safety of Nat subtraction, generalizability, and dependence on specialized Mathlib API rather than raw line count.

## Next declaration to read

The next source declaration is

```lean
inductive SignedFiveAdicSource
    (u v w carrier residual distinguished : ℕ) : Prop
```

which records provenance: whether the common `carrier/residual/distinguished` triple came from the difference orientation or the sum orientation. Immediately after it, `SignedFiveAdicPacket` packages the present theorem's valuation shape together with the rest of the five-adic invariants.

Therefore the natural next item in dependency order is `DkMath.FLT.Five.SignedFiveAdicSource`.

## Sources and caveats

- The theorem body, the following `SignedFiveAdicSource` and `SignedFiveAdicPacket`, and the theorem's direct use inside `nonempty_signedFiveAdicPacket_of_normalForm` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.
- The standalone manifest names `DkMath/FLT/Five/SignedFiveAdic.lean` as the original source module.
- That split source file could not be fetched from the target branch, so the exact minimal import list remains unverified.
- No exact page correspondence for this theorem was confirmed in the existing Japanese/English PDFs, so no PDF-specific page claim is added by inference.

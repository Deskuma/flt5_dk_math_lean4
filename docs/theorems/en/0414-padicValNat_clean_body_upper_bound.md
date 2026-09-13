# 0414 `padicValNat_clean_body_upper_bound`

## Declaration kind

`theorem`

## Lean type

```lean
theorem padicValNat_clean_body_upper_bound
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) ≤ 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  by_contra hnot
  have htwo : 2 ≤ padicValNat q (g * GN5 g y) := by
    omega
  have hsq : q ^ 2 ∣ g * GN5 g y :=
    (@padicValNat_dvd_iff_le q (Fact.mk h.prime) (g * GN5 g y) 2 hBodyNe).mpr htwo
  exact h.not_sq_dvd_body hsq
```

This theorem proves that for a `CleanGN5Channel g y q`, the `q`-adic valuation of the full fifth-power body

```lean
g * GN5 g y
```

is at most one.

## Mathematical statement

In the canonical `CleanChannel.lean` source, `CleanGN5Channel g y q` is the structure

```lean
structure CleanGN5Channel (g y q : ℕ) : Prop where
  prime : Nat.Prime q
  dvd_GN5 : q ∣ GN5 g y
  not_dvd_gap : ¬ q ∣ g
  noLift : ¬ q ^ 2 ∣ GN5 g y
```

From it the development has already proved

```lean
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

The essential input for 0414 is the second statement. If

$$
v_q(g\,GN_5(g,y))\ge 2,
$$

then `padicValNat_dvd_iff_le` gives

$$
q^2\mid g\,GN_5(g,y).
$$

But a clean channel guarantees

$$
q^2\nmid g\,GN_5(g,y).
$$

Therefore

$$
v_q(g\,GN_5(g,y))<2.
$$

Since `padicValNat` takes values in the natural numbers, this is equivalent to

$$
v_q(g\,GN_5(g,y))\le1.
$$

The Lean conclusion is

```lean
padicValNat q (g * GN5 g y) ≤ 1
```

## Role in the full proof

Declaration 0413 `padicValNat_lower_bound_d5` established that if a prime `q` divides a positive natural number `x`, then

$$
v_q(x^5)\ge5.
$$

Declaration 0414 supplies the matching clean-body upper bound

$$
v_q(g\,GN_5(g,y))\le1.
$$

The canonical `Valuation.lean` source summarizes this local contradiction as

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

The next declaration, 0415 `padicValNat_clean_body_eq_one`, also uses `h.dvd_body` to obtain

$$
1\le v_q(g\,GN_5(g,y)),
$$

and combines that lower bound with 0414 to sharpen the result to

$$
v_q(g\,GN_5(g,y))=1.
$$

Then `counterexample_false_of_clean_GN5Channel_by_padicValNat` uses the FLT5 body identity

$$
(z-y)GN_5(z-y,y)=x^5
$$

to transport the fifth-power lower bound `≥ 5` and the clean-body exact value `= 1` to the same natural number and derive a contradiction.

Thus 0414 is the upper-bound lemma of the valuation proof route.

## Direct dependencies

### `CleanGN5Channel`

`CleanGN5Channel g y q` describes a clean prime channel in which `q` occurs in `GN5 g y` only to first order and does not divide the gap `g`.

The declarations used directly are

```lean
h.prime : Nat.Prime q
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

The theorem `h.not_sq_dvd_body` is itself proved from `not_dvd_gap` and `noLift`: because `q^2` is coprime to the gap, any square divisibility of the full body would have to lift into the GN5 factor, contradicting `noLift`.

Declaration 0414 does not repeat that proof. It consumes the already established clean-channel interface.

### `GN5`

`GN5 g y` is the homogeneous fifth cyclotomic quotient in gap coordinates `z=g+y`, satisfying

$$
(g+y)^5-y^5=g\,GN_5(g,y).
$$

The polynomial expansion is not used inside 0414; the theorem treats `g * GN5 g y` as the full body whose valuation is being bounded.

### `padicValNat_dvd_iff_le`

This Mathlib theorem is the central bridge.

For a nonzero natural number `n`, it conceptually relates

$$
q^k\mid n
\Longleftrightarrow
k\le v_q(n).
$$

Declaration 0414 uses the reverse direction `.mpr` to turn

```lean
2 ≤ padicValNat q (g * GN5 g y)
```

into

```lean
q ^ 2 ∣ g * GN5 g y
```

### `omega`

After negating the desired upper bound, `omega` converts

```lean
¬ padicValNat q (g * GN5 g y) ≤ 1
```

into

```lean
2 ≤ padicValNat q (g * GN5 g y)
```

using natural-number arithmetic.

## Proof flow

### 1. Install primality as a typeclass instance

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

This supplies the `[Fact (Nat.Prime q)]` expected by the relevant `padicValNat` API.

### 2. Prove that the full body is nonzero

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

If the body were zero, every natural number would divide it, so in particular

```lean
q ^ 2 ∣ 0
```

would hold. This contradicts `h.not_sq_dvd_body`.

Mathematically, nonzeroness is forced by the clean-channel condition; in Lean it must be produced explicitly because `padicValNat_dvd_iff_le` requires it as a side condition.

### 3. Negate the upper bound and obtain valuation at least two

```lean
by_contra hnot
have htwo : 2 ≤ padicValNat q (g * GN5 g y) := by
  omega
```

This is the discrete natural-number implication

$$
\neg(v\le1)\Longrightarrow2\le v.
$$

### 4. Convert the valuation lower bound back into square divisibility

```lean
have hsq : q ^ 2 ∣ g * GN5 g y :=
  (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 2 hBodyNe).mpr htwo
```

Thus

$$
2\le v_q(body)
$$

becomes

$$
q^2\mid body.
$$

### 5. Contradict the clean-channel invariant

```lean
exact h.not_sq_dvd_body hsq
```

The square divisibility is forbidden by the clean channel, so the contradiction closes the original upper-bound goal.

## Lean-specific processing

### 1. The `Fact` instance

On paper one simply uses the assumption that `q` is prime. Some Mathlib valuation lemmas instead expect primality through a typeclass argument.

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

only repackages the already available proof for instance search; it introduces no new mathematical assumption.

### 2. Extracting the nonzero side condition indirectly

To apply `padicValNat_dvd_iff_le` to the full body, Lean needs

```lean
g * GN5 g y ≠ 0.
```

Rather than proving the individual factors positive or nonzero, the source derives this immediately from the stronger invariant

```lean
¬ q ^ 2 ∣ g * GN5 g y.
```

This is an efficient proof-engineering choice.

### 3. `by_contra` and discreteness of `Nat`

Mathematically, the negation of `v ≤ 1` immediately gives `v ≥ 2`. Lean still needs an order-theoretic conversion.

Using `omega` avoids a manual chain through lemmas about `<`, `≤`, and successors.

### 4. Exposing implicit arguments with `@`

```lean
@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 2 hBodyNe
```

makes the implicit and instance arguments explicit and fixes the exact application shape.

The tradeoff is tighter coupling to the precise Mathlib theorem signature.

### 5. `.mpr`

The equivalence returned by `padicValNat_dvd_iff_le` is used in the direction

```lean
(k ≤ padicValNat q n) → q ^ k ∣ n
```

via `.mpr`.

This is a useful contrast with 0413, which used `.mp` on the same bridge theorem to convert divisibility into a valuation lower bound. The two declarations therefore use the same API in opposite directions.

## Redundancy and duplication

### Duplication between `letI` and `Fact.mk h.prime`

As in 0413, the proof first registers

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

and then explicitly passes

```lean
Fact.mk h.prime
```

to `padicValNat_dvd_iff_le`.

This is a small Lean-level duplication. It may nevertheless be intentional for robustness by fixing the instance argument explicitly.

### `hBodyNe` is repeated in 0415

The next theorem `padicValNat_clean_body_eq_one` contains exactly the same proof

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

so the nonzeroness argument is genuinely duplicated across adjacent valuation lemmas.

## Optimization candidates

### 1. Extract a clean-body nonzero lemma

Because 0414 and 0415 share the same argument, the clearest local refactoring is a helper such as

```lean
theorem CleanGN5Channel.body_ne
    (h : CleanGN5Channel g y q) :
    g * GN5 g y ≠ 0 := by
  ...
```

placed near the clean-channel API.

This would shorten both valuation lemmas and centralize the invariant-derived nonzeroness fact.

### 2. Let typeclass inference remove the explicit `Fact.mk h.prime`

After `letI`, it may be possible to invoke `padicValNat_dvd_iff_le` without explicitly constructing another `Fact` value.

Whether all arguments infer cleanly in the repository's pinned Mathlib version has not been checked with a Lean build, so this remains an optimization candidate rather than a confirmed rewrite.

### 3. Abstract the generic valuation upper-bound pattern

The mathematics of 0414 is not GN5-specific. It is an instance of the general principle

$$
\neg(q^{k+1}\mid n)
\Longrightarrow
v_q(n)\le k.
$$

A generic helper could remove repeated valuation/divisibility boilerplate.

Even then, retaining 0414 as a thin FLT5-specific wrapper would preserve readability of the dependency graph.

### 4. Replace `by_contra` plus `omega` with direct order lemmas

If reducing tactic dependencies is a goal, one can derive `2 ≤ v` explicitly from `¬ v ≤ 1` using natural-number order lemmas.

The current proof is already concise and transparent, so this is optional rather than necessary.

## Required Mathlib imports and import optimization candidates

The canonical standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The Mathlib functionality directly needed by 0414 includes at least

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- natural-number divisibility
- `omega`

The DkMath-side dependencies include at least

- `GN5`
- `CleanGN5Channel`
- `CleanGN5Channel.not_sq_dvd_body`

so there is substantial room to replace the umbrella `Mathlib` import with narrower imports. The main candidates are the Mathlib module providing the p-adic valuation API and the module providing the `omega` tactic.

However, the exact minimal module paths and transitive import closure for the pinned Mathlib version have not been verified by a Lean build in this run, so no exact minimal import list is asserted.

The standalone file is also a generated artifact whose source order includes `GN5.lean`, `CleanChannel.lean`, and `Valuation.lean`. The minimal imports for theorem 0414 alone should therefore be distinguished from the minimal imports for the entire `Valuation.lean` module.

## Suitability as a Comparator challenge

### Standalone challenge

Yes.

Although short, 0414 tests several distinct abilities:

1. read fields and derived theorems from `CleanGN5Channel`;
2. derive nonzeroness of the full body from `not_sq_dvd_body`;
3. convert failure of the upper bound into `2 ≤ valuation`;
4. apply `padicValNat_dvd_iff_le` in the correct direction;
5. contradict the clean-channel square-divisibility invariant.

Paired with 0413, it also tests whether a prover can use the same valuation bridge in opposite directions (`.mp` versus `.mpr`).

### Challenge-design caveat

If both `h.not_sq_dvd_body` and `padicValNat_dvd_iff_le` are named explicitly in the prompt, proof search becomes quite short.

A stronger challenge would provide only the `CleanGN5Channel` hypothesis and the target, requiring the system to discover both

- the existing full-body square non-divisibility API, and
- the appropriate Mathlib valuation/divisibility bridge.

If the benchmark is intended to compare proof synthesis rather than theorem-name retrieval, explicitly listing the permitted valuation lemmas may instead be preferable.

## Next declaration to read

The next declaration is 0415 `padicValNat_clean_body_eq_one`, also a `theorem`:

```lean
theorem padicValNat_clean_body_eq_one
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
  exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

It combines the upper bound from 0414,

$$
v_q(body)\le1,
$$

with the lower bound obtained from `q ∣ body`,

$$
1\le v_q(body),
$$

and uses antisymmetry to conclude

$$
v_q(body)=1.
$$

This completes the clean-body side of the valuation contradiction with an exact value.

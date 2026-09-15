# 0413 `padicValNat_lower_bound_d5`

## Declaration kind

`theorem`

## Lean type

```lean
theorem padicValNat_lower_bound_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hvalX : 1 ≤ padicValNat q x := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp (by simpa using hqx)
  have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by simp
  rw [hpow]
  omega
```

This theorem proves that if a prime `q` divides a positive natural number `x`, then the `q`-adic valuation of its fifth power `x^5` is at least five.

## Mathematical statement

The assumptions are

$$
0<x,
\qquad q\text{ is prime},
\qquad q\mid x.
$$

From `q ∣ x` one gets

$$
v_q(x)\ge 1.
$$

Using the valuation power law

$$
v_q(x^5)=5v_q(x),
$$

one obtains

$$
v_q(x^5)
=5v_q(x)
\ge 5.
$$

The Lean conclusion is

```lean
5 ≤ padicValNat q (x ^ 5)
```

Mathematically this is a basic local estimate, but in this development it is isolated as the lower-bound lemma needed by the later clean-channel contradiction: a complete fifth power carries local load at least five.

## Role in the full proof

By 0412 the unconditional golden zero-sector closure has been completed. Declaration 0413 enters `Valuation.lean`, where an independent `padicValNat` route reconstructs the same FLT5 contradiction.

The module description summarizes this valuation route as

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

Declaration 0413 supplies the first half:

$$
\text{complete fifth power}
\Longrightarrow
\text{local }q\text{-adic load}\ge5.
$$

The next theorem, `padicValNat_clean_body_upper_bound`, proves that the corresponding valuation on a clean channel is at most one. Then `padicValNat_clean_body_eq_one` sharpens this to exactly one. Finally `counterexample_false_of_clean_GN5Channel_by_padicValNat` transports both statements to the same quantity and derives the contradiction between `≥ 5` and `= 1`.

Thus 0413 is the lower-bound lemma for the valuation proof route.

## Direct dependencies

### `padicValNat`

This is Mathlib's natural-number `q`-adic valuation function.

The theorem compares

```lean
padicValNat q x
padicValNat q (x ^ 5)
```

### `Nat.Prime q`

```lean
hq : Nat.Prime q
```

provides primality of `q`.

The main `padicValNat` API is used through a typeclass assumption, so the proof begins with

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

which repackages the proposition proof as a local instance.

### `padicValNat_dvd_iff_le`

This is the first substantive bridge in the proof.

The source applies it explicitly as

```lean
(@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp
```

For positive `x`, it connects

$$
q^1\mid x
\Longleftrightarrow
1\le v_q(x).
$$

Since `hqx : q ∣ x` is equivalent to `q^1 ∣ x`, `simpa` yields

```lean
hvalX : 1 ≤ padicValNat q x
```

### Power law for `padicValNat`

The proof records

```lean
have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by simp
```

which is exactly

$$
v_q(x^5)=5v_q(x).
$$

### `omega`

The final natural-number arithmetic

```lean
5 ≤ 5 * padicValNat q x
```

is closed from `hvalX : 1 ≤ padicValNat q x` by `omega`.

## Proof flow

### 1. Install primality as an instance

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

This supplies the `[Fact (Nat.Prime q)]` expected by the relevant Mathlib valuation API.

### 2. Convert divisibility into a valuation lower bound

```lean
have hvalX : 1 ≤ padicValNat q x := by
  exact (@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp
    (by simpa using hqx)
```

From `hx : 0 < x`, Lean obtains

```lean
hx.ne' : x ≠ 0
```

for the nonzero side condition. The hypothesis `hqx : q ∣ x` is normalized to `q ^ 1 ∣ x`, and `padicValNat_dvd_iff_le` then produces

```lean
1 ≤ padicValNat q x.
```

### 3. Expand the valuation of the fifth power

```lean
have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by
  simp
```

This reduces the target from the fifth power itself to the valuation of the base `x`.

### 4. Finish with linear arithmetic

```lean
rw [hpow]
omega
```

The goal becomes

```lean
5 ≤ 5 * padicValNat q x
```

which follows immediately from `hvalX`.

## Lean-specific processing

### 1. Converting a proposition into a `Fact` instance

On paper, one simply uses the hypothesis that `q` is prime. In Lean, some Mathlib APIs ask for

```lean
[Fact (Nat.Prime q)]
```

as a typeclass argument.

Thus

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

is required. It adds no mathematical assumption; it only exposes the existing proof `hq` to instance search.

### 2. Exposing implicit arguments with `@`

```lean
@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne'
```

uses `@` to expose implicit arguments explicitly.

This makes the exact argument order stable and visible, but it also couples the proof more tightly to the precise Mathlib API signature.

### 3. `hx.ne'`

From

```lean
hx : 0 < x
```

Lean derives

```lean
hx.ne' : x ≠ 0
```

which supplies the nonzero hypothesis required by `padicValNat_dvd_iff_le`.

Thus positivity from the FLT5 setting naturally satisfies the valuation API's domain condition.

### 4. Normalizing `q^1` with `simpa`

The valuation bridge at exponent `1` speaks about `q ^ 1 ∣ x`, whereas the theorem hypothesis is `q ∣ x`.

```lean
by simpa using hqx
```

lets simplification discharge the identity `q ^ 1 = q`.

### 5. Obtaining the power formula by `simp`

The entire identity

```lean
padicValNat q (x ^ 5) = 5 * padicValNat q x
```

is solved by

```lean
by simp
```

using the registered simplification rule for powers of `padicValNat`.

### 6. `omega`

The last step is Presburger arithmetic over natural numbers, so `omega` is an appropriate tactic.

It is not discovering any new valuation fact; it merely multiplies the already established inequality `1 ≤ padicValNat q x` by five.

## Redundancy and duplication

### Duplication between `letI` and `Fact.mk hq`

The proof first registers

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

but then explicitly passes

```lean
(Fact.mk hq)
```

to `padicValNat_dvd_iff_le`.

Thus the same primality proof is packaged twice. This is a small Lean-level redundancy.

On the other hand, the explicit argument may have been chosen for robustness, because it fixes the theorem's typeclass argument directly rather than relying entirely on inference.

### The named intermediate `hpow`

The sequence

```lean
have hpow : ... := by simp
rw [hpow]
```

could possibly be compressed by simplifying the target directly.

However, naming `hpow` makes the mathematically decisive identity

$$
v_q(x^5)=5v_q(x)
$$

visible, which is valuable for review and exposition.

## Optimization candidates

### 1. Let typeclass inference simplify the bridge theorem call

After `letI`, it may be possible to apply `padicValNat_dvd_iff_le` without explicitly constructing `Fact.mk hq`.

Conceptually one could aim for a form such as

```lean
have hvalX : 1 ≤ padicValNat q x := by
  apply (padicValNat_dvd_iff_le ...).mp
  simpa using hqx
```

Whether all implicit arguments are inferred cleanly in the repository's pinned Mathlib version has not been checked by a Lean build, so this remains a candidate rather than a confirmed replacement.

### 2. Generalize from exponent five

The same argument suggests a generic result of the form

$$
q\mid x
\Longrightarrow
n\le v_q(x^n)
$$

for a suitable positive exponent `n`.

Even if a generic lemma is introduced, retaining the FLT5-specific theorem as a named corollary is useful because it keeps the dependency graph readable.

### 3. Replace `omega` by explicit monotonicity if desired

The final step only multiplies `hvalX` by five, so one could use monotonicity of multiplication instead of an arithmetic tactic.

The current `omega` proof is already short and clear, however, so there is no practical need to change it unless reducing tactic dependencies is an explicit goal.

## Required Mathlib imports and import optimization candidates

The standalone canonical source uses

```lean
import Mathlib
```

The Mathlib functionality directly used by 0413 includes at least

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- `omega`

so there is substantial room to narrow the umbrella `Mathlib` import.

The main candidates are the Mathlib module providing the p-adic valuation API and the module providing the `omega` tactic.

However, the exact minimal module paths and transitive import closure for the repository's pinned Mathlib version have not been verified by a Lean build, so no exact minimal import list is asserted here.

For `Valuation.lean` as a whole, later declarations also use DkMath-side objects such as `CleanGN5Channel`, `GN5`, `Body5`, and `CounterexamplePack`. Therefore the minimal imports for theorem 0413 alone should be distinguished from the minimal imports for the entire module.

## Suitability as a Comparator challenge

### Standalone challenge

Yes. Although short, 0413 tests several distinct abilities:

1. convert `Nat.Prime q` into a `Fact` instance;
2. translate divisibility `q ∣ x` into a lower bound for `padicValNat`;
3. apply the valuation power law to a fifth power;
4. close the remaining natural-number arithmetic.

This makes it more informative than a theorem solved entirely by one `ring` or one `simp` call.

### Challenge-design caveat

If `padicValNat_dvd_iff_le` is explicitly named in the prompt, the search difficulty becomes much lower.

A stronger Comparator task would provide

- the ordinary `padicValNat` environment,
- the theorem body as a hole,
- only the hypotheses `q ∣ x`, `0 < x`, and `Nat.Prime q`,

and require the system to discover the appropriate bridge theorem itself.

Conversely, if the goal is to compare proof synthesis rather than theorem-name retrieval, supplying the allowed valuation lemmas explicitly would make the benchmark fairer.

## Next declaration to read

The next declaration is

```lean
theorem padicValNat_clean_body_upper_bound
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) ≤ 1 := by
  ...
```

While 0413 establishes the fifth-power lower bound

$$
v_q(x^5)\ge5,
$$

the next theorem establishes the clean GN5 body upper bound

$$
v_q(g\,GN_5(g,y))\le1.
$$

Its key argument is that valuation at least two would imply

$$
q^2\mid g\,GN_5(g,y),
$$

contradicting `CleanGN5Channel.not_sq_dvd_body`.

This begins to place the two incompatible valuation bounds side by side.

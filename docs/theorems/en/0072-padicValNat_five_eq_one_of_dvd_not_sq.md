# 0072 — `padicValNat_five_eq_one_of_dvd_not_sq`

## Lean type

```lean
theorem padicValNat_five_eq_one_of_dvd_not_sq
    {n : ℕ} (h5 : 5 ∣ n) (h25 : ¬ 25 ∣ n) :
    padicValNat 5 n = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hnz : n ≠ 0 := by
    intro hn0
    apply h25
    simp [hn0]
  have hge : 1 ≤ padicValNat 5 n :=
    (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 1 hnz).mp (by simpa using h5)
  have hle : padicValNat 5 n ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ padicValNat 5 n := by omega
    have hsq : 5 ^ 2 ∣ n :=
      (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 2 hnz).mpr htwo
    exact h25 (by simpa using hsq)
  exact le_antisymm hle hge
```

## Mathematical statement

If a natural number $n$ is divisible by $5$ but not by $25$, then its $5$-adic valuation is exactly $1$.

$$
5\mid n,\qquad 25\nmid n
\Longrightarrow
v_5(n)=1.
$$

Here Lean's `padicValNat 5 n` represents the $5$-adic valuation on natural numbers.

## Role in the whole proof

Articles 0068–0071 progressively converted the residual's modulo-$25$ information into ordinary divisibility. This theorem is the endpoint of that chain:

$$
(residual : ZMod\ 25)=5
\Longrightarrow residual\bmod25=5
\Longrightarrow 5\mid residual
\quad\text{and}\quad
25\nmid residual
\Longrightarrow v_5(residual)=1.
$$

Thus it converts congruence arithmetic into an **exact valuation** statement.

Inside `nonempty_signedFiveAdicPacket_of_normalForm`, the difference orientation applies this theorem to `GN5 (w - v) v`, while the sum orientation applies it to `SumGN5 u v`. The resulting fact is stored in the packet as `residual_padicValNat`. Later layers therefore do not reopen the modulo-$25$ calculation; they consume the normalized invariant `v_5(residual)=1` directly.

The next theorem, `padicValNat_carrier_shape_of_mul_eq_fifth`, combines

$$
carrier\cdot residual=distinguished^5,
\qquad v_5(residual)=1
$$

to show that the carrier valuation has the form $4\pmod5$. The present theorem is therefore the junction from local residual information to the valuation shape of the carrier.

## Direct dependencies

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Nat.Prime 5`
- `Fact (Nat.Prime 5)`
- `le_antisymm`
- `omega`
- `simp`

The essential API lemma is `padicValNat_dvd_iff_le`, which for nonzero $n$ connects divisibility and valuation:

$$
p^k\mid n
\Longleftrightarrow
k\le v_p(n).
$$

## Proof flow

1. Install a local `Fact (Nat.Prime 5)` instance using `letI`.
2. Derive $n\neq0$ from `h25 : ¬ 25 ∣ n`; if $n=0$, then $25\mid0$, contradiction.
3. Use `h5 : 5 ∣ n` and `padicValNat_dvd_iff_le` to obtain
   $$
   1\le v_5(n).
   $$
4. For the opposite bound, assume $v_5(n)>1$. Since the valuation is a natural number,
   $$
   2\le v_5(n).
   $$
5. Apply `padicValNat_dvd_iff_le` again to get $5^2\mid n$, hence $25\mid n$, contradicting `h25`.
6. Therefore $v_5(n)\le1$.
7. Finish with `le_antisymm hle hge`.

## Lean-specific processing

### Injecting `Fact (Nat.Prime 5)`

`padicValNat_dvd_iff_le` requires primality through typeclass inference, so the proof installs

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

locally. Mathematically this is merely the observation that 5 is prime, but Lean must satisfy the API's typeclass requirement explicitly.

### Explicit arguments to `@padicValNat_dvd_iff_le`

The proof uses calls such as

```lean
@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 1 hnz
```

where `@` exposes implicit arguments. This is robust against elaboration ambiguity, but it also repeats the primality witness even after the local instance has already been installed.

### The nonzero hypothesis `hnz`

The valuation API treats zero separately, so the theorem must provide `hnz : n ≠ 0`. Here it is extracted economically from `25 ∤ n`.

### Use of `omega`

After `by_contra hnot`, `omega` is used only for the natural-number order step from `¬ v_5(n) ≤ 1` to `2 ≤ v_5(n)`. It is not automating the number-theoretic content itself.

## Redundancy and duplication

The most visible redundancy is the duplicated prime instance. The proof begins with

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

but both applications of `padicValNat_dvd_iff_le` still pass `Fact.mk (by decide)` explicitly.

The lower-bound and upper-bound arguments also use the same equivalence in opposite directions. This symmetry is easy to audit, though it leaves room for abstraction.

## Optimization candidates

The first candidate is to let typeclass inference shorten the calls. If the current Mathlib elaborator accepts it, the proof may be reducible conceptually toward a form such as

```lean
have hge : 1 ≤ padicValNat 5 n :=
  (padicValNat_dvd_iff_le hnz).mp (by simpa using h5)
```

The exact implicit-argument shape is Mathlib-version dependent, so this is a **build-required optimization candidate**, not a claim that the shorter form already compiles here.

A second candidate is a general reusable lemma for any prime $p$:

$$
p\mid n,\qquad p^2\nmid n
\Longrightarrow
v_p(n)=1.
$$

Then the FLT5-specific theorem could become a thin wrapper. Since this development uses only $p=5$ at this point, the current specialization has the advantage of auditability.

A third candidate is to state the second hypothesis as `¬ 5 ^ 2 ∣ n` from the beginning. The current `¬ 25 ∣ n` is friendlier to human readers, while `simpa` later normalizes $5^2=25$. This is a readability-versus-API-alignment tradeoff.

## Required Mathlib imports and import optimization

The generated standalone artifact on this branch uses `import Mathlib`, and its manifest identifies this theorem as originating from `DkMath/FLT/Five/SignedFiveAdic.lean`. However, the split source file itself is absent from this museum branch, so its exact original import list could not be checked directly.

At minimum, the proof needs facilities from the following areas:

- Mathlib's $p$-adic valuation API providing `padicValNat` and `padicValNat_dvd_iff_le`
- `Nat.Prime`
- `omega`
- standard `simp` and order lemmas

A narrower import than `Mathlib` is therefore very likely possible, but the exact minimal import is **unverified**. Import optimization should be tested in an environment containing the split source module, using `#check padicValNat_dvd_iff_le` and a Lean build.

## Correspondence with the existing PDFs

A concrete page in the existing Japanese or English PDF corresponding directly to this theorem could not be verified on this museum branch during this pass. No PDF-specific explanation or page number is therefore inferred. The repository's Lean source remains the mathematical and formal authority.

## Comparator challenge suitability

**Suitable.** The inputs and goal are short and mathematically transparent, yet a successful Lean proof requires the contestant to connect the valuation API, prime typeclass, nonzero side condition, and divisibility/valuation equivalence correctly.

A challenge can present the theorem unchanged and optionally allow `padicValNat_dvd_iff_le` as a hint. Useful comparison points are:

- handling of the prime instance
- derivation of $n\neq0$
- construction of lower and upper valuation bounds
- normalization of `25` versus `5 ^ 2`
- degree of dependence on `omega`

## Next theorem to read

The next declaration should be

```lean
theorem padicValNat_carrier_shape_of_mul_eq_fifth
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (_hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 5)
    (hrVal : padicValNat 5 residual = 1) :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

It consumes the exact residual valuation $1$ established here and uses valuation additivity on a fifth-power product to force the carrier valuation into the congruence class $4\pmod5$. This is where the local modulo-$25$ analysis joins the valuation obstruction for the entire fifth-power factorization.

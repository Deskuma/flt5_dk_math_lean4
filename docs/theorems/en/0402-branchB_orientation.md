# 0402 `CounterexamplePack.branchB_orientation`

## Declaration kind

`theorem`

## Lean type

```lean
theorem CounterexamplePack.branchB_orientation
    {x y z : ℕ} (p : CounterexamplePack x y z) :
    ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x := by
  by_cases hyGap : 5 ∣ z - y
  · right
    intro hxGap
    have hyz : y ≤ z := (right_lt_of_fermat5Equation p.hx p.hEq).le
    have hxz : x ≤ z := by
      have hEqSwap : Fermat5Equation y x z := by
        simpa [Fermat5Equation, Nat.add_comm] using p.hEq
      exact (right_lt_of_fermat5Equation p.hy hEqSwap).le
    have hbody : Body5 (z - y) y = x ^ 5 :=
      body5_eq_fifth_power_of_fermat hyz p.hEq
    have h5xPow : 5 ∣ x ^ 5 := by
      rw [← hbody]
      exact dvd_mul_of_dvd_left hyGap _
    have h5x : 5 ∣ x :=
      (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5xPow
    have h5z : 5 ∣ z := by
      rw [← Nat.sub_add_cancel hxz]
      exact dvd_add hxGap h5x
    have h5y : 5 ∣ y := by
      rcases h5z with ⟨m, hm⟩
      rcases hyGap with ⟨n, hn⟩
      use m - n
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega) h5x h5y) p.hxy
  · exact Or.inl hyGap
```

## Mathematical statement

`CounterexamplePack x y z` packages a primitive positive candidate counterexample to FLT5. In particular it carries

$$
x^5+y^5=z^5
$$

and

$$
\gcd(x,y)=1.
$$

The theorem states that the two gaps

$$
z-y,\qquad z-x
$$

cannot both be divisible by 5. Hence at least one of

$$
5\nmid(z-y)
$$

or

$$
5\nmid(z-x)
$$

must hold.

This is therefore an orientation-routing theorem: if the left gap `z - y` is clean, the original packet can be sent directly into Branch B; otherwise the swapped packet can use `z - x` as its clean gap.

## Role in the full proof

By the preceding declaration `signedGoldenZeroSectorExclusion_of_arithmetic`, the arithmetic zero-sector exclusion has already been lifted to the receiver `SignedGoldenZeroSectorExclusion`. To close all primitive FLT5 packets, however, one still needs a guaranteed gap orientation satisfying the non-divisibility hypothesis required by Branch B.

`branchB_orientation` supplies exactly that routing fact.

The later theorem `counterexamplePackRefuter_of_unitFifthPowerExclusion` consumes the result directly:

```lean
rcases p.branchB_orientation with hyGap | hxGap
· exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
· exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

Thus the theorem implements the proof-level map

$$
\text{primitive packet}
\longrightarrow
\text{one admissible Branch-B orientation}.
$$

## Direct dependencies

### `CounterexamplePack`

Through `p.hx`, `p.hy`, `p.hxy`, and `p.hEq`, the proof uses at least the following data:

- `p.hx : 0 < x`
- `p.hy : 0 < y`
- `p.hxy : Nat.Coprime x y`
- `p.hEq : Fermat5Equation x y z`

### `Fermat5Equation`

This represents

$$
x^5+y^5=z^5.
$$

The proof explicitly uses its symmetry in `x` and `y` via

```lean
simpa [Fermat5Equation, Nat.add_comm] using p.hEq
```

to obtain a swapped equation.

### `right_lt_of_fermat5Equation`

From positivity and the FLT5 equation, this gives the required inequalities against `z`. Here it is used to prove

```lean
hyz : y ≤ z
hxz : x ≤ z
```

so that natural-number subtraction can safely be reconstructed.

### `body5_eq_fifth_power_of_fermat`

This supplies

```lean
Body5 (z - y) y = x ^ 5
```

and therefore transports divisibility of the gap `z-y` into divisibility of `x^5`.

### `Nat.Prime.dvd_of_dvd_pow`

Since 5 is prime,

$$
5\mid x^5 \Longrightarrow 5\mid x.
$$

### `Nat.not_coprime_of_dvd_of_dvd`

At the end, common divisibility

$$
5\mid x,\qquad 5\mid y
$$

contradicts `Nat.Coprime x y`.

## Proof flow

### 1. Split on divisibility of `z-y`

```lean
by_cases hyGap : 5 ∣ z - y
```

If this is false, the left disjunct is immediate:

```lean
Or.inl hyGap
```

The interesting branch is `5 ∣ z-y`, where the theorem must prove

$$
5\nmid(z-x).
$$

### 2. Assume `5 ∣ z-x` for contradiction

```lean
intro hxGap
```

The rest of the proof shows that simultaneous divisibility of both gaps forces both primitive coordinates to be divisible by 5.

### 3. Establish the order facts needed by `Nat.sub`

From `right_lt_of_fermat5Equation`, the proof gets

$$
y\le z.
$$

For the `x` side, it swaps the equation to

$$
y^5+x^5=z^5
$$

using

```lean
have hEqSwap : Fermat5Equation y x z := by
  simpa [Fermat5Equation, Nat.add_comm] using p.hEq
```

and obtains

$$
x\le z.
$$

### 4. Transport `5 ∣ z-y` to `5 ∣ x^5`

The factorization lemma gives

```lean
have hbody : Body5 (z - y) y = x ^ 5 :=
  body5_eq_fifth_power_of_fermat hyz p.hEq
```

Because `Body5` visibly contains the gap factor, `hyGap` yields divisibility of the body and hence of `x^5`:

```lean
rw [← hbody]
exact dvd_mul_of_dvd_left hyGap _
```

### 5. Use primality to obtain `5 ∣ x`

```lean
have h5x : 5 ∣ x :=
  (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5xPow
```

This descends divisibility from the fifth power to its base.

### 6. Deduce `5 ∣ z`

Since `hxz : x ≤ z`, natural subtraction satisfies

$$
z=(z-x)+x.
$$

Both summands are divisible by 5, so

$$
5\mid z.
$$

Lean spells out the reconstruction as

```lean
rw [← Nat.sub_add_cancel hxz]
exact dvd_add hxGap h5x
```

### 7. Deduce `5 ∣ y`

Now both `z` and `z-y` are divisible by 5, so `y` is divisible by 5 as well.

The Lean proof opens the divisibility witnesses explicitly:

```lean
rcases h5z with ⟨m, hm⟩
rcases hyGap with ⟨n, hn⟩
use m - n
omega
```

This explicit witness construction is needed because subtraction is taking place in `ℕ`, where one cannot blindly use ring-style subtraction lemmas.

### 8. Contradict primitivity

Finally,

$$
5\mid x,\qquad 5\mid y,
$$

and $5>1$, so `x` and `y` cannot be coprime:

```lean
exact (Nat.not_coprime_of_dvd_of_dvd (by omega) h5x h5y) p.hxy
```

This contradiction establishes `¬ 5 ∣ z-x`.

## Lean-specific details

### Natural-number subtraction

The main Lean-specific issue is `Nat.sub`. On paper one freely writes

$$
z=(z-x)+x
$$

or reconstructs `y` from `z` and `z-y`. In Lean, `Nat.sub` is truncated subtraction, so the inequalities `x ≤ z` and `y ≤ z` must be available explicitly.

This makes `right_lt_of_fermat5Equation` more than a cosmetic order lemma: it is required to justify the arithmetic transport through gaps.

### Swapping `x` and `y`

Instead of rebuilding the entire packet, the proof swaps only the equation:

```lean
simpa [Fermat5Equation, Nat.add_comm]
```

and reuses the same order theorem.

### Concrete primality of 5

```lean
(by norm_num : Nat.Prime 5)
```

closes the primality obligation locally, avoiding an extra named lemma.

### `omega`

`omega` handles the witness arithmetic for `5 ∣ y` and the simple linear natural-number fact `5 > 1`. It is especially convenient because the witness contains natural subtraction.

## Redundancy and repeated structure

The proof is already short and has little redundancy. Two pieces could nevertheless be abstracted if they recur elsewhere:

1. the equation-swap boilerplate needed to apply `right_lt_of_fermat5Equation` to both coordinates;
2. the natural-number divisibility step recovering `k ∣ y` from `k ∣ z`, `k ∣ z-y`, and `y ≤ z`.

The second could be packaged as a general lemma of the shape

```lean
k ∣ z → k ∣ z - y → y ≤ z → k ∣ y
```

although for a single use the present local argument is arguably easier to audit.

## Optimization candidates

### Factor out simultaneous gap divisibility

The mathematical core is

$$
5\mid(z-y)\land5\mid(z-x)
\Longrightarrow
5\mid x\land5\mid y.
$$

Factoring this into an internal lemma would make `branchB_orientation` itself read almost entirely as “simultaneous divisibility contradicts coprimality.”

The current proof is still sufficiently compact that this is optional rather than necessary.

### Symmetric order API

Because `right_lt_of_fermat5Equation` is oriented, the proof must swap the equation before obtaining `x ≤ z`. If this pattern occurs repeatedly, a lemma returning both inequalities at once could reduce boilerplate, for example a `both_lt_right_of_fermat5Equation`-style API.

### Simplify the proof of `h5y`

There may already be a Mathlib lemma that derives divisibility across natural-number subtraction under an order hypothesis. If so, the explicit witness plus `omega` could be replaced by a more declarative step. This was not verified while preparing this document, so it remains a possible optimization rather than a confirmed replacement.

## Required Mathlib imports

The authoritative standalone file `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The theorem directly relies on Mathlib support for at least:

- `Nat.Prime` and `dvd_of_dvd_pow`
- `Nat.Coprime` and `Nat.not_coprime_of_dvd_of_dvd`
- natural-number divisibility
- `Nat.sub_add_cancel`
- `norm_num`
- `omega`
- standard rewriting and elimination tactics such as `simpa`, `rw`, and `rcases`

Local FLT5 dependencies include the modules defining or proving `CounterexamplePack`, `Fermat5Equation`, `right_lt_of_fermat5Equation`, `Body5`, and `body5_eq_fifth_power_of_fermat`.

### Import minimization

It is very likely that `import Mathlib` is broader than necessary for this isolated theorem. A minimized environment would mainly need Nat prime/gcd/divisibility support, the relevant tactics, and the preceding local FLT5 modules.

Because no Lean build is performed in this documentation run, the exact minimal import set has not been validated. Therefore the claim that `Mathlib` can be reduced is reasonable, but a precise replacement import list remains unverified.

## Comparator challenge suitability

**Yes; this is a good challenge candidate.**

The theorem combines several small but proof-engineering-sensitive ingredients:

- the concrete prime 5;
- natural-number subtraction;
- divisibility;
- coprimality;
- prime divisibility descending from a fifth power;
- symmetry of the Fermat equation.

For a compact Comparator challenge, one could avoid importing the full `CounterexamplePack` structure and expose only:

- positivity of `x` and `y`;
- `Nat.Coprime x y`;
- the equation `x^5 + y^5 = z^5`;
- the body-factorization lemma;
- the order facts or the lemma producing them.

Then the target

```lean
¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x
```

would test whether the prover can robustly manage divisibility together with truncated natural subtraction.

## Next declaration to read

The next declaration is **0403 `CounterexamplePackRefuter`**.

Its declaration kind is not `theorem` but **`abbrev`**:

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

Declaration 0402 proves that every primitive packet admits one of the two Branch-B orientations. Declaration 0403 then names the receiver interface asserting that every primitive packet is impossible.

The following theorem, `counterexamplePackRefuter_of_unitFifthPowerExclusion`, immediately consumes the orientation split from 0402 and proves

$$
\text{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\text{CounterexamplePackRefuter}.
$$

Therefore 0403 is the correct next declaration in dependency order.
# 0406 `exists_counterexamplePack_of_positive_fermat5`

## Declaration kind

`theorem`

## Lean type

```lean
/-- Arbitrary positive solutions can be reduced to a primitive counterexample packet. -/
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z' := by
  let d := Nat.gcd x y
  let x' := x / d
  let y' := y / d
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_left y hx
  have hdx : d ∣ x := Nat.gcd_dvd_left x y
  have hdy : d ∣ y := Nat.gcd_dvd_right x y
  have hd5z5 : d ^ 5 ∣ z ^ 5 := by
    have hd5x5 : d ^ 5 ∣ x ^ 5 := pow_dvd_pow_of_dvd hdx 5
    have hd5y5 : d ^ 5 ∣ y ^ 5 := pow_dvd_pow_of_dvd hdy 5
    rw [← hEq]
    exact dvd_add hd5x5 hd5y5
  have hdz : d ∣ z := by
    have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd (a := d ^ 5) (b := z)
      (by decide : 5 ≠ 0)).mp hd5z5
    simpa using hroot
  let z' := z / d
  have hxEq : d * x' = x := Nat.mul_div_cancel' hdx
  have hyEq : d * y' = y := Nat.mul_div_cancel' hdy
  have hzEq : d * z' = z := Nat.mul_div_cancel' hdz
  have hxPos : 0 < x' := Nat.div_pos (Nat.le_of_dvd hx hdx) hdPos
  have hyPos : 0 < y' := Nat.div_pos (Nat.le_of_dvd hy hdy) hdPos
  have hzPos : 0 < z' := Nat.div_pos (Nat.le_of_dvd hz hdz) hdPos
  have hcop : Nat.Coprime x' y' := by
    exact Nat.coprime_div_gcd_div_gcd hdPos
  have hEq' : Fermat5Equation x' y' z' := by
    have hscaled : d ^ 5 * (x' ^ 5 + y' ^ 5) = d ^ 5 * z' ^ 5 := by
      calc
        d ^ 5 * (x' ^ 5 + y' ^ 5) = (d * x') ^ 5 + (d * y') ^ 5 := by ring
        _ = x ^ 5 + y ^ 5 := by rw [hxEq, hyEq]
        _ = z ^ 5 := hEq
        _ = (d * z') ^ 5 := by rw [hzEq]
        _ = d ^ 5 * z' ^ 5 := by ring
    unfold Fermat5Equation
    exact Nat.mul_left_cancel (pow_pos hdPos 5) hscaled
  exact ⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

## Mathematical statement and meaning

This theorem proves the standard primitive normalization step for exponent five: if there is a positive natural-number solution

$$
x^5+y^5=z^5,
\qquad x>0,\ y>0,\ z>0,
$$

then there is also a positive solution whose two left coordinates are coprime, packaged as a `CounterexamplePack`.

Set

$$
d=\gcd(x,y),
\qquad x'=\frac{x}{d},
\qquad y'=\frac{y}{d}.
$$

By construction,

$$
\gcd(x',y')=1.
$$

The essential extra step is to show that the same $d$ also divides $z$. Since

$$
d\mid x,
\qquad d\mid y,
$$

we have

$$
d^5\mid x^5,
\qquad d^5\mid y^5,
$$

and therefore, using the Fermat equation,

$$
d^5\mid x^5+y^5=z^5.
$$

Lean then uses `Nat.dvd_pow_iff_ceilRoot_dvd` to descend from fifth-power divisibility to

$$
d\mid z.
$$

Thus we may also define

$$
z'=\frac{z}{d}.
$$

Substituting

$$
x=dx',\qquad y=dy',\qquad z=dz'
$$

into the original equation gives

$$
d^5(x'^5+y'^5)=d^5z'^5.
$$

Because $d>0$, hence $d^5>0$, natural-number left cancellation yields

$$
x'^5+y'^5=z'^5.
$$

Therefore every positive solution reduces to a primitive one through

$$
(x,y,z)
\longmapsto
\left(\frac{x}{d},\frac{y}{d},\frac{z}{d}\right).
$$

## Role in the full proof

By 0405 the development has reached a refuter for primitive packets:

```lean
CounterexamplePack x y z → False
```

The final FLT5 target, however, concerns arbitrary positive natural numbers and assumes no coprimality. 0406 is the normalization bridge between these two levels.

Its logical flow is

$$
\begin{aligned}
&x^5+y^5=z^5,
\quad x,y,z>0\\
&\qquad\Downarrow\quad d=\gcd(x,y)\\
&x=dx',\quad y=dy',\quad z=dz'\\
&\qquad\Downarrow\\
&x'^5+y'^5=z'^5,
\quad x',y',z'>0,
\quad \gcd(x',y')=1\\
&\qquad\Downarrow\\
&\mathrm{CounterexamplePack}(x',y',z').
\end{aligned}
$$

This theorem is independent of the golden-integer, unit-class, and zero-sector descent machinery. It belongs to the elementary natural-number normalization layer at the entrance of the proof and connects arbitrary positive solutions to the primitive obstruction proved later.

## Direct dependencies

### `Fermat5Equation`

The equation represented conceptually by

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

It is used once to transfer divisibility to $z^5$ and again to reconstruct the normalized equation.

### `CounterexamplePack`

The structure produced by the theorem.

From the final constructor term, the relevant fields here are at least

- `0 < x'`
- `0 < y'`
- `0 < z'`
- `Nat.Coprime x' y'`
- `Fermat5Equation x' y' z'`

and the theorem finishes with

```lean
⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

### `Nat.gcd_pos_of_pos_left`

Obtains

$$
0<\gcd(x,y)
$$

from $x>0$.

This positivity is needed both for positivity of the quotients and for cancellation of $d^5$.

### `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`

Provide

$$
d\mid x,
\qquad d\mid y.
$$

### `pow_dvd_pow_of_dvd`

Lifts divisibility to fifth powers:

$$
d\mid x
\Longrightarrow
d^5\mid x^5.
$$

The same is used for $y$.

### `Nat.dvd_pow_iff_ceilRoot_dvd`

This is the most distinctive Mathlib dependency in the proof.

From

```lean
hd5z5 : d ^ 5 ∣ z ^ 5
```

and the fact that $5\neq0$, it recovers

```lean
hdz : d ∣ z
```

Mathematically this is the familiar comparison of prime exponents in $d^5$ and $z^5$; the Lean implementation reuses a general theorem formulated through `ceilRoot`.

### `Nat.mul_div_cancel'`

Turns divisibility into exact reconstruction equations such as

$$
d\left(\frac{x}{d}\right)=x.
$$

It is used for all three coordinates.

### `Nat.div_pos`

Proves positivity of $x'$, $y'$, and $z'$.

`Nat.le_of_dvd` supplies $d\le x,y,z$, and `hdPos` supplies positivity of the divisor.

### `Nat.coprime_div_gcd_div_gcd`

Provides directly

$$
\gcd\left(\frac{x}{d},\frac{y}{d}\right)=1.
$$

### `Nat.mul_left_cancel`

Cancels the common factor $d^5$ from

$$
d^5A=d^5B.
$$

The proof term explicitly supplies `pow_pos hdPos 5` to justify that the common factor is positive.

## Proof and construction flow

### 1. Define the gcd and normalized left coordinates

```lean
let d := Nat.gcd x y
let x' := x / d
let y' := y / d
```

### 2. Establish positivity and basic divisibility of the gcd

```lean
have hdPos : 0 < d := Nat.gcd_pos_of_pos_left y hx
have hdx : d ∣ x := Nat.gcd_dvd_left x y
have hdy : d ∣ y := Nat.gcd_dvd_right x y
```

### 3. Prove $d^5\mid z^5$

```lean
have hd5x5 : d ^ 5 ∣ x ^ 5 := pow_dvd_pow_of_dvd hdx 5
have hd5y5 : d ^ 5 ∣ y ^ 5 := pow_dvd_pow_of_dvd hdy 5
rw [← hEq]
exact dvd_add hd5x5 hd5y5
```

The Fermat equation is rewritten backwards so the divisibility goal on $z^5$ becomes one on $x^5+y^5$.

### 4. Recover $d\mid z$

```lean
have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd ...).mp hd5z5
simpa using hroot
```

This is the technical center of the normalization.

### 5. Define $z'$ and reconstruct all three original coordinates

```lean
let z' := z / d
have hxEq : d * x' = x := Nat.mul_div_cancel' hdx
have hyEq : d * y' = y := Nat.mul_div_cancel' hdy
have hzEq : d * z' = z := Nat.mul_div_cancel' hdz
```

### 6. Prove positivity and coprimality of the normalized coordinates

```lean
have hxPos : 0 < x' := ...
have hyPos : 0 < y' := ...
have hzPos : 0 < z' := ...
have hcop : Nat.Coprime x' y' := ...
```

### 7. Prove the normalized Fermat equation

First the proof constructs the scaled equality

```lean
d ^ 5 * (x' ^ 5 + y' ^ 5) = d ^ 5 * z' ^ 5
```

using a `calc` chain and `ring`.

Then it cancels the common factor:

```lean
unfold Fermat5Equation
exact Nat.mul_left_cancel (pow_pos hdPos 5) hscaled
```

### 8. Build the `CounterexamplePack`

```lean
exact ⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

## Lean-specific processing

### Local `let` bindings

The proof uses `let` for `d`, `x'`, `y'`, and `z'`. This keeps the mathematical quotient notation readable while still allowing later arithmetic lemmas and `ring` to unfold the local definitions as required.

### `rw [← hEq]`

The equation is deliberately rewritten in the reverse direction to replace the divisibility target `z ^ 5` by `x ^ 5 + y ^ 5`.

### `by decide : 5 ≠ 0`

`Nat.dvd_pow_iff_ceilRoot_dvd` requires a proof that the exponent is nonzero. Since the exponent is the concrete numeral 5, Lean discharges this by decision procedure.

### `simpa using hroot`

The general root-divisibility theorem produces a conclusion whose computed normal form is the desired `d ∣ z`. `simpa` absorbs the representational details of the `ceilRoot` API.

### `ring`

The first and last steps of `hscaled` normalize semiring identities such as

$$
d^5x'^5=(dx')^5.
$$

No number-theoretic reasoning is hidden in these `ring` calls; they are purely algebraic normalization.

### `Nat.mul_left_cancel (pow_pos hdPos 5)`

Natural-number cancellation requires the positivity/nonzeroness of the left factor explicitly. Lean receives this as the proof term `pow_pos hdPos 5`.

## Redundancy and duplication

There is no major logical duplication. The normalization stages are deliberately explicit.

The main repeated patterns are the three reconstruction equalities

```lean
hxEq / hyEq / hzEq
```

and the three positivity proofs

```lean
hxPos / hyPos / hzPos.
```

A local helper could reduce these repetitions, but the current form makes the role of each coordinate transparent and is arguably preferable for an explanatory museum document.

The scaled equality `hscaled` also performs a reusable operation: preservation of the Fermat-five equation under removal of a common factor. If such a lemma existed separately, this theorem could become shorter.

## Optimization candidates

### Extract gcd normalization as a reusable lemma

One could isolate a theorem of the schematic form

```lean
Fermat5Equation x y z →
d = Nat.gcd x y →
∃ x' y' z',
  x = d * x' ∧ y = d * y' ∧ z = d * z' ∧
  Nat.Coprime x' y' ∧ Fermat5Equation x' y' z'
```

and leave 0406 mainly as packaging into `CounterexamplePack`.

### Hide the root-divisibility API behind an exponent-five helper

Instead of exposing `Nat.dvd_pow_iff_ceilRoot_dvd` directly in the FLT5 proof, one could prove

```lean
lemma dvd_of_pow_five_dvd_pow_five {d z : ℕ} :
    d ^ 5 ∣ z ^ 5 → d ∣ z := ...
```

once and use the simpler interface thereafter.

### Package scaling and cancellation

A suitable lemma expressing preservation of `Fermat5Equation` under a common nonzero scaling factor could replace the `hscaled` calculation.

These abstractions would shorten the theorem, but 0406 is a single normalization boundary and the present proof is local and auditable. Over-abstraction could make dependency tracing harder.

## Required Mathlib imports and import optimization

The standalone repository source uses `import Mathlib`, so the only import that is directly verified for this declaration is `Mathlib`.

The Mathlib facilities used directly by 0406 are chiefly

- natural-number `gcd`, `Coprime`, division, and divisibility lemmas,
- `Nat.dvd_pow_iff_ceilRoot_dvd`,
- power/divisibility lemmas,
- the `ring` tactic,
- `decide` for the concrete fact $5\neq0$.

It is therefore likely possible to replace the broad `Mathlib` import with a small collection of modules covering natural-number gcd/divisibility/roots together with `ring`. However, the exact minimal module set is **not verified** in the repository source inspected here, and no Lean build is performed in this documentation run.

In particular, identifying the precise defining module of `Nat.dvd_pow_iff_ceilRoot_dvd` would require a separate Mathlib dependency inspection.

## Suitability as a Comparator challenge

**Good candidate.**

Unlike the immediately preceding receiver-composition theorems, 0406 contains substantial constructive arithmetic. A challenge can retain

- `Fermat5Equation`,
- `CounterexamplePack`,
- the standard Mathlib natural-number API,

and replace the proof with a hole. This tests whether a model can

1. discover the gcd normalization,
2. obtain $d\mid z$ from $d^5\mid z^5$ in Lean,
3. prove positivity and coprimality of the quotients,
4. reconstruct the normalized equation through scaling and cancellation,
5. assemble the resulting structure.

The use of `Nat.dvd_pow_iff_ceilRoot_dvd` is especially useful for testing Mathlib API discovery.

For a more mathematically focused challenge, one could supply the helper

```lean
d ^ 5 ∣ z ^ 5 → d ∣ z
```

and ask the model to solve the remaining normalization problem.

Overall this is a stronger Comparator challenge than 0404 or 0405 because it combines arithmetic reasoning, library search, algebraic normalization, and structure construction.

## Next declaration to read

The next declaration is **0407 `PositiveFermat5Refuter`**.

Its declaration kind is `abbrev`:

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0406 establishes

$$
\text{positive solution}
\Longrightarrow
\text{primitive CounterexamplePack},
$$

and 0407 gives a name to the receiver type expressing that every positive solution is impossible.

The following theorem `positiveFermat5Refuter_of_counterexamplePackRefuter` then consumes 0406 directly and closes

$$
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter}.
$$

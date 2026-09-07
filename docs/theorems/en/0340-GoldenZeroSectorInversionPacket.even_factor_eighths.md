# 0340 — `GoldenZeroSectorInversionPacket.even_factor_eighths`

## Declaration kind

This declaration is a **`theorem`**.

```lean
/-- After removing eight, the two even-branch factors have opposite parity. -/
theorem GoldenZeroSectorInversionPacket.even_factor_eighths
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 8 * A1 ∧ p.source.B0 = 8 * B1 ∧
      ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)) := by
  rcases p.eight_dvd_factors hc with ⟨h8A, h8B⟩
  rcases h8A with ⟨A1, hA⟩
  rcases h8B with ⟨B1, hB⟩
  have hdiff : B1 = A1 + p.source.d ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
    calc
      8 * B1 = p.source.B0 := hB.symm
      _ = p.source.A0 + 8 * p.source.d ^ 5 := p.factor_difference
      _ = 8 * (A1 + p.source.d ^ 5) := by rw [hA]; ring
  have hdOdd : Odd (p.source.d ^ 5) := p.source.d_odd.pow
  rcases Nat.even_or_odd A1 with hAeven | hAodd
  · have hBodd : Odd B1 := by rw [hdiff]; exact hAeven.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inr ⟨hAeven, hBodd⟩⟩
  · have hBeven : Even B1 := by rw [hdiff]; exact hAodd.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inl ⟨hAodd, hBeven⟩⟩
```

## Lean type

The theorem has type

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
∃ A1 B1 : ℕ,
  p.source.A0 = 8 * A1 ∧
  p.source.B0 = 8 * B1 ∧
  ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1))
```

Thus, in the even-`c` branch, the divisibilities $8\mid A_0$ and $8\mid B_0$ established in 0339 are turned into explicit quotients `A1` and `B1`, together with the stronger conclusion that those two quotients always have opposite parity.

## Mathematical statement

From 0339 one may write

$$
A_0=8A_1,
\qquad
B_0=8B_1.
$$

The inversion packet also supplies the exact difference relation

$$
B_0=A_0+8d^5.
$$

Substituting the two quotient equations and cancelling the positive common factor 8 gives

$$
B_1=A_1+d^5.
$$

By `p.source.d_odd`, the number $d$ is odd, hence so is $d^5$. Therefore $A_1$ and $B_1=A_1+d^5$ must have opposite parity. Consequently,

$$
(\operatorname{Odd}(A_1)\land\operatorname{Even}(B_1))
\lor
(\operatorname{Even}(A_1)\land\operatorname{Odd}(B_1))
$$

holds.

## Role in the overall FLT5 proof

This theorem is the **branching point that splits the even-`c` case into the two exact factorization branches**.

The preceding theorem, 0339 `GoldenZeroSectorInversionPacket.eight_dvd_factors`, only shows that both `A0` and `B0` contain a factor 8. The present theorem removes that common factor and enriches the resulting quotients with parity information.

That opposite parity is consumed immediately by `nonempty_even_factorData`:

- if `A1` is odd and `B1` is even, an additional factor 2 is extracted from the right-hand quotient;
- if `A1` is even and `B1` is odd, an additional factor 2 is extracted from the left-hand quotient.

These two alternatives eventually become the constructors `GoldenZeroSectorFactorData.evenLeftLow` and `.evenRightLow`.

The proof flow is

```text
c even
  │
  ▼
8 ∣ A0, 8 ∣ B0
  │
  ▼
A0 = 8*A1, B0 = 8*B1
  │
  ▼
B1 = A1 + d^5
  │
  ▼
d^5 odd
  │
  ▼
A1, B1 have opposite parity
  │
  ├── A1 odd,  B1 even
  └── A1 even, B1 odd
```

## Direct dependencies

### `GoldenZeroSectorInversionPacket.eight_dvd_factors`

The theorem from 0339. Under `Even p.source.c`, it provides

```lean
8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0
```

and the witnesses of these divisibilities become `A1` and `B1`.

### `p.factor_difference`

This gives the exact difference relation

```lean
p.source.B0 = p.source.A0 + 8 * p.source.d ^ 5
```

and is the arithmetic core used to derive

```lean
B1 = A1 + p.source.d ^ 5.
```

### `p.source.d_odd`

This supplies oddness of `d`. Applying `.pow` gives oddness of the fifth power.

### `Nat.mul_left_cancel`

Used to cancel the common factor 8 after the quotient equations are substituted into `factor_difference`.

### `Nat.even_or_odd`

Provides the exhaustive parity split for `A1`. Each branch then uniquely determines the parity of `B1`.

### `Even.add_odd`, `Odd.add_odd`

These parity lemmas establish the parity of `B1 = A1 + d^5` in the two cases.

### `ring`

Closes the polynomial normalization

```lean
8 * A1 + 8 * d^5 = 8 * (A1 + d^5).
```

## Proof/construction flow

### 1. Turn divisibility by 8 into quotient witnesses

```lean
rcases p.eight_dvd_factors hc with ⟨h8A, h8B⟩
rcases h8A with ⟨A1, hA⟩
rcases h8B with ⟨B1, hB⟩
```

This yields

```lean
hA : p.source.A0 = 8 * A1
hB : p.source.B0 = 8 * B1.
```

### 2. Derive the quotient difference equation

Substitute `hA` and `hB` into `p.factor_difference`, obtaining

$$
8B_1=8(A_1+d^5),
$$

then cancel 8 with `Nat.mul_left_cancel` to get

$$
B_1=A_1+d^5.
$$

### 3. Establish oddness of `d^5`

```lean
have hdOdd : Odd (p.source.d ^ 5) := p.source.d_odd.pow
```

uses preservation of oddness under powers.

### 4. Split on the parity of `A1`

```lean
rcases Nat.even_or_odd A1 with hAeven | hAodd
```

performs an exhaustive two-way split.

### 5. Derive the opposite parity of `B1`

If `A1` is even, then `B1=A1+d^5` is odd. If `A1` is odd, then `B1` is even.

### 6. Return the existential packet

The same witnesses `A1`, `B1`, and their factor equations are returned together with the appropriate disjunct proving opposite parity.

## Lean-specific processing

### Expanding divisibility witnesses directly

Because `a ∣ b` is represented by an existential witness, `rcases h8A with ⟨A1, hA⟩` turns the divisibility proof into a concrete quotient that can immediately participate in later equations.

### Explicit cancellation side condition

```lean
apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
```

makes the positivity of the cancellable factor explicit in the natural-number setting.

### Parity as proof-carrying branching

`Nat.even_or_odd A1` returns proof objects, not just a Boolean test. Those proofs are passed directly to parity lemmas such as `.add_odd`.

### Transport through exact equality

The proof of the parity of `B1` starts by rewriting with `hdiff`. Thus the arithmetic normalization and the parity reasoning remain cleanly separated.

## Redundancy and duplication

The two parity branches are mirror images. The only substantive difference is whether the resulting proof for `B1` is `Odd B1` or `Even B1`.

That duplication is nevertheless structurally appropriate because the target itself is a disjunction

```lean
(Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1).
```

Likewise, retaining `hA` and `hB` separately is not redundant: both equations are returned unchanged in the final existential package.

## Optimization candidates

1. A reusable lemma saying that `B = A + k` with `Odd k` forces `A` and `B` to have opposite parity could compress the final case split. This would be worthwhile if the same pattern occurs elsewhere.

2. The current `Nat.mul_left_cancel` plus `calc` proof of the quotient equation is explicit and audit-friendly. Replacing it with heavier automation would not necessarily improve the proof.

3. One could return a dedicated branch label instead of a disjunction, but the present existential-plus-disjunction form is a useful boundary between the arithmetic layer and the later `GoldenZeroSectorFactorData` construction layer.

4. `ring` could in principle be replaced by direct distributivity rewrites, but for this single normalization the current form is concise and clear.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

for the whole artifact.

The main facilities directly used by this theorem are:

- natural-number divisibility and multiplication cancellation;
- `Even` / `Odd`;
- `Nat.even_or_odd`;
- parity lemmas for addition and powers;
- `norm_num`;
- `ring`.

A substantially smaller import set than all of `Mathlib` is therefore likely possible. However, this museum task does not run Lean builds, so the exact minimal import combination has not been verified and no precise module list is asserted here.

The standalone manifest identifies the originating source module as `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean`.

## Comparator challenge suitability

**Suitable.**

A clean standalone challenge is:

> Let natural numbers $A_0,B_0,d,A_1,B_1$ satisfy $A_0=8A_1$, $B_0=8B_1$, and $B_0=A_0+8d^5$. If $d$ is odd, prove that $A_1$ and $B_1$ have opposite parity.

This strips away nearly all FLT5-specific golden-order machinery and leaves a small, checkable arithmetic/parity problem.

A Comparator challenge can compare:

- how the factor 8 is cancelled;
- how `Odd (d^5)` is obtained;
- whether parity is handled by explicit case splitting or by a reusable general lemma.

## Next declaration to read

The next declaration is

```lean
private theorem nonempty_even_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
```

It consumes the opposite-parity conclusion proved here, splits the even branch into

- `A1` odd / `B1` even,
- `A1` even / `B1` odd,

extracts one additional factor 2 from the even quotient, and then applies coprime fifth-power splitting to construct either `GoldenZeroSectorFactorData.evenLeftLow` or `.evenRightLow`.

Thus 0340 is the parity splitter that connects the coarse two-adic statement of 0339 with the exact fifth-power certificate construction that follows.

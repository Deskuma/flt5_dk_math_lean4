# 0277 — `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`

## Declaration kind

This declaration is a **`theorem`**.

In the zero sector of `SignedGoldenRamifierStrippedPacket`, it proves that the quartic factor `goldenFifthSndFactor` appearing in the second coordinate of a fifth power is not divisible by 5.

## Lean type

```lean
/-- The zero-sector quartic factor is not divisible by five. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  apply p.zeroSector_five_not_dvd_gamma_norm hbeta
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

Writing `gamma = (r,s)` and

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
N(\gamma)=\operatorname{goldenNorm}(\gamma),
$$

the statement is

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
5\nmid H(r,s).
$$

## Mathematical meaning

The preceding theorem 0276 gives

$$
5\mid\bigl(H(r,s)-N(\gamma)^2\bigr),
$$

that is,

$$
H(r,s)\equiv N(\gamma)^2\pmod 5.
$$

On the other hand, 0274 `zeroSector_five_not_dvd_gamma_norm` guarantees in the zero sector that

$$
5\nmid N(\gamma).
$$

Suppose, for contradiction, that

$$
5\mid H(r,s).
$$

Subtracting the divisibility relation from 0276 gives

$$
5\mid N(\gamma)^2.
$$

Since 5 is prime,

$$
5\mid N(\gamma)
$$

follows, contradicting 0274.

Thus this theorem transfers an already established five-adic exclusion on the norm side to the quartic-factor side.

## Role in the full proof

Theorem 0275 established the exact signed zero-sector coordinate equation

$$
s\,H(r,s)=-5^6a^{10}.
$$

Later the proof moves this equation to natural-number absolute values and separates the factors. Before doing so, it is essential to know that the factor $5^6$ on the right-hand side cannot be absorbed into the quartic factor $H$.

Theorem 0277 establishes exactly

$$
5\nmid H(r,s),
$$

which becomes the entry point for proving

$$
\gcd(5^6,H)=1.
$$

In the canonical source, after `zeroSector_natAbs_product_eq` converts the signed equation into

$$
|s|\,|H(r,s)|=5^6a^{10},
$$

this theorem is used directly to construct `Nat.Coprime (5 ^ 6) |H|`.

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket`

This is the packet structure obtained from the signed golden exceptional branch of the FLT5 development. The theorem does not unfold the packet internals; instead it uses the packet-level API `zeroSector_five_not_dvd_gamma_norm`.

### `GoldenInt`

This is the two-integer-coordinate type for elements of the golden order. The coordinates `gamma.fst` and `gamma.snd` are passed to the quartic factor.

### `goldenFifthSndFactor`

This is the quartic polynomial occurring in the second coordinate of a fifth power. In the canonical source it is defined as

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

### `goldenNorm`

The golden norm has coordinate form

$$
N(r,s)=r^2+rs-s^2.
$$

### 0274 `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm`

Under the zero-sector hypothesis `hbeta : p.beta = goldenPow gamma 5`, it gives

$$
5\nmid N(\gamma).
$$

This is the contradiction target at the end of the proof.

### 0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq`

For arbitrary `gamma : GoldenInt`, it gives

$$
5\mid(H-N^2).
$$

The present theorem combines this with `hH : 5 ∣ H` to derive $5\mid N^2$.

### `dvd_sub`

This standard divisibility lemma states that if the same integer divides two terms, then it divides their difference.

### `Prime.dvd_of_dvd_pow`

If a prime divides a power, then it divides the base. Here it is used to derive divisibility of `goldenNorm gamma` from divisibility of its square.

## Proof flow

### 1. Assume the negation of the desired conclusion

```lean
intro hH
```

Now

```lean
hH : (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

is available.

### 2. Turn the proof into a contradiction with 0274

```lean
apply p.zeroSector_five_not_dvd_gamma_norm hbeta
```

The remaining goal becomes

```lean
(5 : ℤ) ∣ goldenNorm gamma
```

so the theorem is reduced to the transfer implication “if $5\mid H$, then $5\mid N$.”

### 3. Obtain the modulo-5 relation from 0276

```lean
have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
```

This gives

$$
5\mid(H-N^2).
$$

### 4. Transfer divisibility to the square of the norm

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
  have h := dvd_sub hH hdiff
  ring_nf at h
  exact h
```

Since `hH` gives $5\mid H$ and `hdiff` gives $5\mid(H-N^2)$, their difference

$$
H-(H-N^2)=N^2
$$

is divisible by 5.

The result of `dvd_sub hH hdiff` is not syntactically already of the form `5 ∣ N^2`, so `ring_nf at h` normalizes the expression.

### 5. Descend through the prime square

```lean
exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

`norm_num` proves that the integer 5 is prime, and `Prime.dvd_of_dvd_pow` yields

$$
5\mid N^2 \Longrightarrow 5\mid N.
$$

This contradicts 0274 and closes the proof.

## Lean-specific processing

### Using `apply` on a negated proposition

The type of `p.zeroSector_five_not_dvd_gamma_norm hbeta` is

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

and Lean represents `¬ P` as `P → False`. Applying it therefore replaces the current contradiction goal with the positive divisibility goal `5 ∣ goldenNorm gamma`.

### Orientation of `dvd_sub`

`dvd_sub hH hdiff` produces a divisibility statement mathematically equivalent to

$$
5\mid H-(H-N^2).
$$

The `ring_nf` call reduces that expression to $N^2$. This is a compact combination of the divisibility API with the polynomial normalizer.

### `show Prime (5 : ℤ) by norm_num`

To use `Prime.dvd_of_dvd_pow` over integers, Lean needs the proposition `Prime (5 : ℤ)`, not merely `Nat.Prime 5`. The explicit `show` is therefore a type-directed bridge into the integer primality API.

## Redundancy and duplication

The theorem itself is short and contains little local redundancy.

The more significant duplication occurs downstream: the same pattern

1. assume `5 ∣ H`,
2. combine this with 0276 using `dvd_sub`,
3. derive `5 ∣ N ^ 2`,
4. use primality of 5 to derive `5 ∣ N`

appears again later, especially in the fifth-root-side theorem `fifthRoot_five_not_dvd_H`.

Thus the duplication is not inside 0277 itself but in the repeated **divisibility-transfer pattern**.

## Optimization candidates

### 1. Extract a generic transfer lemma

A generic integer lemma of the shape

```lean
(5 : ℤ) ∣ H - N ^ 2 → ¬ (5 : ℤ) ∣ N → ¬ (5 : ℤ) ∣ H
```

could be factored out. Then 0277 and similar later theorems would only need to supply 0276 and the appropriate norm exclusion theorem.

If the pattern is used only a small number of times, however, the current local proof may remain clearer.

### 2. Consider an `Int.ModEq` API

Since 0276 mathematically says

$$
H\equiv N^2\pmod5,
$$

an `Int.ModEq` formulation could make the transfer more explicitly congruential. The current development, however, already uses divisibility APIs heavily, so this would not necessarily reduce downstream proof size.

### 3. Possible removal of `ring_nf at h`

A different orientation of the subtraction or an intermediate equality could potentially avoid the normalization step. The present one-line `ring_nf` is robust, though, so the practical gain would be small.

## Required Mathlib imports and import optimization

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

The direct Mathlib mechanisms used by this theorem include integer divisibility, `Prime`, `dvd_sub`, `Prime.dvd_of_dvd_pow`, `norm_num`, and `ring_nf`. Project-side dependencies include `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenNorm`, `goldenFifthSndFactor`, theorem 0274, and theorem 0276.

The generated artifact manifest places this theorem in `DkMath/FLT/Five/SignedGoldenZeroSector.lean`.

The **minimal Mathlib import set has not been verified**. This run does not perform a Lean build, so replacing `import Mathlib` with a smaller concrete import list would be speculative until tactic imports and project transitive dependencies are checked in Lean.

## Relation to the existing PDFs

The target branch contains Japanese and English FLT5 PDF artifacts.

However, in this run the PDF binary contents were not available through the GitHub connector in a form suitable for direct analysis. Therefore the exact page, section, and wording corresponding to theorem 0277 remain **unverified**. The technical explanation above uses the canonical Lean source as the primary evidence and does not guess a PDF location.

## Comparator challenge suitability

**Suitable, with medium difficulty.**

A good challenge would provide

- `hbeta : p.beta = goldenPow gamma 5`,
- theorem 0274 `p.zeroSector_five_not_dvd_gamma_norm hbeta`, and
- theorem 0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq gamma`,

with target

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

The solver must discover the chain

1. assume divisibility of `H`,
2. use `dvd_sub` to get divisibility of `N ^ 2`,
3. use primality of 5 to descend to divisibility of `N`, and
4. contradict the norm exclusion theorem.

This tests composition of divisibility, primality, normalization, and existing APIs rather than merely a direct polynomial calculation.

## Next declaration to read

The next declaration is **0278 `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq`**.

In the canonical source it immediately follows 0277 and converts the signed equation from 0275

$$
sH(r,s)=-5^6a^{10}
$$

into the natural-number absolute-value equation

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

This is the natural next step in dependency order: 0277 first excludes a factor of 5 from the quartic factor, and 0278 then moves the product equation into the `Nat` factorization setting used by the subsequent splitting arguments.

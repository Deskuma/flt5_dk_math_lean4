# 0278 — `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq`

## Declaration kind

This declaration is a **`theorem`**.

It transports the signed integer product equation available in the zero sector of `SignedGoldenRamifierStrippedPacket` into a natural-number absolute-value product equation using `Int.natAbs`.

## Lean type

```lean
/-- Natural absolute-value form of the zero-sector product equation. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd.natAbs *
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  have h := congrArg Int.natAbs (p.zeroSector_snd_factor_eq hbeta)
  simpa [Int.natAbs_mul, pow_succ] using h
```

Writing `gamma = (r,s)` and

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
a=p.\operatorname{exceptional}.\operatorname{powerSplit}.a,
$$

the theorem states

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
|s|\,|H(r,s)|=5^6a^{10}.
$$

Lean's `Int.natAbs` returns the absolute value of an integer as a natural number, so both sides of the conclusion live in `ℕ`.

## Mathematical meaning

The earlier theorem 0275 `zeroSector_snd_factor_eq` gives the exact signed equation

$$
s\,H(r,s)=-5^6a^{10}
$$

in the zero sector.

The present theorem applies absolute values to both sides:

$$
|sH(r,s)|=|-5^6a^{10}|,
$$

and therefore obtains

$$
|s|\,|H(r,s)|=5^6a^{10}.
$$

Mathematically this is elementary, but structurally it is an important boundary in the proof. Up to 0275, the argument is working with signed equations in `ℤ`; from this theorem onward, prime-factor arguments, coprimality, and power splitting can be conducted with the natural-number APIs in `ℕ`.

Thus 0278 is best understood as a **bridge from signed coordinate arithmetic to natural-number factorization**.

## Role in the overall proof

The zero-sector descent eventually needs the tenth-power split

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

To reach that statement, the proof first needs the total product in the natural-number form

$$
|s|\,|H|=5^6a^{10}.
$$

This theorem supplies exactly that input.

In the canonical source, the immediately following theorem `zeroSector_coprime_coords` directly obtains the result as

```lean
have hprod := p.zeroSector_natAbs_product_eq hbeta
```

and uses it to send a hypothetical common prime divisor `q` of the coordinates into the right-hand side

$$
q\mid 5^6a^{10}.
$$

The theorem is then used again in `zeroSector_tenthPower_split`:

```lean
have hprod : gamma.snd.natAbs * H =
    5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  simpa [H] using p.zeroSector_natAbs_product_eq hbeta
```

There it is combined with 0277, which proves $5\nmid H$, and with coprimality information. This forces all six factors of 5 into the `|s|` side and then allows the remaining coprime factors to split as tenth powers.

Schematically, the dependency flow is

$$
\text{0275: }sH=-5^6a^{10}
\longrightarrow
\text{0278: }|s||H|=5^6a^{10}
\longrightarrow
\text{coprimality / 5-adic separation}
\longrightarrow
|s|=5^6c^{10},\ |H|=d^{10}.
$$

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket`

The packet structure produced by the signed golden exceptional branch. This theorem does not unfold its internal fields; instead it uses the packet-level theorem 0275.

### `GoldenInt`

The two-integer-coordinate representation of an element of the golden order. `gamma.snd` is the visible second coordinate, and `gamma.fst`, `gamma.snd` are the inputs to the quartic factor.

### `goldenPow`

Exponentiation on `GoldenInt`. The hypothesis

```lean
hbeta : p.beta = goldenPow gamma 5
```

expresses the zero-sector fifth-power representation.

### `goldenFifthSndFactor`

The quartic polynomial occurring in the second coordinate of a fifth power. For coordinates `(r,s)`,

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

### 0275 `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq`

This is the only substantive project-level dependency of the theorem. Its conclusion is

```lean
gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
  -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

and the current theorem simply applies `Int.natAbs` to this equality.

### `congrArg`

The standard congruence principle for applying the same function to both sides of an equality. Here it is used as

```lean
congrArg Int.natAbs (...)
```

to lift the signed equation to an equality of natural absolute values.

### `Int.natAbs_mul`

The multiplicativity of natural absolute value:

$$
|xy|_{\mathbb N}=|x|_{\mathbb N}|y|_{\mathbb N}.
$$

### `pow_succ`

The standard successor-power expansion lemma. In this proof it assists simplification of the powers, sign, and casts on the right-hand side.

## Proof flow

### 1. Obtain the signed equation from 0275

From

```lean
p.zeroSector_snd_factor_eq hbeta
```

we have

$$
sH=-5^6a^{10}.
$$

### 2. Apply `Int.natAbs` to both sides

```lean
have h := congrArg Int.natAbs (p.zeroSector_snd_factor_eq hbeta)
```

Conceptually, this produces an equality of the form

```lean
Int.natAbs (gamma.snd * H) =
  Int.natAbs (-(5 : ℤ) ^ 6 * (a : ℤ) ^ 10)
```

in `ℕ`.

### 3. Simplify the absolute values and casts

```lean
simpa [Int.natAbs_mul, pow_succ] using h
```

On the left, `Int.natAbs_mul` yields

```lean
gamma.snd.natAbs * H.natAbs.
```

On the right, the minus sign disappears under absolute value, and the nonnegative integer powers coming from `5` and `a` normalize to

```lean
5 ^ 6 * p.exceptional.powerSplit.a ^ 10.
```

This is exactly the target.

## Lean-specific points

### The type transition `ℤ → ℕ` via `Int.natAbs`

Using ordinary absolute value would keep the result in `ℤ`. `Int.natAbs` instead moves directly into `ℕ`, which is precisely where the downstream proof wants to use `Nat.Coprime`, `Nat.Prime`, and natural-number power-factorization lemmas.

This choice is therefore not merely cosmetic: it is a deliberate API transition.

### Lifting an equation with `congrArg`

Rather than re-proving an arithmetic identity, the proof maps an already-established equality through a function. This is a standard and robust Lean pattern for deriving alternate representations of an equation.

### `simpa` handles sign removal and casts

The signed right-hand side is

```lean
-(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10.
```

After `natAbs`, simplification removes the sign, distributes over multiplication, and normalizes the casts back into a natural-number expression. `pow_succ` supports this normalization.

## Redundancy and repetition

The theorem itself is only two proof lines, so there is essentially no local redundancy.

Architecturally, 0275 and 0278 form a useful pair: 0275 preserves the exact signed equation, while 0278 exposes the natural-number factorization form. If similar signed-to-`natAbs` bridges occur repeatedly elsewhere in the descent development, the common pattern

```lean
congrArg Int.natAbs ...
```

followed by multiplicativity simplification could be abstracted.

For this theorem alone, however, additional abstraction would likely reduce readability rather than improve it.

## Optimization candidates

### 1. Check whether `pow_succ` is necessary

The current proof is

```lean
simpa [Int.natAbs_mul, pow_succ] using h
```

Depending on the current Mathlib simp set and cast normalization, it may be possible to remove `pow_succ`.

This is an **unverified optimization candidate**. No Lean build is performed in this run, and the existing proof is already short and stable.

### 2. Extract a generic signed-product-to-`natAbs` lemma

If the same pattern appears many times, one could introduce a general lemma converting equations such as

```lean
x * y = -(m : ℤ) ^ k * (a : ℤ) ^ n
```

into a natural absolute-value product equation.

However, once exponent parity, casts, and sign conditions are generalized, such a helper may become heavier than the two-line specialized proof.

### 3. Naming

`zeroSector_natAbs_product_eq` accurately exposes both the operation (`natAbs`) and the resulting shape (`product_eq`). A more mathematical name such as `zeroSector_abs_factorization_eq` is possible, but the current name has better searchability against the actual Lean primitive used in the proof.

## Required Mathlib imports and import optimization

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

and its manifest places this theorem in `DkMath/FLT/Five/SignedGoldenZeroSector.lean`.

The Mathlib mechanisms directly used here are small:

- equality congruence via `congrArg`;
- `Int.natAbs`;
- `Int.natAbs_mul`;
- integer/natural casts and simp normalization;
- `pow_succ`.

On the project side, the theorem needs `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenPow`, `goldenFifthSndFactor`, and 0275.

The **minimal Mathlib import set for the original module is not confirmed**. The standalone artifact intentionally uses broad `import Mathlib`, and no Lean build is performed here, so a concrete reduced import list would be speculative rather than verified.

## Relation to the existing PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`, and
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the normal GitHub repository-content connector path does not expose those PDF binaries in an analyzable textual form in this run. Therefore the precise page number, section number, and wording corresponding to this theorem are **not confirmed**.

The theorem-level technical discussion here is grounded primarily in the canonical Lean source, specifically the generated `DkMath/FLT/Five/SignedGoldenZeroSector.lean` section of `Flt5DkMath/FLT5StandAlone.lean`. No PDF page correspondence is guessed.

## Comparator challenge suitability

**Suitable; low-to-medium difficulty.**

A challenge can provide 0275 as an available lemma via

```lean
p.zeroSector_snd_factor_eq hbeta
```

and ask for the goal

```lean
gamma.snd.natAbs *
    (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
  5 ^ 6 * p.exceptional.powerSplit.a ^ 10.
```

The challenge is not about polynomial algebra. Its educational core is the Lean-side type transition:

1. apply `Int.natAbs` to an equality;
2. use `Int.natAbs_mul`;
3. simplify signs and casts into a natural-number expression.

That makes it a compact exercise in transporting an `ℤ` arithmetic fact into a downstream `ℕ` factorization API.

## Next declaration to read

The next declaration in the canonical source is

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
```

It proves that the two integer coordinates of the zero-sector fifth-power base `gamma` are primitive:

$$
\gcd(|r|,|s|)=1.
$$

Its proof directly uses the present 0278 product equation. A hypothetical common prime divisor `q` of the two coordinates is sent into the right-hand side `5^6a^{10}`, and the resulting alternatives are contradicted by the packet facts `five_not_dvd_b` and `powerSplit.coprime_a_b`.

Thus 0278 is not merely a formatting lemma: it is the factorization input that activates the next primitive-coordinate argument.
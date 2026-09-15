# 0379 `snd_natAbs_eq`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma expresses the natural absolute value of the packet's second coordinate exactly in terms of the preserved fifth-power parameter `t`.

## Lean code

```lean
theorem snd_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    p.base.snd.natAbs = 5 * p.t ^ 5 := by
  rcases p.snd_eq with h | h <;> rw [h]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
```

## Lean type

Expanding the namespace, its type is conceptually

```lean
GoldenZeroSectorDescentPacket.snd_natAbs_eq :
  (p : GoldenZeroSectorDescentPacket) →
    p.base.snd.natAbs = 5 * p.t ^ 5
```

Since `Int.natAbs` is applied to `p.base.snd : ℤ`, the left-hand side has type `ℕ`. The right-hand side is likewise the natural number

$$
5t^5
$$

built from `p.t : ℕ`, so both sides live in the same type `ℕ`.

## Mathematical statement

0376 `GoldenZeroSectorDescentPacket` preserves the second-coordinate condition

$$
s=5t^5
\quad\text{or}\quad
s=-5t^5,
$$

where

$$
s=p.base.snd.
$$

Therefore, independently of the sign,

$$
|s|=5t^5.
$$

Because Lean's `Int.natAbs` returns the absolute value of an integer as a natural number, the precise theorem statement is

$$
\operatorname{natAbs}(p.base.snd)=5p.t^5.
$$

Whereas 0378 `snd_ne_zero` extracted the qualitative nondegeneracy statement $s\ne0$, this theorem gives the exact quantitative value of its magnitude.

## Role in the whole proof

0377 defines the descent measure by

$$
\mu(p)=|p.base.snd|.
$$

The present theorem therefore identifies that measure with the packet parameter `t` by

$$
\mu(p)=5t^5.
$$

This exact formula is used directly later in `fifthRoot_power_split`. There, the product involving the second coordinate of a fifth root `gamma` and its quartic factor produces

$$
|s|^2,
$$

which this theorem rewrites as

$$
|s|^2=(5t^5)^2.
$$

After algebraic rearrangement this becomes

$$
|\gamma_2|\,|H(\gamma)|=5(t^2)^5,
$$

which has exactly the form needed for a coprime fifth-power splitting argument.

The canonical Lean source uses the theorem directly as

```lean
_ = (5 * p.t ^ 5) ^ 2 := by rw [p.snd_natAbs_eq]
_ = 5 * (5 * (p.t ^ 2) ^ 5) := by ring
```

Thus this lemma is the bridge that converts the packet's signed coordinate invariant into an unsigned natural-number invariant consumable by the recursive fifth-power factorization.

## Direct dependencies

The direct project-level dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.snd_eq`

The main Lean / Mathlib facilities used directly are:

- `Int.natAbs`
- `Int.natAbs_mul`
- `Int.natAbs_pow`
- `rcases`
- `rw`
- `simp`

It does not depend on 0378 `snd_ne_zero`; this theorem is derived independently from `snd_eq` alone.

## Proof flow

1. Start from the packet's signed equation

   ```lean
   p.snd_eq :
     p.base.snd = 5 * (p.t : ℤ) ^ 5 ∨
       p.base.snd = -(5 * (p.t : ℤ) ^ 5)
   ```

   and split its two cases with

   ```lean
   rcases p.snd_eq with h | h
   ```

2. `<;> rw [h]` replaces `p.base.snd` by the concrete signed fifth-power expression in both generated goals.

3. In the positive branch,

   $$
   |5t^5|=5t^5
   $$

   is normalized by `simp` using `Int.natAbs_mul` and `Int.natAbs_pow`.

4. In the negative branch,

   $$
   |-5t^5|=5t^5,
   $$

   and the sign disappears under `natAbs`.

The two branches therefore merge into the same natural-number identity.

## Lean-specific processing

### `rcases ... with h | h`

`p.snd_eq` is a disjunction retaining the sign information, so it cannot be used as a single rewrite equation. `rcases` explicitly separates its two sign cases.

### `<;> rw [h]`

The tactic combinator `<;>` applies the same `rw [h]` command to both goals produced by the preceding case split.

This abbreviates the more repetitive form

```lean
rcases p.snd_eq with h | h
· rw [h]
  ...
· rw [h]
  ...
```

and is a Lean-specific way to share tactic steps across branches.

### `Int.natAbs_mul`

This transports the natural absolute value of an integer product to the product of natural absolute values. Conceptually,

$$
|ab|=|a||b|.
$$

Here it moves the integer coefficient `5` and `(p.t : ℤ)^5` into a natural-number product.

### `Int.natAbs_pow`

This transports `natAbs` through an integer power:

$$
|x^n|=|x|^n.
$$

Since `p.t` originates in `ℕ`, the absolute value of its cast simplifies back to `p.t`.

### `simp`

In both branches, `simp` simultaneously normalizes multiplicativity of `natAbs`, powers, sign invariance, and the natural-number cast.

The mathematical content is elementary, but `simp` carries the type-level transition from a signed invariant over `ℤ` to a measure equation over `ℕ`.

## Redundancy and duplication

Both branches close with exactly the same command:

```lean
simp [Int.natAbs_mul, Int.natAbs_pow]
```

Therefore the tactic script could potentially be compressed to

```lean
  rcases p.snd_eq with h | h <;>
    rw [h] <;>
    simp [Int.natAbs_mul, Int.natAbs_pow]
```

However, the current source keeps the two branches visually explicit, making it immediately clear that `snd_eq` has positive and negative cases. This can reasonably be read as preferring explanatory structure over minimal line count.

It is also possible that `Int.natAbs_mul` and `Int.natAbs_pow` are already sufficiently represented in the current Mathlib simp set for some of these explicit arguments to be unnecessary. This has not been verified because this task does not run a Lean build.

## Optimization candidates

1. **Merge the identical `simp` branches**

   Since both branches use the same closing tactic, `<;>` can combine them.

2. **Add a measure-facing API lemma**

   From 0377 and the present theorem one could expose

   ```lean
   theorem descentMeasure_eq (p : GoldenZeroSectorDescentPacket) :
       goldenZeroSectorDescentMeasure p = 5 * p.t ^ 5 := ...
   ```

   so downstream proofs do not need to know that the measure is implemented as `base.snd.natAbs`.

3. **Expose positivity of the measure**

   From `p.t_pos` and this theorem one can readily derive

   $$
   0<\mu(p).
   $$

   A lemma such as `goldenZeroSectorDescentMeasure_pos` would be a natural part of the well-founded descent API.

4. **Separate signed and unsigned invariants**

   The packet could store both `snd_eq` and an equation equivalent to `snd_natAbs_eq`, which would shorten downstream proofs. That would duplicate information, however, so deriving the unsigned equation as a theorem, as the present design does, keeps the invariant itself smaller.

## Required Mathlib imports and import optimization candidates

The standalone canonical source uses `import Mathlib`.

For this theorem alone, the needed facilities are integers and naturals, `Int.natAbs`, powers, the basic tactics `rcases` / `rw` / `simp`, and the lemmas `Int.natAbs_mul` and `Int.natAbs_pow`.

The theorem also depends on the project definition `GoldenZeroSectorDescentPacket`, so a modular source file must import the FLT5 project layer that makes that packet available.

The exact minimal Mathlib import has not been verified because no Lean build is performed in this task. Any replacement of `import Mathlib` by specific modules therefore remains only an optimization candidate.

## Comparator challenge suitability

**Yes. It is suitable as a small sign-elimination / `natAbs` normalization challenge.**

The essential tasks are:

- handling a positive/negative disjunction,
- normalizing `natAbs` from `ℤ` to `ℕ`,
- transporting `natAbs` through multiplication and powers,
- removing the sign in the negative branch.

The difficulty is low, but it is a clean micro challenge for testing whether a solver handles the integer/natural-number boundary correctly.

For a harder variant, one could restrict `simp` and require explicit composition of lemmas such as `Int.natAbs_mul`, `Int.natAbs_pow`, and `Int.natAbs_neg`.

## Next declaration to read

The next declaration in the same namespace is

```lean
theorem H_pos (p : GoldenZeroSectorDescentPacket) :
    0 < goldenFifthSndFactor p.base.fst p.base.snd := by
  rw [p.H_eq]
  exact pow_pos (by exact_mod_cast p.D_pos) 5
```

The packet preserves

$$
H(p.base.fst,p.base.snd)=D^5,
\qquad D>0,
$$

so this theorem extracts

$$
H(p.base.fst,p.base.snd)>0.
$$

Where the present theorem converts the second coordinate's signed equation into a natural absolute-value identity, the next theorem extracts positivity from the quartic side's fifth-power invariant. Together they make the two principal descent quantities

$$
|s|
\quad\text{and}\quad
H(r,s)
$$

available as nondegenerate positive quantities.
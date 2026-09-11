# 0383 `coprime_s_H`

## Declaration kind

`theorem`

Inside the `GoldenZeroSectorDescentPacket` namespace, this lemma exposes that the packet's second coordinate `s` is coprime to the quartic factor `H(r,s)`.

## Lean code

```lean
theorem coprime_s_H (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs :=
  coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.base.fst p.base.snd p.coprime_coords
```

## Lean type

After expanding the namespace, its conceptual type is

```lean
GoldenZeroSectorDescentPacket.coprime_s_H :
  (p : GoldenZeroSectorDescentPacket) →
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs
```

The coordinates of `p.base : GoldenInt` are

```lean
p.base.fst : ℤ
p.base.snd : ℤ
```

while `Nat.Coprime` is a relation on natural numbers, so both integer quantities are transferred to naturals using `Int.natAbs`.

## Mathematical statement

Write `p.base = (r,s)` and set

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s).
$$

The packet stores the primitive condition

$$
\gcd(|r|,|s|)=1
$$

in the field `coprime_coords`.

The present theorem derives

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

Thus, for primitive coordinates `(r,s)`, no new common prime divisor appears between the visible second coordinate `s` and the quartic fifth-power coordinate factor `H(r,s)`. The theorem packages this fact as a packet-level API.

## Role in the overall proof

0381–0382 propagated the 5-adic clean property down to the fifth root `D`:

$$
5\nmid H(r,s)
\Longrightarrow
5\nmid D.
$$

From 0383 onward, the argument moves into a coprimality chain. The present theorem extracts from the packet's primitive condition the implication

$$
\gcd(|r|,|s|)=1
\Longrightarrow
\gcd(|s|,|H(r,s)|)=1.
$$

The immediately following theorem `coprime_D_s` combines this with the packet identity

$$
H(r,s)=D^5
$$

to obtain

$$
\gcd(D,|s|)=1.
$$

Later lift/conjugate coprimality arguments combine the mutual coprimality of `D^5`, `|s|`, and 5 to exclude nonunit common divisors of the quadratic lift and its conjugate.

Accordingly, this theorem is the bridge that translates the original primitive-coordinate condition into the coprimality needed after fifth-power re-entry.

## Direct dependencies

The directly used project declarations are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.coprime_coords`
- `GoldenInt.fst`
- `GoldenInt.snd`
- `goldenFifthSndFactor`
- `coprime_natAbs_goldenFifthSndFactor_of_coprime`

The general lemma called directly has type

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
    (r s : ℤ) (hrs : Nat.Coprime r.natAbs s.natAbs) :
    Nat.Coprime s.natAbs (goldenFifthSndFactor r s).natAbs
```

That lemma contains the substantive argument converting primitive coordinates into coprimality between `s` and the quartic factor. The present theorem specializes it with

```lean
r   := p.base.fst
s   := p.base.snd
hrs := p.coprime_coords
```

0380 `H_pos`, 0381 `five_not_dvd_H`, and 0382 `five_not_dvd_D` are not direct dependencies. The proof term itself closes using only `coprime_coords` and the general lemma.

## Proof / construction flow

The proof is a single term-style specialization and contains no tactic block.

1. Extract the packet coordinates:

   ```lean
   p.base.fst
   p.base.snd
   ```

2. Extract the primitive invariant:

   ```lean
   p.coprime_coords
   ```

   whose type is

   ```lean
   Nat.Coprime p.base.fst.natAbs p.base.snd.natAbs
   ```

3. Pass those values directly to the general theorem:

   ```lean
   coprime_natAbs_goldenFifthSndFactor_of_coprime
     p.base.fst p.base.snd p.coprime_coords
   ```

4. The conclusion of that theorem definitionally matches the current goal, so the resulting proof term is the entire body of `coprime_s_H`.

All substantive arithmetic has already been discharged in the reusable general lemma. The role of 0383 is to provide a named specialization appropriate to the descent packet.

## Mathematics inside the general lemma

The repository's `coprime_natAbs_goldenFifthSndFactor_of_coprime` proves the result by contradiction. Assuming that `|s|` and `|H(r,s)|` are not coprime, it extracts a common prime divisor `q`.

Its opening is schematically

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqs, hqH⟩
```

After extracting `q`, the proof transports the natural-number divisibility facts back to integer divisibility using `Int.natCast_dvd.mpr`, then exploits the congruence structure of the quartic polynomial. This forces `q` to divide `r` as well, contradicting

$$
\gcd(|r|,|s|)=1.
$$

Thus the one-line proof of 0383 is short not because the mathematics is weak, but because the polynomial divisibility argument has already been abstracted into a reusable lemma.

## Lean-specific processing

### Term-style proof

The theorem does not use

```lean
:= by
```

Instead, the result of applying an existing theorem is placed directly on the right-hand side.

Lean computes the result type from the arguments and sees that it exactly matches the target, so no rewrite is required.

### Structure projections

```lean
p.base.fst
p.base.snd
p.coprime_coords
```

are all structure-field projections.

In particular, `p.coprime_coords` retrieves an invariant stored when the `GoldenZeroSectorDescentPacket` was constructed, allowing later theorems to reuse it rather than re-prove primitiveness.

### `Int.natAbs`

Because `Nat.Coprime` lives over natural numbers, signed integer coordinates are mapped through `natAbs`.

This makes the statements

$$
\gcd(|r|,|s|)=1
$$

and

$$
\gcd(|s|,|H(r,s)|)=1
$$

independent of signs.

## Redundancy and duplication

Locally, the code is already a one-line specialization, so there is essentially no computational redundancy.

At first sight the theorem might appear unnecessary because later code could call the general lemma directly. However, as a descent API this named theorem is useful.

Rather than repeatedly writing

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
  p.base.fst p.base.snd p.coprime_coords
```

later proofs can simply use

```lean
p.coprime_s_H
```

which exposes the mathematical meaning and preserves the packet abstraction boundary.

The apparent duplication is therefore intentional and reasonable as an API layer.

## Optimization candidates

1. **Keep the current form**

   The split between a general arithmetic theorem and a packet-specific corollary is clean, and the proof is already minimal.

2. **No need for `@[simp]`**

   `Nat.Coprime ...` is not an equality intended for rewriting, so adding this theorem to the simp set would provide little benefit.

3. **Keep the short name**

   Within the namespace, `coprime_s_H` is concise and readable. Outside the namespace, the fully qualified name `GoldenZeroSectorDescentPacket.coprime_s_H` already supplies enough context, so a longer declaration name is unnecessary.

4. **Preserve the reusable general lemma**

   The contradiction proof from the general theorem should not be copied into this packet theorem. The current arrangement centralizes the polynomial arithmetic in one place and improves maintainability.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`.

At the surface level, this theorem itself needs mainly:

- `Nat.Coprime`
- `Int.natAbs`
- basic Lean support for structure projections and theorem application

The body itself uses no tactics and does not directly invoke `ring`, `norm_num`, `omega`, or `exact_mod_cast`.

However, the directly called theorem `coprime_natAbs_goldenFifthSndFactor_of_coprime` depends on prime/divisibility/integer-cast APIs, so the minimal project import must account for those transitive dependencies as well.

Because no Lean build is performed in this task, the exact minimal Mathlib module set has not been verified. Specific module names are therefore intentionally not asserted.

## Comparator challenge suitability

**Yes, but the theorem itself is very easy, so two distinct challenge forms are useful.**

### API-selection challenge

Provide `GoldenZeroSectorDescentPacket` and the general lemma, then ask the model to reconstruct the present theorem in one line.

This tests whether it can:

- select the appropriate structure projections,
- discover and reuse the existing general theorem,
- avoid unnecessary polynomial expansion.

This is a good small Comparator challenge for proof search and theorem reuse.

### Substantive arithmetic challenge

For a more demanding challenge, use the general theorem

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
```

itself.

The core tasks are then:

- extract a common prime divisor from non-coprimality,
- transport natural divisibility into integers,
- use the quartic factor shape to deduce `q ∣ r^4`,
- descend prime divisibility to `q ∣ r`,
- contradict primitive coordinates.

Thus 0383 is best treated as an API-composition challenge, while the general lemma is the substantive arithmetic challenge.

## Next declaration to read

The next declaration is 0384 `coprime_D_s`, again a `theorem`.

```lean
theorem coprime_D_s (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.D p.base.snd.natAbs := by
  have hcop := p.coprime_s_H
  have hHAbs :
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
    rw [p.H_eq, Int.natAbs_pow]
    simp
  ...
```

Where 0383 establishes

$$
\gcd(|s|,|H(r,s)|)=1,
$$

0384 uses

$$
H(r,s)=D^5
$$

to descend coprimality to the fifth root and obtain

$$
\gcd(D,|s|)=1.
$$
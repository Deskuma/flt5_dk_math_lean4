# 0395 `GoldenZeroSectorStrictDescent`

## Declaration kind

`structure`

This proof-data structure packages one strict descent step from a `GoldenZeroSectorDescentPacket` into three pieces: the next packet, the fifth-power re-entry equation, and strict decrease of the measure.

## Lean code

```lean
/-- One certified re-entry step with strict decrease of the visible coordinate. -/
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

## Lean type

Conceptually, the declaration has type

```lean
GoldenZeroSectorStrictDescent :
  GoldenZeroSectorDescentPacket → Type
```

For a fixed `source : GoldenZeroSectorDescentPacket`, an inhabitant contains

```lean
{
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
}
```

Crucially, `next` is not merely a `GoldenInt`. It is a complete next-generation packet satisfying all recursive zero-sector descent invariants.

## Mathematical statement

Write

$$
\alpha = source.base
$$

and

$$
\gamma = next.base.
$$

The structure records two mathematical facts as one certified step.

First, the re-entry equation

$$
T(\alpha)=\gamma^5,
$$

where

$$
T(r,s)=\left(r^2+rs+s^2,\ s^2\right).
$$

Second, strict decrease of the measure

$$
\mu(next)<\mu(source),
$$

with

$$
\mu(p)=|p.base.snd|.
$$

Thus the structure represents a transition

$$
source \longmapsto next
$$

inside the same zero-sector invariant while forcing a strictly smaller natural-number measure.

## Role in the overall proof

0395 is the boundary where the two strands developed immediately before it are packaged together.

By 0394, the fifth root `gamma` has recovered the recursive fifth-power shape

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma)=v^5,
$$

together with primitive coordinates, norm prime to five, and the positivity conditions needed to build another `GoldenZeroSectorDescentPacket`.

Independently, 0393 proves

$$
|\gamma_{\mathrm{snd}}|<|source.base.snd|.
$$

`GoldenZeroSectorStrictDescent` combines these as

$$
\text{recursive shape preserved}
\quad+\quad
\text{measure strictly decreases}.
$$

The following theorem `GoldenZeroSectorDescentPacket.strictDescent` constructs an actual inhabitant of this structure. The theorem after that, `goldenZeroSectorDescentPacket_false`, consumes the certificate with `Nat.strong_induction_on` to close the infinite descent.

Accordingly, 0395 is the **interface structure** between local arithmetic and well-founded descent.

## Meaning of the fields

### `next`

```lean
next : GoldenZeroSectorDescentPacket
```

This stores the next packet itself.

It therefore carries the full recursive invariant, including:

- a second coordinate of the form $5u^5$;
- a quartic factor that is a fifth power;
- primitive coordinates;
- a norm not divisible by five.

### `lift_eq`

```lean
lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
```

This records that the quadratic lift of the source is the fifth power of the next base:

$$
T(source.base)=next.base^5.
$$

It is provenance: `next` is not an arbitrary smaller packet, but a legitimate re-entry root generated from the arithmetic of `source`.

### `measure_lt`

```lean
measure_lt :
  goldenZeroSectorDescentMeasure next <
    goldenZeroSectorDescentMeasure source
```

This stores strict decrease of the natural-valued measure. Expanding the definition gives

$$
|next.base.snd|<|source.base.snd|.
$$

Because the inequality is a field of the certificate, the later induction argument does not have to reopen the arithmetic proof of decrease.

## Direct dependencies

The declaration itself directly refers only to:

- `GoldenZeroSectorDescentPacket`;
- `goldenZeroSectorLift`;
- `goldenPow`;
- `goldenZeroSectorDescentMeasure`.

However, the immediately following theorem showing that this structure is inhabited depends on the main preceding results:

- `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`;
- `GoldenZeroSectorDescentPacket.fifthRoot_power_split`;
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`;
- `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`;
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`.

Thus 0395 is syntactically a thin declaration, but semantically it is the aggregation point of 0387–0394.

## Construction flow

The structure declaration itself has no proof script. Lean automatically generates a constructor for its three fields.

The following `strictDescent` theorem constructs a value essentially as follows.

1. Obtain a fifth root `gamma` from `exists_lift_eq_fifthPower`.
2. Apply `fifthRoot_power_split` to obtain positive `u,v` satisfying
   $$
   \gamma.snd=5u^5,
   \qquad
   H(\gamma)=v^5.
   $$
3. Recover coordinate primitivity through `fifthRoot_coprime_coords`.
4. Recover nondivisibility of the norm by five.
5. Assemble these facts into `next : GoldenZeroSectorDescentPacket`.
6. Store `hroot` as `lift_eq`.
7. Store 0393 `fifthRoot_measure_lt` as `measure_lt`.

This separation keeps the arithmetic construction distinct from the strong-induction closure.

## Lean-specific processing

The syntax

```lean
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
```

defines a parameterized structure. `source` is available to the fields but is not itself an ordinary record field.

Consequently, `GoldenZeroSectorStrictDescent p` is the type of descent certificates **from the specific source `p`**, rather than the type of arbitrary descent steps.

Because `next` is declared first, later fields can depend on it. This is a standard dependent-record pattern: `lift_eq` and `measure_lt` both refer to the previously introduced `next`.

The later closure can destruct the existential wrapper with

```lean
obtain ⟨step⟩ := q.strictDescent
```

and then use

```lean
step.next
step.measure_lt
```

to continue strong induction. The arithmetic internals remain hidden from the induction body, which is an important proof-engineering benefit.

## Redundancy and duplication

The structure itself has only three fields and contains essentially no syntactic redundancy.

One possible question is whether `lift_eq` is strictly necessary. The later theorem `goldenZeroSectorDescentPacket_false` directly uses only `next` and `measure_lt`; if the sole purpose were to close strong induction, `lift_eq` could appear redundant.

Nevertheless, `lift_eq` preserves the provenance of the descent step: it certifies that the next packet comes from a fifth root of the source's quadratic lift. Retaining it therefore improves auditability and reuse, and prevents the certificate from degenerating into an unexplained choice of a smaller packet.

Likewise, storing `measure_lt` as a field avoids having to reconstruct its arguments or rerun the arithmetic proof when the step is consumed later.

## Optimization candidates

The current declaration is already minimal for its domain-specific role.

If the repository later acquires several descents of the same shape, one possible abstraction would be

```lean
structure StrictDescentStep (α : Type) (measure : α → ℕ) (source : α) where
  next : α
  measure_lt : measure next < measure source
```

and the FLT5-specific re-entry equation could then be added as an extra refinement.

For the present proof, however, keeping the domain-specific `lift_eq` together with the strict decrease is useful, and introducing a generic framework would not necessarily reduce code. Such abstraction is more compelling only if the pattern recurs across other exponents or descent arguments.

## Required Mathlib imports and import optimization

The declaration itself invokes no advanced Mathlib theorem. It only requires that the referenced DkMath definitions already be available.

The standalone source currently assumes `import Mathlib`, but the exact minimal import for this structure alone cannot be certified here because this run does not perform a Lean build.

At the declaration level, no arithmetic tactic, `Finset` machinery, or algebraic-number-theory API is used directly. If this declaration were split into its own module, its import requirements could likely be restricted to the modules defining `GoldenZeroSectorDescentPacket`, `goldenZeroSectorLift`, `goldenPow`, and `goldenZeroSectorDescentMeasure`.

## Comparator challenge suitability

**Weak as a standalone challenge.**

0395 has no proof body: it is a `structure` declaration. A standalone Comparator task would mainly test whether the model reproduces the intended dependent-record design.

By contrast, 0395 together with the following `GoldenZeroSectorDescentPacket.strictDescent` theorem forms a strong challenge. The target

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

requires the model to combine the established 0387–0394 API into:

- root extraction;
- fifth-power splitting;
- primitive invariant recovery;
- the 5-adic invariant;
- strict measure decrease;
- dependent-record construction.

Therefore the best Comparator unit is a **0395+0396 constructor challenge**, rather than 0395 in isolation.

## Next declaration to read

The next declaration is

```lean
theorem GoldenZeroSectorDescentPacket.strictDescent
    (p : GoldenZeroSectorDescentPacket) :
    Nonempty (GoldenZeroSectorStrictDescent p) := by
  ...
```

0395 defines what a certified strict descent step must contain. The next theorem actually assembles the results of 0387–0394 into an inhabitant of that type.

The proof flow is therefore

$$
\text{packet arithmetic}
\longrightarrow
\text{strict descent certificate}
\longrightarrow
\text{strong induction closure},
$$

and the next declaration is the constructor at the center of that chain.
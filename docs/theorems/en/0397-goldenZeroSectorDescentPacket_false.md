# 0397 `goldenZeroSectorDescentPacket_false`

## Declaration kind

`theorem`

This theorem closes the contradiction for any `GoldenZeroSectorDescentPacket` by strong induction on its natural-valued descent measure.

## Lean code

```lean
/--
There is no infinite chain of certified zero-sector descent packets. `strictDescent`
preserves the packet invariant and supplies a smaller natural measure, so
`Nat.strong_induction_on` applies. The argument uses only the golden lift and
preceding packet lemmas, never the final FLT5 theorem; hence the closure is
non-circular.
-/
theorem goldenZeroSectorDescentPacket_false
    (p : GoldenZeroSectorDescentPacket) : False := by
  have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
      goldenZeroSectorDescentMeasure q = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hq
        obtain ⟨step⟩ := q.strictDescent
        exact ih (goldenZeroSectorDescentMeasure step.next)
          (by simpa [hq] using step.measure_lt) step.next rfl
  exact noAt (goldenZeroSectorDescentMeasure p) p rfl
```

## Lean type

```lean
goldenZeroSectorDescentPacket_false :
  (p : GoldenZeroSectorDescentPacket) → False
```

The input is a packet satisfying the certified zero-sector descent invariant, and the output is `False`.

Logically, this is the elementwise form of the assertion

$$
\neg\,\mathrm{Nonempty}(\mathrm{GoldenZeroSectorDescentPacket}).
$$

## Mathematical statement

Define the measure by

$$
\mu(p)=|p.base.snd|\in\mathbb N.
$$

By 0396, `GoldenZeroSectorDescentPacket.strictDescent`, every packet `q` admits another packet `q'` satisfying

$$
\mu(q')<\mu(q).
$$

If an initial packet `p` existed, repeated descent would therefore yield

$$
\mu(p)>
\mu(p_1)>
\mu(p_2)>
\mu(p_3)>
\cdots,
$$

an infinite strictly descending chain of natural numbers. Such a chain cannot exist because `<` on `ℕ` is well-founded.

This theorem formalizes that classical infinite-descent argument directly with `Nat.strong_induction_on`.

## Role in the full proof

0397 is the **well-founded closure** of the zero-sector descent subproof.

Declarations 0387–0394 establish fifth-root extraction, coordinate arithmetic, primitive conditions, nondivisibility by five, fifth-power splitting, and strict measure decrease. Declaration 0395 introduces the certificate type `GoldenZeroSectorStrictDescent`, and 0396 proves that every packet has such a certificate.

At 0397 none of the local arithmetic is unfolded again. The proof consumes only

```lean
obtain ⟨step⟩ := q.strictDescent
```

and

```lean
step.measure_lt.
```

Conceptually, the dependency architecture has therefore become

$$
\text{local golden arithmetic}
\longrightarrow
\text{certified strict descent}
\longrightarrow
\text{well-founded contradiction}.
$$

As the source comment states, this closure does not invoke the final FLT5 theorem to eliminate the zero sector. It closes using only the preceding golden-lift and packet lemmas, so the argument is non-circular.

## Direct dependencies

The principal direct dependencies are:

- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorDescentMeasure`
- `GoldenZeroSectorDescentPacket.strictDescent` — 0396
- `GoldenZeroSectorStrictDescent.next` — field of 0395
- `GoldenZeroSectorStrictDescent.measure_lt` — field of 0395
- `Nat.strong_induction_on`

In particular, the measure is defined by

```lean
def goldenZeroSectorDescentMeasure
    (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

so the integral second coordinate is projected by `natAbs` into a well-founded natural-number measure.

The other field of the 0395 certificate,

```lean
lift_eq :
  goldenZeroSectorLift source.base = goldenPow next.base 5
```

is not referenced directly by the proof term of 0397. It records the mathematical provenance of the descent step; the abstract well-founded closure itself consumes only `next` and `measure_lt`.

## Proof flow

1. Introduce a local proposition saying that no packet can have measure exactly `n`:

   ```lean
   have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
       goldenZeroSectorDescentMeasure q = n → False := by
   ```

2. Apply strong induction to `n`:

   ```lean
   induction n using Nat.strong_induction_on with
   | h n ih =>
   ```

   The induction hypothesis `ih` is available for every strictly smaller natural number `m<n`.

3. Assume a packet `q` with

   ```lean
   hq : goldenZeroSectorDescentMeasure q = n.
   ```

4. Extract one strict descent certificate from 0396:

   ```lean
   obtain ⟨step⟩ := q.strictDescent
   ```

5. The field `step.measure_lt` gives

   $$
   \mu(step.next)<\mu(q).
   $$

   Rewriting the right-hand side with `hq` yields

   $$
   \mu(step.next)<n.
   $$

6. Apply `ih` at that smaller measure. The new packet `step.next` has measure equal to itself, so the final equality argument is discharged by `rfl`.

7. Finally instantiate `noAt` at the measure of the original packet:

   ```lean
   exact noAt (goldenZeroSectorDescentMeasure p) p rfl
   ```

This produces `False`.

## Lean-specific handling

### `induction n using Nat.strong_induction_on`

Ordinary successor induction directly exposes only the immediately preceding case, while a descent step is not required to lower the measure by exactly one.

The available invariant is only

$$
\mu(next)<\mu(source),
$$

so strong induction, which permits every smaller natural number, is the natural mechanism.

### `obtain ⟨step⟩ := q.strictDescent`

Declaration 0396 returns

```lean
Nonempty (GoldenZeroSectorStrictDescent q).
```

The needed witness is immediately eliminated with `obtain`.

Because the target is `False`, hence a proposition, elimination from `Nonempty` is sufficient. No computational witness extraction or `Classical.choose` is required.

### `simpa [hq] using step.measure_lt`

The right-hand side of `step.measure_lt` is

```lean
goldenZeroSectorDescentMeasure q,
```

whereas `ih` expects the upper bound `n`. Supplying `hq` to the simplifier rewrites these into the required form.

### `rfl`

After selecting `step.next`, the remaining equality

```lean
goldenZeroSectorDescentMeasure step.next =
  goldenZeroSectorDescentMeasure step.next
```

is closed by reflexivity.

## Redundancy and duplication

There is almost no arithmetic duplication inside 0397. Instead, the theorem demonstrates that 0395–0396 have already abstracted the arithmetic and descent certificate sufficiently well.

One minor structural redundancy is the equality-indexed local proposition

```lean
∀ n, ∀ q, goldenZeroSectorDescentMeasure q = n → False.
```

This introduces a measure index and then closes with

```lean
noAt (goldenZeroSectorDescentMeasure p) p rfl.
```

That form is very readable for direct strong induction, but a more general well-founded relation could avoid the equality index entirely.

Also, the `lift_eq` field of 0395 is invisible here, but that does not make it redundant. Since 0397 is the abstract closure layer, the fact that the transition genuinely comes from a fifth-root lift should already be certified and hidden behind 0396.

## Optimization candidates

The strongest generalization is to extract a generic strict-descent impossibility lemma.

Conceptually, for a type `α`, a measure `μ : α → ℕ`, and an operation satisfying

$$
\forall x:\alpha,\;\exists y:\alpha,\;\mu(y)<\mu(x),
$$

no inhabitant of `α` can exist.

A possible API shape would be

```lean
theorem false_of_always_exists_smaller
    {α : Type*} (μ : α → ℕ)
    (step : ∀ x : α, Nonempty { y : α // μ y < μ x }))
    (x : α) : False := ...
```

Then 0397 would merely instantiate this generic lemma with the packet type, its measure, and the descent operation from 0396. Such an abstraction becomes particularly attractive if FLT3, FLT5, or future prime-exponent developments reuse the same closure pattern.

Alternatively, `Nat.lt_wfRel` or the general `WellFounded` / measure API could express the proof as the impossibility of endlessly descending a well-founded relation, raising the abstraction level above explicit natural-number induction.

The current proof is nevertheless extremely short and makes the descent principle transparent, so it is already a strong implementation for a standalone FLT5 development.

## Required Mathlib imports and import optimization

The standalone canonical source currently uses

```lean
import Mathlib
```

for the complete generated development.

The Mathlib-side functionality directly used by 0397 is primarily:

- `Nat.strong_induction_on`
- proposition-level elimination of `Nonempty`
- `simpa`

The packet type, measure, and `strictDescent` theorem are preceding DkMath declarations.

This theorem itself does not directly use the heavier ring, valuation, number-field, or nonlinear-arithmetic APIs that occur earlier in the proof. Therefore its local Mathlib dependency could likely be made quite small if the source modules were split finely.

The exact minimal import set is not confirmed here because no Lean build is being run. A safe import-minimization experiment would first import the DkMath module providing declarations through 0396, then add only the Mathlib modules required for `Nat.strong_induction_on` and the `simpa` tactic.

## Comparator challenge feasibility

**Highly suitable.**

0397 tests whether a prover can correctly construct a well-founded contradiction from an already-certified descent API without reopening the number-theoretic details.

A challenge can expose only

```lean
goldenZeroSectorDescentMeasure : GoldenZeroSectorDescentPacket → ℕ

GoldenZeroSectorDescentPacket.strictDescent :
  (p : GoldenZeroSectorDescentPacket) →
  Nonempty (GoldenZeroSectorStrictDescent p)
```

plus the certificate fields

```lean
next
measure_lt
```

and set the target to

```lean
(p : GoldenZeroSectorDescentPacket) → False.
```

Useful evaluation points are:

- choosing strong induction,
- connecting strict inequality to the induction-hypothesis index,
- proposition-level elimination of the `Nonempty` witness,
- rewriting the equality index `hq`,
- respecting the abstraction boundary instead of reproving arithmetic facts.

A further comparison could pit

1. a direct `Nat.strong_induction_on` solution, against
2. a generic `WellFounded` / measure-based solution,

allowing evaluation of reuse and abstraction quality in addition to proof length.

## Next declaration to read

The next declaration is not a theorem but a **`def`**:

```lean
def goldenZeroSectorDescentPacket_of_candidate
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorDescentPacket where
  base := ⟨p.r, p.s⟩
  t := 5 * p.c ^ 2
  D := p.d ^ 2
  ...
```

Declaration 0397 has established that a `GoldenZeroSectorDescentPacket` cannot exist. The next declaration shows that any original `GoldenZeroSectorCandidate` can be mapped into exactly such an impossible recursive packet.

Thus the next stage is the bridge

$$
\text{zero-sector candidate}
\longrightarrow
\text{descent packet}
\longrightarrow
\bot,
$$

connecting the closed descent engine back to the original FLT5 zero-sector candidate.

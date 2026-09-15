# 0399 `goldenZeroSectorCandidate_false`

## Declaration kind

`theorem`

This theorem excludes every `GoldenZeroSectorCandidate` by composing the candidate-to-descent-packet conversion from 0398 with the infinite-descent closure from 0397.

## Lean code

```lean
/-- The deterministic candidate emitted by inversion is impossible. -/
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

## Lean type

```lean
goldenZeroSectorCandidate_false :
  GoldenZeroSectorCandidate → False
```

Thus any assumption `p : GoldenZeroSectorCandidate` yields `False`.

Logically, this is an exclusion statement corresponding to

$$
\neg\,\exists p,\; p : \mathrm{GoldenZeroSectorCandidate}.
$$

## Mathematical meaning

`GoldenZeroSectorCandidate` packages the certified integer coordinates, tenth-power decompositions, coprimality, and norm conditions emitted by the zero-sector inversion.

0398 `goldenZeroSectorDescentPacket_of_candidate` turns such a candidate into a packet satisfying the recursive descent invariant:

$$
P(p):=\operatorname{goldenZeroSectorDescentPacket\_of\_candidate}(p).
$$

0397 `goldenZeroSectorDescentPacket_false` proves that every descent packet is impossible:

$$
q : \mathrm{GoldenZeroSectorDescentPacket}
\Longrightarrow
\bot.
$$

Therefore 0399 merely composes

$$
p
\longmapsto
P(p)
\longmapsto
\bot.
$$

No new divisibility calculation, golden-integer arithmetic, fifth-power splitting, or measure estimate occurs in this theorem. All such mathematics has already been completed before 0399.

## Role in the full proof

0399 is the **public final exclusion point** of the `SignedGoldenZeroSectorDescent` layer.

The immediately preceding chain is

$$
\mathrm{GoldenZeroSectorCandidate}
\xrightarrow{0398}
\mathrm{GoldenZeroSectorDescentPacket}
\xrightarrow{0397}
\bot.
$$

0397 is responsible for the general well-founded closure: a packet satisfying the recursive invariant cannot exist. 0398 is responsible for the arithmetic transport showing that the actual inversion candidate enters that invariant. 0399 joins those two APIs and eliminates the candidate type itself.

This separation is useful structurally. Well-founded infinite descent and the arithmetic transport from candidate to packet are certified independently, so the final exclusion reduces to one line of composition.

## Direct dependencies

The direct dependencies are very small:

- `GoldenZeroSectorCandidate`
- `goldenZeroSectorDescentPacket_of_candidate` — 0398
- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorDescentPacket_false` — 0397

The proof body effectively performs only the last two function applications.

Indirectly, 0399 inherits the entire dependency chain used by 0397 and 0398: zero-sector inversion, fifth-power re-entry, coprimality, power splitting, strict descent, and `Nat.strong_induction_on`. None of those ingredients is unfolded again here.

## Proof flow

The proof is entirely term-style.

1. Receive `p : GoldenZeroSectorCandidate`.
2. Apply 0398 to obtain

   ```lean
   goldenZeroSectorDescentPacket_of_candidate p
   ```

   of type `GoldenZeroSectorDescentPacket`.
3. Pass that packet to 0397:

   ```lean
   goldenZeroSectorDescentPacket_false
   ```

4. The result type is `False`, so the goal closes immediately.

At the type level, Lean sees

```lean
goldenZeroSectorDescentPacket_of_candidate p
  : GoldenZeroSectorDescentPacket
```

and

```lean
goldenZeroSectorDescentPacket_false
  : GoldenZeroSectorDescentPacket → False
```

so ordinary function composition is sufficient.

## Lean-specific handling

### Term proof without a tactic block

The theorem is written directly as

```lean
:=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

No `by`, `exact`, `rw`, or `simp` is needed. This is a particularly transparent Curry–Howard realization of

$$
A\to B,\quad B\to\bot
\quad\Rightarrow\quad
A\to\bot.
$$

### No coercion or implicit-argument repair

The output type of 0398 exactly matches the input type of 0397. Consequently, no cast, `simpa`, explicit type annotation, or namespace-level adapter is required. This is evidence that the preceding APIs have been aligned cleanly.

### Returning `False`

Rather than exposing only an outer negation, the theorem takes a concrete candidate `p` and returns `False`. Downstream receiver code can therefore eliminate a candidate immediately once it has constructed one.

## Redundancy and duplication

There is essentially no redundancy inside 0399. It is already the minimal composition of two existing declarations.

One could instead write

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False := by
  exact goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

but the current term-style proof is shorter and makes the dependency chain more explicit.

Using a generic combinator such as `Function.comp` would also be possible in principle, but would make this one-line proof less readable rather than more reusable.

## Optimization candidates

### 1. Keep the current implementation

For code size, readability, and dependency transparency, the present implementation is already close to optimal. There is no meaningful local simplification left.

### 2. API naming symmetry

If the descent layer were generalized for reuse, one could imagine a schematic interface such as

```lean
candidateToPacket
packetFalse
candidateFalse
```

but the current names preserve the mathematical object being manipulated and are preferable for FLT5 auditing.

### 3. Generic contradiction bridge

A helper of type

```lean
(A → B) → (B → False) → A → False
```

could encode the same pattern, but that helper would merely restate function composition. Introducing it only for 0399 would add abstraction without reducing mathematical complexity.

## Required Mathlib import and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

However, the proof term of 0399 does not directly invoke any specialized Mathlib theorem, tactic, or typeclass. It only requires `GoldenZeroSectorCandidate`, 0398, and 0397 to already be in scope.

From the theorem-local perspective, therefore, **no additional specialized Mathlib import is identifiable**. A minimally imported source module would still have to import the preceding local modules that define the candidate, packet, and the two bridge/exclusion declarations.

Because no Lean build is performed in this task, the exact smallest replacement for the broad `Mathlib` import has not been verified.

## Comparator challenge feasibility

**Feasible, but too easy as a standalone challenge.**

A minimal abstraction reduces to something like

```lean
variable {Candidate Packet : Type}
variable (toPacket : Candidate → Packet)
variable (packetFalse : Packet → False)

example (p : Candidate) : False :=
  packetFalse (toPacket p)
```

This is useful for checking elementary function application and type alignment, but it does not test any of the number theory of FLT5.

A better Comparator challenge would combine 0398 and 0399: construct the descent packet from the candidate fields and then feed it to the contradiction theorem. That version would exercise structure construction, natural/integer casts, power normalization, signed divisibility transport, and the final API composition.

## Next declaration to read

The next declaration is **0400 `GoldenZeroSectorArithmeticExclusion`**, whose kind is `abbrev`.

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

After 0399 closes the concrete `GoldenZeroSectorCandidate`, 0400 moves into the `SignedGoldenClosure` layer and exposes the arithmetic content as a receiver interface.
# 0396 `GoldenZeroSectorDescentPacket.strictDescent`

## Declaration kind

`theorem`

This theorem constructs an inhabitant of the `GoldenZeroSectorStrictDescent` structure defined in 0395 from any `GoldenZeroSectorDescentPacket`.

## Lean code

```lean
/--
Construct the next descent packet from a fifth root of the quadratic lift. The
new visible coordinate is the root's second coordinate; coprimality, the
fifth-power shape, and the norm condition are preserved, while
`fifthRoot_measure_lt` proves that its `|s|` measure strictly decreases.
-/
theorem GoldenZeroSectorDescentPacket.strictDescent
    (p : GoldenZeroSectorDescentPacket) :
    Nonempty (GoldenZeroSectorStrictDescent p) := by
  obtain ⟨gamma, hroot, hnorm⟩ := p.exists_lift_eq_fifthPower
  obtain ⟨u, v, hu, hv, hsnd, hH⟩ :=
    p.fifthRoot_power_split gamma hroot hnorm
  have hcop := p.fifthRoot_coprime_coords gamma hroot hnorm
  have h5norm : ¬ (5 : ℤ) ∣ goldenNorm gamma := by
    rw [hnorm]
    intro h
    exact p.five_not_dvd_D (by exact_mod_cast h)
  let next : GoldenZeroSectorDescentPacket := {
    base := gamma
    t := u
    D := v
    t_pos := hu
    D_pos := hv
    coprime_coords := hcop
    snd_eq := Or.inl hsnd
    H_eq := hH
    five_not_dvd_norm := h5norm }
  exact ⟨{
    next := next
    lift_eq := hroot
    measure_lt := p.fifthRoot_measure_lt gamma hroot }⟩
```

## Lean type

```lean
GoldenZeroSectorDescentPacket.strictDescent :
  (p : GoldenZeroSectorDescentPacket) →
  Nonempty (GoldenZeroSectorStrictDescent p)
```

For every descent packet `p`, the theorem returns the existence of at least one certified strict descent step starting from `p`.

Because the result is wrapped in `Nonempty`, the theorem exposes logical existence rather than a computational next-step function.

## Mathematical statement

Write `p.base = α`. By 0387 there exists a fifth root `γ` of the quadratic lift such that

$$
T(\alpha)=\gamma^5
$$

and

$$
N(\gamma)=D.
$$

By 0394, the second coordinate and quartic factor of this fifth root split again into fifth-power form:

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma)=v^5.
$$

Define

$$
next.base=\gamma,
\qquad
next.t=u,
\qquad
next.D=v.
$$

Then `next` again satisfies the complete `GoldenZeroSectorDescentPacket` invariant.

Moreover, 0393 gives

$$
\mu(next)<\mu(p),
$$

that is,

$$
|\gamma_{\mathrm{snd}}|<|p.base.snd|.
$$

Thus every recursive packet admits another packet of the same arithmetic shape with strictly smaller natural-valued measure.

## Role in the full proof

0396 compresses the local arithmetic of the zero-sector descent into a single object directly usable by well-founded induction.

The declarations 0387–0394 separately establish:

- existence of an honest fifth root,
- the product identity for the root's second coordinate,
- positivity of the quartic factor,
- positivity of the root's second coordinate,
- primitive coordinates,
- nondivisibility of the quartic factor by five,
- strict decrease of the visible measure,
- recovery of the recursive fifth-power shape.

0396 combines these ingredients to construct an actual transition

$$
p\longmapsto next
$$

and packages it as `GoldenZeroSectorStrictDescent p`.

The following theorem, `goldenZeroSectorDescentPacket_false`, can then invoke only this interface and `Nat.strong_induction_on`, without reopening the arithmetic details. Hence 0396 is the **constructor theorem connecting the arithmetic layer to the well-founded induction layer**.

## Direct dependencies

The principal direct dependencies are:

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorStrictDescent`
- `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`
- `GoldenZeroSectorDescentPacket.fifthRoot_power_split`
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`
- `goldenNorm`

In dependency order, 0396 is an aggregation point for the preceding descent lemmas, while 0395 supplies the record type into which the result is packaged.

## Proof flow

1. Use `exists_lift_eq_fifthPower` to obtain

   ```lean
   gamma : GoldenInt
   hroot : goldenZeroSectorLift p.base = goldenPow gamma 5
   hnorm : goldenNorm gamma = (p.D : ℤ)
   ```

2. Use `fifthRoot_power_split` to obtain positive naturals `u, v` and

   $$
   \gamma.snd=5u^5,
   \qquad
   H(\gamma)=v^5.
   $$

3. Use `fifthRoot_coprime_coords` to recover

   $$
   \gcd(|\gamma.fst|,|\gamma.snd|)=1.
   $$

4. Transport `p.five_not_dvd_D` through `hnorm` to prove

   $$
   5\nmid N(\gamma).
   $$

5. Build `next : GoldenZeroSectorDescentPacket` from `gamma`, `u`, `v`, and the recovered invariants.

6. Store `hroot` in `lift_eq`, and use 0393 `fifthRoot_measure_lt` for `measure_lt`.

7. Wrap the resulting structure in `Nonempty`.

## Fields of the new packet

```lean
let next : GoldenZeroSectorDescentPacket := {
  base := gamma
  t := u
  D := v
  t_pos := hu
  D_pos := hv
  coprime_coords := hcop
  snd_eq := Or.inl hsnd
  H_eq := hH
  five_not_dvd_norm := h5norm }
```

The essential point is that `next` is not merely a smaller integer pair. It satisfies the full recursive invariant of the source packet.

`base := gamma` makes the fifth root itself the next base, while `t := u` and `D := v` re-encode the fifth-power splitting obtained in 0394.

`snd_eq := Or.inl hsnd` selects the positive branch `gamma.snd = 5*u^5`. Because 0390 has already established `gamma.snd > 0`, the negative branch is not needed here.

## Lean-specific processing

### `obtain`

```lean
obtain ⟨gamma, hroot, hnorm⟩ := p.exists_lift_eq_fifthPower
```

and

```lean
obtain ⟨u, v, hu, hv, hsnd, hH⟩ := ...
```

destruct existential packages immediately, keeping the later record construction readable.

### `exact_mod_cast`

After rewriting by `hnorm`, the proof must move from integer divisibility

```lean
(5 : ℤ) ∣ (p.D : ℤ)
```

to natural-number divisibility

```lean
5 ∣ p.D
```

in order to contradict `p.five_not_dvd_D`. `exact_mod_cast` performs this transport.

### `let next`

The next packet is defined locally before constructing the outer strict-descent record. This avoids one large nested record literal and makes the proof boundary clearer.

### `Nonempty`

Returning

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

allows the following closure theorem to extract the witness simply by

```lean
obtain ⟨step⟩ := q.strictDescent
```

without exposing a computational choice function.

## Redundancy and duplication

The theorem is already compact and mainly assembles existing APIs.

The clearest repeated pattern is

```lean
have h5norm : ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  rw [hnorm]
  intro h
  exact p.five_not_dvd_D (by exact_mod_cast h)
```

This is a simple transport of `p.five_not_dvd_D` across `hnorm`. If the same pattern appears elsewhere, it could be extracted into a helper such as

```lean
five_not_dvd_norm_of_norm_eq_D
```

The explicit `next` record literal, however, has auditing value: it makes visible exactly which theorem supplies each invariant. Aggressive automation here would reduce transparency.

## Optimization candidates

A natural refactoring would separate construction of the next packet from construction of the strict-descent certificate.

Conceptually one could define

```lean
def GoldenZeroSectorDescentPacket.ofFifthRoot
    (p : GoldenZeroSectorDescentPacket)
    (gamma : GoldenInt)
    ... : GoldenZeroSectorDescentPacket := ...
```

Then `strictDescent` would only need to connect fifth-root extraction with strict measure decrease.

At present, however, the theorem is short enough that the explicit form clearly shows where each invariant comes from. Such an abstraction becomes more compelling only if the same constructor pattern is reused in other descent developments.

Also note that `h5norm` is not the same property as 0392 `fifthRoot_five_not_dvd_H`: here the required invariant concerns `goldenNorm gamma`, not the quartic factor. Over-unifying these two facts would obscure the dependency structure.

## Required Mathlib imports and import optimization

The standalone source currently uses

```lean
import Mathlib
```

for the whole generated development.

The Mathlib-level features directly visible in 0396 are mainly:

- `Nonempty`,
- existential pattern matching,
- `rw`,
- `exact_mod_cast`.

The heavy arithmetic has already been encapsulated in preceding DkMath theorems, so the theorem itself has comparatively light direct requirements.

Nevertheless, the module must import the definitions of `GoldenZeroSectorDescentPacket`, `GoldenZeroSectorStrictDescent`, and the fifth-root lemmas. Because no Lean build is performed in this run, the exact minimal Mathlib import cannot be certified here.

For import optimization, the natural route is to import only the DkMath module corresponding to `SignedGoldenZeroSectorDescent` and then add the tactic support required by `exact_mod_cast`, verifying the result separately with Lean.

## Comparator challenge suitability

**Highly suitable.**

0395 alone is only a structure declaration. In contrast, 0396 requires correct composition of several existing APIs and construction of a dependent record.

A Comparator challenge can expose the following as permitted lemmas:

- `exists_lift_eq_fifthPower`,
- `fifthRoot_power_split`,
- `fifthRoot_coprime_coords`,
- `five_not_dvd_D`,
- `fifthRoot_measure_lt`.

The target is then

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

The challenge tests:

- decomposition of existential witnesses,
- correct relocation of invariants,
- divisibility transport between `ℕ` and `ℤ`,
- dependent structure construction,
- reuse of the strict measure theorem.

Thus **0395+0396 together** form a strong challenge for evaluating descent-API composition.

## Next declaration to read

The next declaration is

```lean
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

Because 0396 has established that every packet produces a strictly smaller packet of the same recursive type, the next theorem can close the contradiction using only strong induction on the natural-valued measure, without reopening the arithmetic proof.

The logical flow is

$$
\text{recursive packet}
\longrightarrow
\text{strictly smaller recursive packet}
\longrightarrow
\text{well-founded contradiction}.
$$

The next declaration is therefore the logical closure of the zero-sector infinite descent.
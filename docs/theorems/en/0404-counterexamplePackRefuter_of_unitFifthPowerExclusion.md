# 0404 `counterexamplePackRefuter_of_unitFifthPowerExclusion`

## Declaration kind

`theorem`

## Lean type

```lean
/-- The unit-times-fifth-power exclusion closes every primitive packet unconditionally. -/
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

## Mathematical statement and meaning

This theorem shows that once the golden-order exclusion

```lean
SignedGoldenUnitFifthPowerExclusion
```

is available, every primitive FLT5 counterexample packet can be refuted.

In other words,

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}.
$$

Expanding `CounterexamplePackRefuter`, the conclusion is

$$
\forall x,y,z\in\mathbb N,
\quad
\mathrm{CounterexamplePack}(x,y,z)\to\bot.
$$

`SignedGoldenUnitFifthPowerExclusion` is the receiver contract that rules out a ramifier-stripped packet whose golden factor `beta` has the form

$$
\beta=\varepsilon\gamma^5
$$

with `epsilon` a unit.

On the other hand, `branchB_false_of_unitFifthPowerExclusion` turns a primitive packet with the clean gap orientation

$$
5\nmid(z-y)
$$

directly into a contradiction from that exclusion.

An arbitrary primitive packet need not initially satisfy `5 \nmid (z-y)`. The immediately preceding theorem `CounterexamplePack.branchB_orientation` guarantees

$$
5\nmid(z-y)
\quad\text{or}\quad
5\nmid(z-x).
$$

In the first case, the original packet `p` is sent directly to the Branch-B refuter. In the second case, the proof swaps the two left inputs and sends `p.swap`. The Branch-B gap of the swapped packet is exactly the original `z-x`, so the same Branch-B theorem can be reused in both orientations.

Thus the mathematical routing is

$$
\mathrm{primitive\ packet}
\xrightarrow{\text{orientation}}
\begin{cases}
5\nmid(z-y), & p,\\
5\nmid(z-x), & p.swap,
\end{cases}
\xrightarrow{\text{Branch B exclusion}}
\bot.
$$

## Role in the overall proof

This theorem is a closure theorem that lifts the local Branch-B contradiction to a refuter for all primitive FLT5 packets.

Architecturally, it connects the boundary

$$
\text{golden unit/fifth-power exclusion}
\longrightarrow
\text{routed Branch-B contradiction}
\longrightarrow
\text{primitive packet refuter}.
$$

The preceding declaration 0403 `CounterexamplePackRefuter` only named the type of a proof capable of refuting every primitive packet. Declaration 0404 provides the first concrete inhabitant of that type.

The theorem itself performs no new 5-adic calculation, golden-integer calculation, or infinite descent. All such arithmetic has already been established earlier. Its sole job is to route the two possible gap orientations to the already proved refuter.

The immediately following theorem

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
```

then constructs `SignedGoldenUnitFifthPowerExclusion` itself from

- `GoldenUnitClassesModFifth`, and
- `GoldenZeroSectorArithmeticExclusion`,

and feeds the result into 0404. Hence 0404 is a reusable adapter in the middle of the closure chain.

## Direct dependencies

### `SignedGoldenUnitFifthPowerExclusion`

This is the type of the input `hExclude`.

Conceptually, for every stripped packet `p` and golden integers `epsilon`, `gamma`, it says that

$$
\epsilon\text{ is a unit},
\qquad
p.beta=\epsilon\gamma^5
$$

implies `False`.

Declaration 0404 does not inspect the internal proof of this contract; it simply forwards the contract to the existing Branch-B refuter.

### `CounterexamplePackRefuter`

The conclusion type defined in 0403:

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

The opening

```lean
intro x y z p
```

works because this `abbrev` reduces to the quantified function type above.

### `CounterexamplePack.branchB_orientation`

The immediately preceding routing theorem:

```lean
p.branchB_orientation :
  ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x
```

This directly supplies the two cases used in 0404.

### `branchB_false_of_unitFifthPowerExclusion`

The Branch-B contradiction theorem. Earlier in the canonical Lean source it is defined as

```lean
theorem branchB_false_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False :=
  branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_unitFifthPowerExclusion hExclude) hPack hBranch
```

Declaration 0404 reuses this theorem in both orientations.

### `CounterexamplePack.swap`

This is the left-input symmetry used in the second branch.

If the original packet has type

```lean
CounterexamplePack x y z
```

then `p.swap` has type

```lean
CounterexamplePack y x z
```

so the original condition

$$
5\nmid(z-x)
$$

moves into exactly the `z-y'` position required by the Branch-B theorem after swapping.

The construction of `swap` itself is not repeated here; 0404 relies on the previously exposed packet API.

## Proof flow

### 1. Introduce the quantified refuter arguments

```lean
intro x y z p
```

Because `CounterexamplePackRefuter` is a reducible `abbrev`, Lean can treat the goal as

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

and fix an arbitrary primitive packet

```lean
p : CounterexamplePack x y z.
```

### 2. Split on the orientation theorem

```lean
rcases p.branchB_orientation with hyGap | hxGap
```

The two hypotheses are

```lean
hyGap : ¬ 5 ∣ z - y
```

or

```lean
hxGap : ¬ 5 ∣ z - x.
```

### 3. Close the first orientation directly

```lean
exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
```

The Branch-B theorem already expects the gap `z-y`, so no conversion is needed.

### 4. Swap the packet in the second orientation

```lean
exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

After swapping the left inputs, the Branch-B theorem sees the original `z-x` as its own `z-y` gap.

This is the key design point of the proof: rather than maintaining separate Branch-B refuters for the two orientations, symmetry is packaged into the packet API and one theorem is used twice.

## Lean-specific processing

### Automatic unfolding of the `abbrev` conclusion

Although the goal is named `CounterexamplePackRefuter`, the proof starts immediately with

```lean
intro x y z p.
```

This is possible because `CounterexamplePackRefuter` is an `abbrev`, so the elaborator may reduce it to

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False.
```

### `rcases ... with ... | ...`

```lean
rcases p.branchB_orientation with hyGap | hxGap
```

is tactic syntax for eliminating an `Or` while naming the hypothesis in each resulting branch.

Mathematically it is an ordinary case split; Lean's syntax makes both branch assumptions explicit in one line.

### Dependent indices and `p.swap`

The packet is indexed:

```lean
p : CounterexamplePack x y z.
```

After swapping,

```lean
p.swap : CounterexamplePack y x z.
```

The parameters `{x y z}` of `branchB_false_of_unitFifthPowerExclusion` are implicit, so Lean re-infers them from `p.swap`. Consequently

```lean
hxGap : ¬ 5 ∣ z - x
```

matches the required Branch-B hypothesis for the swapped packet without an explicit rewrite or `simpa`.

This dependent-index inference is one of the technically interesting Lean aspects of an otherwise short proof.

### Terminal `exact` applications

Both branches are closed by applying an existing theorem whose result is exactly `False`. No additional normalization or arithmetic tactic is needed.

## Redundancy and overlap

The proof is extremely short and contains little local redundancy.

The two branches repeat

```lean
branchB_false_of_unitFifthPowerExclusion hExclude ... ...
```

but differ precisely in `p` versus `p.swap` and `hyGap` versus `hxGap`. Since the mathematical structure itself is a two-way routing, keeping both applications explicit is highly readable.

Factoring this repetition would require a helper that packages an oriented packet together with its gap certificate; that abstraction would likely cost more than the four-line proof it replaces.

There are several thin adapter theorems around this part of the closure layer, including `branchB_false_of_unitFifthPowerExclusion` itself, which routes through `signedBranchARefuter_of_unitFifthPowerExclusion`. This is better viewed as an intentional receiver-boundary design than accidental duplication: each layer remains independently reusable and auditable.

## Optimization candidates

### Prefer the current explicit two-branch proof

The present form is already close to minimal and directly communicates the mathematics:

```lean
p.branchB_orientation
```

chooses a gap, while

```lean
p.swap
```

normalizes the second orientation to the first.

### Package orientation as a routed packet

In principle, the preceding theorem could instead return a dependent witness such as a routed packet together with a clean-gap certificate. Then 0404 could apply the Branch-B theorem only once.

However, such an existential/dependent package would make the relation to the original `x` and `y` less transparent. The current `Or` plus `swap` API is simpler.

### Generic symmetric router

If the same pattern — left condition or right condition, normalized by swapping — appears repeatedly across other exponents or branches, a generic routing lemma could become worthwhile.

For 0404 alone, introducing such an abstraction would not improve the code.

## Required Mathlib imports

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

The body of 0404 directly relies mainly on

- elimination of `Or`,
- `rcases`,
- implicit-argument inference, and
- previously defined DkMath declarations.

It does not directly invoke arithmetic or algebra tactics.

The heavier Mathlib dependencies live in the declarations that 0404 consumes:

- `CounterexamplePack`,
- `SignedGoldenUnitFifthPowerExclusion`,
- `CounterexamplePack.branchB_orientation`,
- `branchB_false_of_unitFifthPowerExclusion`, and
- `CounterexamplePack.swap`.

According to the standalone manifest, 0404 belongs to `DkMath/FLT/Five/SignedGoldenClosure.lean` and consumes public APIs established in earlier modules such as `SignedGoldenUnitClasses.lean`.

### Import optimization candidate

`import Mathlib` is not intrinsically required by this four-line theorem itself.

In the modular DkMath source, `SignedGoldenClosure.lean` could potentially import only the DkMath modules it directly needs and whatever narrower Mathlib modules those dependencies require.

No Lean build is performed in this task, so the exact minimal Mathlib import set has not been verified. Therefore no specific fine-grained Mathlib module is asserted here as the proven minimum.

## Comparator challenge suitability

**Suitable, and more useful than 0403 by itself.**

Although short, the theorem exercises several nontrivial interface features:

1. unfolding an `abbrev` conclusion,
2. eliminating an `Or`,
3. transforming a dependent packet with `swap`,
4. re-inferring implicit indices, and
5. routing both cases through the same refuter theorem.

A natural Comparator challenge would provide

```lean
hExclude : SignedGoldenUnitFifthPowerExclusion
p : CounterexamplePack x y z
```

plus the required APIs and ask the model to prove

```lean
False.
```

The difficulty is low to moderate. It is primarily a test of Lean interface composition and dependent elaboration rather than deep number-theoretic search.

For a cleaner challenge, hide the completed theorem `counterexamplePackRefuter_of_unitFifthPowerExclusion` itself and expose only

- `branchB_orientation`,
- `branchB_false_of_unitFifthPowerExclusion`, and
- `CounterexamplePack.swap`,

then ask for the closure proof to be reconstructed.

## Next declaration to read

The next declaration is

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

Declaration 0404 provides

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}.
$$

The next theorem constructs that input `SignedGoldenUnitFifthPowerExclusion` from

$$
\mathrm{GoldenUnitClassesModFifth}
$$

and

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}.
$$

Thus the next stage composes the higher-level receiver chain

$$
(\text{unit classification})
+
(\text{zero-sector arithmetic})
\longrightarrow
\text{all primitive packets are impossible}.
$$

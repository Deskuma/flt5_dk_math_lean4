# 0401 `signedGoldenZeroSectorExclusion_of_arithmetic`

## Declaration kind

`theorem`

This theorem is the receiver bridge that converts the raw zero-sector arithmetic exclusion proposition exposed by 0400 `GoldenZeroSectorArithmeticExclusion` into the upstream interface `SignedGoldenZeroSectorExclusion` required by the signed-golden proof layer.

It proves no new number theory by itself. Instead, it takes the norm identity, signed product identity, primitive-coordinate property, and tenth-power split already proved for the signed ramifier-stripped packet, and feeds them to 0400 in exactly the order required by its interface.

## Lean code

```lean
/-- The exact quartic/tenth-power proposition is sufficient for the zero sector. -/
theorem signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion := by
  intro u v w p gamma hbeta
  exact hArithmetic gamma.fst gamma.snd
    p.exceptional.powerSplit.a p.exceptional.powerSplit.b
    p.exceptional.powerSplit.a_pos p.exceptional.powerSplit.b_pos
    p.exceptional.powerSplit.coprime_a_b p.five_not_dvd_b
    (p.zeroSector_gamma_norm_eq_or_eq_neg hbeta)
    (p.zeroSector_snd_factor_eq hbeta)
    (p.zeroSector_coprime_coords hbeta)
    (p.zeroSector_tenthPower_split hbeta)
```

## Lean type

The declaration has type

```lean
signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion
```

Logically, it is the implication

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\mathrm{SignedGoldenZeroSectorExclusion}.
$$

0400 `GoldenZeroSectorArithmeticExclusion` is a function-shaped proposition saying that, for integer coordinates $r,s$ and natural parameters $a,b$, positivity, coprimality, non-divisibility by $5$, a signed norm identity, a quartic product identity, primitive coordinates, and a tenth-power split jointly imply `False`.

0401 proves that all of those raw hypotheses are available from the packet and fifth-power data introduced by `SignedGoldenZeroSectorExclusion`.

## Mathematical statement

Let the zero-sector data supplied by `SignedGoldenZeroSectorExclusion` be represented by $(p,\gamma)$, with golden-integer coordinates

$$
\gamma=(r,s).
$$

The packet `p` already supplies the natural parameters $a,b$ together with

$$
a>0,\qquad b>0,
$$

$$
\gcd(a,b)=1,
$$

$$
5\nmid b.
$$

From the zero-sector fifth-power relation `hbeta`, existing lemmas provide four further facts.

1. Signed norm identification:

$$
N(\gamma)=b
\quad\text{or}\quad
N(\gamma)=-b.
$$

2. The second-coordinate/quartic-factor product identity:

$$
s\,H(r,s)=-5^6a^{10}.
$$

3. Primitive coordinates:

$$
\gcd(|r|,|s|)=1.
$$

4. Tenth-power splitting: there exist $c,d\in\mathbb N$ such that

$$
|s|=5^6c^{10},
$$

$$
|H(r,s)|=d^{10}.
$$

These are exactly the hypotheses expected by 0400. Applying `hArithmetic` therefore yields `False` immediately.

The mathematical flow is thus

$$
\text{signed-golden zero-sector packet}
\Longrightarrow
\text{the raw arithmetic hypotheses of 0400}
\Longrightarrow
\bot.
$$

## Role in the whole proof

0401 is a **receiver adapter** in the proof architecture.

By 0397--0399, the concrete zero-sector infinite descent has already been closed for `GoldenZeroSectorCandidate` and `GoldenZeroSectorDescentPacket`. 0400 then exposed that arithmetic core as a structure-independent proposition.

0401 reconnects that public arithmetic API to the higher signed-golden packet layer:

$$
\text{zero-sector arithmetic}
\xrightarrow{0400}
\texttt{GoldenZeroSectorArithmeticExclusion}
\xrightarrow{0401}
\texttt{SignedGoldenZeroSectorExclusion}.
$$

Because of this boundary, later closure theorems do not need to know any of the internal mechanics of the infinite descent. They only need an inhabitant of `SignedGoldenZeroSectorExclusion`.

Thus 0401 is the glue that keeps the arithmetic proof layer and the structural FLT5 closure layer loosely coupled.

## Direct dependencies

### Types and definitions

- `GoldenZeroSectorArithmeticExclusion`
  - the raw arithmetic receiver contract defined in 0400.
- `SignedGoldenZeroSectorExclusion`
  - the upstream interface excluding the signed-golden zero sector.
- `GoldenInt`
  - the golden-integer representation whose coordinates are accessed as `gamma.fst` and `gamma.snd`.

### Packet fields and theorems used directly

- `p.exceptional.powerSplit.a`
- `p.exceptional.powerSplit.b`
- `p.exceptional.powerSplit.a_pos`
- `p.exceptional.powerSplit.b_pos`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

These provide $a,b$ and

$$
a>0,\quad b>0,\quad \gcd(a,b)=1,\quad 5\nmid b.
$$

### Zero-sector lemmas depending on `hbeta`

- `p.zeroSector_gamma_norm_eq_or_eq_neg hbeta`
- `p.zeroSector_snd_factor_eq hbeta`
- `p.zeroSector_coprime_coords hbeta`
- `p.zeroSector_tenthPower_split hbeta`

They correspond exactly to the remaining four hypotheses of 0400.

No arithmetic tactic appears in the proof body of 0401; the theorem only connects results already proved upstream.

## Proof flow

Although the Lean proof is short, its dependency flow is precise.

1. Receive `hArithmetic : GoldenZeroSectorArithmeticExclusion`.
2. Expand the target `SignedGoldenZeroSectorExclusion` by introducing

```lean
intro u v w p gamma hbeta
```

3. Pass `gamma.fst` and `gamma.snd` as the integer coordinates $r,s$ required by 0400.
4. Extract $a,b$, positivity, and coprimality from `p.exceptional.powerSplit`.
5. Pass `p.five_not_dvd_b`.
6. Derive and pass the signed norm statement from `hbeta`.
7. Derive and pass the signed quartic product identity from `hbeta`.
8. Derive and pass coordinate coprimality from `hbeta`.
9. Derive and pass the existential tenth-power split from `hbeta`.
10. The resulting `False` is exactly the target conclusion.

The proof is essentially one curried function application.

## Lean-specific processing

### `intro u v w p gamma hbeta`

`SignedGoldenZeroSectorExclusion` is a long function-shaped proposition, so `intro` introduces its quantified data and hypotheses in order.

The variables `u v w` are not referenced directly in the body of 0401. Their relevant arithmetic consequences have already been packaged into `p` and the relation `hbeta`.

### Curried application

Because `hArithmetic` is a proposition represented as an iterated function type rather than a structure value, Lean permits

```lean
exact hArithmetic gamma.fst gamma.snd
  ...
```

with each argument and hypothesis supplied successively.

The use of `abbrev` for 0400 helps here: no explicit

```lean
unfold GoldenZeroSectorArithmeticExclusion
```

is required.

### Nested projections

Expressions such as

```lean
p.exceptional.powerSplit.a
```

extract already-certified arithmetic witnesses from nested proof packets.

Lean tracks the type of every projection, so mixing up the two power-split factors or applying a coprimality fact to the wrong pair would be rejected by the kernel.

### Exact type alignment

Terms such as

```lean
p.zeroSector_gamma_norm_eq_or_eq_neg hbeta
```

already have exactly the types demanded by 0400. Therefore no `simpa`, `rw`, or coercion handling is needed in 0401.

This is evidence that the interfaces between the preceding modules were designed to fit cleanly.

## Redundancy and overlap

The theorem itself contains very little redundancy.

The main maintenance coupling is the long positional argument list passed to `hArithmetic`. If the hypothesis order of 0400 changes, 0401 must change with it.

The repeated projection prefix

```lean
p.exceptional.powerSplit.a
p.exceptional.powerSplit.b
p.exceptional.powerSplit.a_pos
p.exceptional.powerSplit.b_pos
p.exceptional.powerSplit.coprime_a_b
```

is also visually repetitive.

A local alias such as

```lean
let q := p.exceptional.powerSplit
```

could shorten the code, but the current form makes provenance explicit. For a small auditing bridge theorem, that explicitness is arguably preferable.

## Optimization candidates

### 1. Keep the direct adapter

0401 is already close to minimal. Rewriting it into a tactic-heavy proof would not improve either proof search or readability.

### 2. Bundle the raw arithmetic hypotheses only if reused

If several future receivers need exactly the same list of assumptions as 0400, one could introduce a bundle such as

```lean
structure GoldenZeroSectorArithmeticData where
  r s : ℤ
  a b : ℕ
  ...
```

and express the exclusion as

```lean
GoldenZeroSectorArithmeticData → False
```

At present, however, 0400's lightweight `abbrev` and 0401's single direct use make such a structure potentially over-engineered.

### 3. Alias the power-split packet

Giving `p.exceptional.powerSplit` a local name may improve visual compactness, but this is a style choice rather than a substantive optimization.

### 4. Preserve exact interface matching

One particularly good property of 0401 is that it requires no casts, rewriting, or simplification. Future upstream refactors should preferably preserve this direct-fit property.

## Required Mathlib imports and import optimization

The standalone source currently uses

```lean
import Mathlib
```

0401 itself directly uses only

- `intro`,
- `exact`,
- structure projections,
- theorem application.

Thus its proof body has essentially no direct dependency on specialized Mathlib tactics.

Its type, however, depends on the internal FLT5 declarations `GoldenZeroSectorArithmeticExclusion`, `SignedGoldenZeroSectorExclusion`, the packet types, and golden-integer definitions. In the modular source, those internal FLT5 modules are therefore the essential imports.

The standalone artifact alone does not determine the exact smallest set of individual Mathlib imports below `Mathlib`, and no Lean build is performed here. The strict minimal import set is therefore unverified.

If import minimization is desired, the safer strategy is to import only the directly preceding FLT5 module(s) and rely on their transitive Mathlib dependencies, rather than guessing fine-grained Mathlib modules from this short proof body.

## Comparator challenge suitability

**Suitable, but easy as a standalone challenge.**

0401 is better suited to testing **interface matching** than deep proof search.

A challenge can provide only

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

and the goal `SignedGoldenZeroSectorExclusion`.

The model must discover the nested packet fields and the theorems depending on `hbeta`, then supply them to 0400 in the correct order.

Useful evaluation points are:

- locating the correct nested projections,
- selecting the `hbeta`-dependent zero-sector lemmas,
- correctly matching $a,b,r,s$,
- avoiding unnecessary algebra or coercion work.

A harder variant would unfold 0400 and expose only the long raw function type, requiring the model to reconstruct the bridge from the available theorem environment.

As a challenge of mathematical discovery, however, 0401 is weak. Its value lies in architectural correctness rather than difficult local reasoning.

## Technical meaning

The key contribution of 0401 is not a new identity.

It fixes, at kernel level, that the zero-sector arithmetic exclusion proved downstream can be converted **without loss of information** into the exact type expected by the upstream signed-golden closure.

Conceptually, it realizes the final arrow in

$$
\text{descent arithmetic}
\leftrightarrow
\text{raw receiver assumptions}
\longrightarrow
\text{signed zero-sector exclusion}.
$$

Thin adapter theorems of this kind can look obvious informally, but they are important in a large formalization: they make explicit which information crosses a module boundary and prevent hidden assumptions or accidental circular dependencies from entering the proof.

## Next declaration to read

The next declaration is 0402 `CounterexamplePack.branchB_orientation`.

Its declaration kind is `theorem`.

```lean
theorem CounterexamplePack.branchB_orientation
    {x y z : ℕ} (p : CounterexamplePack x y z) :
    ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x := by
  ...
```

After 0401 completes the zero-sector receiver bridge, `SignedGoldenClosure` next proves that every primitive FLT5 packet has at least one gap orientation satisfying the Branch B condition:

$$
5\nmid(z-y)
\quad\text{or}\quad
5\nmid(z-x).
$$

This is the routing lemma that begins reconnecting zero-sector exclusion to the elimination of an actual primitive counterexample.

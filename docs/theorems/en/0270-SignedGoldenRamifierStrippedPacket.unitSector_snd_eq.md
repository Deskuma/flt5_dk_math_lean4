# 0270 — `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq`

## Declaration kind

This is a `theorem`.

Its fully qualified name is `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq`, and it is placed as a packet-level theorem for `SignedGoldenRamifierStrippedPacket`.

## Lean type

```lean
theorem SignedGoldenRamifierStrippedPacket.unitSector_snd_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} {gamma : GoldenInt}
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) :
    (goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd =
      -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  rw [← hbeta, p.beta_snd]
```

The type says that if `p.beta` is represented as the product of the finite unit-sector representative `goldenPhi ^ i` and a fifth power `gamma ^ 5`, then the second coordinate of that product is exactly the five-adic coordinate already stored by the packet,

$$
-5^7 a^{10},
$$

where $a$ is

```lean
p.exceptional.powerSplit.a
```

in the Lean structure.

Because `i : Fin 5`, the sector index is restricted to $0,1,2,3,4$. The theorem itself does not perform a case split on these five sectors. It uses only the equality `hbeta` identifying the sector expression with `p.beta`.

## Mathematical statement

Suppose the golden integer `beta` has a finite unit-sector representation

$$
\beta=\varphi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}.
$$

The construction of `SignedGoldenRamifierStrippedPacket` has already retained the exact second-coordinate identity

$$
\operatorname{snd}(\beta)
=-5^7a^{10}.
$$

Taking second coordinates of the equality therefore gives immediately

$$
\operatorname{snd}(\varphi^i\gamma^5)
=-5^7a^{10}.
$$

Thus the theorem does not introduce a new polynomial identity. Its purpose is to transport a previously established packet invariant into the finite unit-sector representation used by the later arithmetic.

## Role in the complete proof

Theorems 0264–0268 computed the second coordinates obtained by multiplying

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

by a fifth power. Writing `gamma^5 = A + Bφ`, those coordinates are

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B.
$$

Theorem 0269 `golden_neg_unit_mul_fifth_snd` then reduced negative unit representatives to sign changes of the positive representatives.

The present theorem is the first direct connection between that finite-sector arithmetic and the five-adic invariant stored in `SignedGoldenRamifierStrippedPacket`.

On the packet side one has

$$
\operatorname{snd}(\beta)=-5^7a^{10},
$$

while on the sector side one has a representation `beta = φ^i γ^5`. This theorem identifies the two descriptions at the level of the second coordinate.

Later nonzero-sector exclusions can therefore combine the explicit formulas from 0264–0268 with the right-hand side of this theorem. That pushes divisibility by $5$ into combinations of `goldenFifthFstPoly` and `goldenFifthSndPoly`, after which the proof can force a contradiction with the norm-side conditions. In this sense 0270 is the attachment point between coordinate arithmetic and the packet's five-adic invariant.

## Direct dependencies

Only a small set of definitions and facts is used directly by the proof.

- `SignedGoldenRamifierStrippedPacket`
  - The exceptional packet after one visible ramifier `tau` has been removed.
  - It stores `beta : GoldenInt`, `exceptional`, and the exact coordinate field `beta_snd`.
- `SignedGoldenRamifierStrippedPacket.beta_snd`
  - This is a structure field rather than a separately proved theorem.
  - In the canonical source it has the form

```lean
beta_snd : beta.snd =
  -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
```

- `GoldenInt`
  - The coordinate model for golden integers $a+b\varphi$.
- `goldenPhi`
  - The `GoldenInt` representative of $\varphi$.
- `goldenPow`
  - The project API for natural powers in `GoldenInt`.
- `goldenMul`
  - The project API for multiplication in `GoldenInt`.
- `Fin 5`
  - Restricts the unit-sector index to the five residue representatives.
- The hypothesis `hbeta`
  - The bridge equality identifying the packet's `beta` with the unit-sector fifth-power expression.

Notably, the proof script does not directly invoke the individual sector theorems 0259–0269. Those become relevant later when `i` is specialized and the corresponding concrete sector formula is expanded. The present theorem only transports the packet invariant.

## Proof flow

The proof consists of one line:

```lean
rw [← hbeta, p.beta_snd]
```

The first rewrite

```lean
rw [← hbeta]
```

replaces the left-hand expression

```lean
(goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd
```

with `p.beta.snd`.

The hypothesis has the orientation

```lean
hbeta : p.beta = sectorExpression
```

so the reverse rewrite `← hbeta` is required in order to turn the sector expression back into the packet object.

The goal then becomes essentially

```lean
p.beta.snd =
  -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

and

```lean
rw [p.beta_snd]
```

closes it using the exact coordinate field stored in the packet.

No `ring`, `omega`, `norm_num`, sector enumeration, or case split is needed.

## Lean-specific processing

The important Lean detail is the direction of rewriting.

`hbeta` points from the packet object to the sector expression, while the goal is phrased in terms of the sector expression's `.snd`. Consequently the useful rewrite is `rw [← hbeta]`, not `rw [hbeta]`.

It is also notable that the proof does not explicitly apply

```lean
congrArg (fun x => x.snd)
```

to `hbeta`. Lean rewriting descends into the expression under the projection, so replacing the underlying `sectorExpression` by `p.beta` automatically turns

```lean
sectorExpression.snd
```

into

```lean
p.beta.snd
```

After that, the structure field `p.beta_snd` exactly matches the remaining goal. The theorem is therefore easy not because the mathematical information is weak, but because the earlier packet design stored the invariant in exactly the form needed by downstream rewriting.

## Redundancy and duplication

There is essentially no redundancy inside the theorem. The two rewrites have distinct roles:

1. `← hbeta` moves from the representation back to the packet object.
2. `p.beta_snd` reads the exact five-adic coordinate from the packet.

One could inline these two rewrites directly in every later sector proof. However, naming this bridge as `unitSector_snd_eq` creates a useful abstraction boundary: downstream arithmetic can consume the statement “the sector expression has the fixed five-adic second coordinate” without depending on how `SignedGoldenRamifierStrippedPacket` was constructed.

Thus the theorem removes conceptual duplication even though its own proof is only one line.

## Optimization candidates

The current proof is already close to minimal, so code-length optimization offers little benefit.

A possible alternative would be some `simpa` formulation such as

```lean
simpa [hbeta] using p.beta_snd
```

or a variant with an explicitly reversed equality. Whether that exact version is accepted depends on simplifier orientation and has not been build-checked in this task.

The existing

```lean
rw [← hbeta, p.beta_snd]
```

is more explicit about the two logical transports and is likely preferable for proof auditing.

A more abstract design could introduce a generic lemma saying that for arbitrary `x : GoldenInt`, if `p.beta = x`, then `x.snd` equals the stored coordinate. Such a lemma would be mathematically valid, but it would erase the useful semantic fact that the representation here is specifically a `Fin 5` unit sector times a fifth power. The current theorem's specialization therefore carries useful downstream meaning.

## Required Mathlib imports and import optimization

The checked standalone artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the combined generated development.

This theorem itself needs very little from Lean/Mathlib directly. Its proof relies mainly on

- equality rewriting (`rw`),
- `Fin 5`,
- `Nat` and `Int`,
- and the project-side definitions of `GoldenInt` and `SignedGoldenRamifierStrippedPacket`.

It does not use `ring`, `omega`, or other heavier tactics.

The standalone artifact concatenates many generated source modules, and the exact import declaration of the original `SignedGoldenSectorArithmetic.lean` module was not available as a separate file in the repository state inspected here. Therefore a precise minimal Mathlib import cannot be claimed without a Lean build.

A likely optimization would be to import only the project modules providing `SignedGoldenRamifierStrippedPacket`, golden-unit/fifth-power APIs, and the basic finite/equality infrastructure they require. The exact minimal set remains unverified.

## Comparator challenge suitability

Yes. The theorem is easy mathematically, but it is useful as a proof-engineering comparator.

The challenge can present the original goal:

```lean
theorem SignedGoldenRamifierStrippedPacket.unitSector_snd_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} {gamma : GoldenInt}
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) :
    (goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd =
      -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  ...
```

Possible proofs to compare include:

1. Explicitly deriving the projected equality with `congrArg`, then chaining it with `p.beta_snd`.
2. Using `simpa` to automate the transport.
3. The current two-step rewrite `rw [← hbeta, p.beta_snd]`.

The useful evaluation point is whether a prover recognizes the already-stored invariant and uses the equality in the correct direction, rather than expanding golden multiplication or trying unnecessary sector arithmetic.

## Correspondence with the PDFs

The target branch contains both

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

and their presence was verified.

However, in the current environment the GitHub-hosted PDF bodies could not be retrieved in a form suitable for analysis. Therefore the exact PDF page or section corresponding to 0270 could not be verified, and no such correspondence is guessed here.

The technical statement, Lean type, dependency analysis, and proof flow in this note are grounded in the canonical `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is `SignedGoldenUnitFifthPowerExclusion`.

Its declaration kind is `abbrev`, and the canonical source defines it as

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

It is the reusable contradiction contract saying that no ramifier-stripped packet can have `beta` equal to a unit times a fifth power.

Now that 0270 transports the packet's exact second coordinate into a finite sector expression, the development can package the subsequent sector arithmetic into the proposition-level exclusion interface `beta = ε γ^5 -> False`.
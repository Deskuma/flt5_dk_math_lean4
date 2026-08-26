# 0235 — `signedGoldenRamifierStrippedPacket_of_powerSplit`

## Lean type

```lean
/-- Chosen ramifier-stripped packet from the exact five-adic power split. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_exceptional
    (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

This is a `noncomputable def`, not a theorem. It is a composition API that takes an exact five-adic power split `s`, passes through the square-golden exceptional packet, and returns one ramifier-stripped packet.

## Mathematical statement and meaning of the declaration

`SignedFiveAdicPowerSplit u v w` retains the exact power split obtained after organizing the unique common factor five in the signed five-adic packet. Conceptually it records

$$
\mathrm{carrier}=5^4a^5,
$$

$$
\mathrm{residual}=5b^5,
$$

$$
\mathrm{distinguished}=5ab,
$$

together with positivity and coprimality data for `a` and `b`.

The present definition first sends `s` through

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit s
```

to obtain a square-golden exceptional packet, and then passes that packet to declaration 0234

```lean
signedGoldenRamifierStrippedPacket_of_exceptional.
```

Thus the structural flow is

$$
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\mathrm{SignedSquareGoldenExceptionalPacket}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}.
$$

The resulting stripped packet records the removal of the visible ramifier

$$
\tau=2+\varphi
$$

through

$$
\alpha=\tau\beta,
$$

and exposes certificates including

$$
N(\beta)=b^5,
$$

$$
\beta_{\mathrm{snd}}=-5^7a^{10},
$$

$$
5\nmid b,
$$

$$
5\nmid N(\beta),
$$

and

$$
\tau\nmid\beta.
$$

This declaration proves none of these facts again. It only composes the two already-constructed conversions.

## Role in the full proof

Declarations 0231–0234 complete the layer that constructs a ramifier-stripped packet from a square-golden exceptional packet. Further upstream, `SignedFiveAdicPowerSplit` is one of the principal outputs of exact five-adic normalization.

Declaration 0235 directly connects those two layers as a convenience bridge.

A downstream consumer therefore does not need to write

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit s
```

and manually pass the result to 0234. It can simply use

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit s.
```

There is no new mathematical information, but this is important in the architecture of the proof tower. A consumer whose input is an exact five-adic split can move into the ramifier-stripped golden-order state without explicitly depending on the intermediate square-coordinate representation.

The following declaration 0236 then starts one layer earlier, at a signed normal form, and reaches the stripped packet through the present definition. Thus 0235 is the public conversion API

$$
\text{power-split layer}
\longrightarrow
\text{ramifier-stripped layer},
$$

while 0236 supplies the corresponding entry point from the normal-form layer.

## Direct dependencies

The direct dependencies are:

- `SignedFiveAdicPowerSplit`
- `SignedSquareGoldenExceptionalPacket`
- `SignedGoldenRamifierStrippedPacket`
- `signedSquareGoldenExceptionalPacket_of_powerSplit`
- 0234 `signedGoldenRamifierStrippedPacket_of_exceptional`

There is no tactic proof in the body of this declaration.

Conceptually it is simply the function composition

$$
P(s)=R(E(s)),
$$

where

- $E$ is `signedSquareGoldenExceptionalPacket_of_powerSplit`, and
- $R$ is `signedGoldenRamifierStrippedPacket_of_exceptional`.

All heavy arithmetic, five-adic valuation work, golden-norm calculations, and ramifier-stripping arguments have already been completed upstream.

## Construction flow

The body consists of two nested function applications:

```lean
signedGoldenRamifierStrippedPacket_of_exceptional
  (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

1. Receive `s : SignedFiveAdicPowerSplit u v w`.
2. Apply `signedSquareGoldenExceptionalPacket_of_powerSplit s` to obtain a `SignedSquareGoldenExceptionalPacket u v w`.
3. Pass that packet to declaration 0234.
4. Return a `SignedGoldenRamifierStrippedPacket u v w`.

The intermediate object is embedded directly in the expression, so no local `let` binding or proof block is needed.

## Lean-specific processing

The declaration is marked `noncomputable`.

Although `Classical.choice` does not appear directly in its body, the two upstream conversion functions it invokes are `noncomputable def`s whose constructions cross classical-choice boundaries. Consequently this composition is also exposed as a proof-oriented data API rather than as an executable witness extractor.

Importantly, `noncomputable` does not mean that the returned certificates are ambiguous or unchecked. Every field required by `SignedGoldenRamifierStrippedPacket` is verified by Lean's kernel. What is not supplied is a computational procedure specifying which inhabitant of an existence proof is selected.

The parameters `{u v w : ℕ}` are implicit and are inferred from the type of the input `s`, so consumers normally do not need to pass them explicitly.

## Redundancy and duplication

Mathematically this definition is a complete wrapper. Downstream code could write the nested expression directly:

```lean
signedGoldenRamifierStrippedPacket_of_exceptional
  (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

Therefore the declaration adds no logical expressive power.

The API duplication is nevertheless useful:

- it hides the intermediate representation from consumers;
- it provides a direct entry point at each layer of the proof tower;
- it reduces coupling of downstream code to the precise conversion sequence;
- the declaration name states the intended transition from a power split to a stripped packet;
- the public surface can potentially remain stable if the intermediate square-golden representation is refactored later.

Thus deleting the wrapper merely to reduce line count could make the layer structure less readable.

## Optimization candidates

1. **Keep the current staged wrapper**
   - This is the clearest form and preserves explicit abstraction boundaries.

2. **Inline it into 0236**
   - This would remove one named conversion from the next normal-form bridge, but would also eliminate the public power-split-to-stripped entry point.

3. **Use a generic composition helper**
   - Technically possible, but for a domain-specific transformation this one-line named declaration carries more semantic information than generic composition syntax.

4. **Replace the classical-choice chain with explicit constructors**
   - If the upstream `Nonempty + Classical.choice` architecture were redesigned around explicit data construction, this path might become computable. Changing 0235 alone would not accomplish that.

5. **Regularize the conversion graph as an API**
   - A consistent naming scheme for `normalForm → fiveAdic → powerSplit → squareGolden → stripped` canonical conversions could further improve traceability through the long proof tower.

The current body is already one line, so there is essentially no local proof optimization to perform. The interesting optimization question is the topology of the API.

## Required Mathlib imports and import optimization

This declaration itself uses no tactic. Its direct requirements are the upstream project types and conversion definitions together with support for a `noncomputable` declaration.

Its effective dependencies lie in the project layers for:

- signed five-adic power splitting,
- the signed square-golden exceptional packet, and
- ramifier stripping.

There should be no need to import all of `Mathlib` solely for this declaration.

However, the surrounding `SignedGoldenRamifierStripped.lean` module contains the substantial upstream construction using `nlinarith`, `omega`, `ring`, `norm_num`, integer divisibility, primes, and casts. Therefore actual import minimization must be tested at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes, although this is a comparison of API architecture rather than mathematical theorem strength.

Possible contestants are:

- A: the current staged named wrapper;
- B: inline the two conversions at every use site;
- C: an explicit computable constructor chain;
- D: a generic composition helper or canonical-conversion framework.

Useful comparison axes include:

- downstream code size;
- clarity of abstraction boundaries;
- coupling to intermediate representations;
- robustness under refactoring;
- scope of `noncomputable` dependencies;
- ease of following the source in dependency order.

The A-versus-B comparison is especially useful for asking whether a one-line wrapper in a long Lean formalization is unnecessary duplication or a valuable semantic API boundary.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this declaration appears immediately after 0234 and is followed by `signedGoldenRamifierStrippedPacket_of_normalForm`.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact page or section corresponding to this one-line API bridge was not identified in this pass, so no PDF page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0236 `signedGoldenRamifierStrippedPacket_of_normalForm`**:

```lean
/-- Chosen ramifier-stripped packet directly from a signed normal form. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

Declaration 0235 provides the entry point from an exact power split to a stripped packet. Declaration 0236 begins one layer earlier, constructs the power split from a signed normal form, and immediately feeds it through 0235. This completes the canonical conversion chain from signed routing to ramifier stripping.
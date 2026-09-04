# 0254 — `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor`

## Lean type

```lean
/-- Any implementation of the generic coprime-factor theorem supplies the stripped
packet's unit-times-fifth-power representation. -/
theorem signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    (hFactor : GoldenCoprimeFactorOfFifthPower) :
    SignedGoldenFifthPowerUpToUnitCore := by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

This is a `theorem`.

It takes the generic fifth-power factor-extraction contract isolated in 0253 `GoldenCoprimeFactorOfFifthPower`, applies it specifically to the stripped packet's `beta` and its conjugate, and thereby constructs the previously required `SignedGoldenFifthPowerUpToUnitCore`.

## Mathematical statement

The contract from 0253 says that for golden integers `x`, `y`, and `z`, if

$$
\operatorname{GoldenRelPrime}(x,y)
$$

and

$$
xy=z^5,
$$

then there exist a unit $\varepsilon$ and a golden integer $\gamma$ such that

$$
x=\varepsilon\gamma^5.
$$

The present theorem specializes this to a stripped packet `p` by taking

$$
x:=\beta,
\qquad
y:=\overline{\beta},
\qquad
z:=\operatorname{goldenOfInt}(b).
$$

Upstream results have already established

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

and

$$
\beta\overline{\beta}
=
(\operatorname{goldenOfInt}b)^5.
$$

Applying `hFactor` therefore yields

$$
\exists \varepsilon,\gamma,
\quad
\operatorname{GoldenUnit}(\varepsilon)
\land
\beta=\varepsilon\gamma^5,
$$

which is exactly the output required by `SignedGoldenFifthPowerUpToUnitCore`.

## Role in the full proof

Declarations 0241–0244 established relative primality of `beta` and `goldenConj beta`. Declarations 0251–0252 established that their product is an embedded fifth power. Declaration 0253 then isolated the generic algebraic rule that converts those two facts into a unit-times-fifth-power representation of one factor.

Declaration 0254 connects all three layers:

$$
\text{stripped packet}
\Longrightarrow
\begin{cases}
\operatorname{RelPrime}(\beta,\overline{\beta}),\\
\beta\overline{\beta}=z^5
\end{cases}
\Longrightarrow
\beta=\varepsilon\gamma^5.
$$

No new number-theoretic calculation occurs here. Its importance is architectural: it closes the boundary between FLT5-specific packet arithmetic and the generic gcd/UFD-style factor-extraction theorem.

Later, `GoldenCoprimeFactor.lean` provides a concrete implementation of `GoldenCoprimeFactorOfFifthPower`; feeding that implementation into this adapter immediately supplies `SignedGoldenFifthPowerUpToUnitCore`.

## Direct dependencies

The theorem directly uses:

- 0253 `GoldenCoprimeFactorOfFifthPower`
- 0240 `SignedGoldenFifthPowerUpToUnitCore`
- `SignedGoldenRamifierStrippedPacket`
- 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`
- 0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`
- `goldenConj`
- `goldenOfInt`

The proof is simply an application of the function-shaped contract from 0253 to the exact data and certificates stored in the stripped packet.

Conceptually,

$$
hFactor
+
\operatorname{RelPrime}(\beta,\overline{\beta})
+
\beta\overline{\beta}=z^5
\Longrightarrow
\beta=\varepsilon\gamma^5.
$$

## Proof flow

The proof is extremely short:

```lean
by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

1. Unfold the `SignedGoldenFifthPowerUpToUnitCore` contract enough to accept arbitrary `u v w` and a stripped packet `p`.
2. Supply `p.beta` as `x` to `hFactor`.
3. Supply `goldenConj p.beta` as `y`.
4. Supply `goldenOfInt (p.exceptional.powerSplit.b : ℤ)` as `z`.
5. Supply `p.beta_relPrime_conj` as the relative-primality hypothesis.
6. Supply `p.beta_mul_conj_eq_fifth` as the product-is-a-fifth-power hypothesis.
7. The conclusion of `hFactor` is exactly the conclusion required by `SignedGoldenFifthPowerUpToUnitCore`.

No `rw`, `simp`, `ring`, or `norm_num` is needed.

## Lean-specific processing

`SignedGoldenFifthPowerUpToUnitCore` is an `abbrev : Prop`, so after `intro u v w p` it behaves transparently as an ordinary dependent function type.

Likewise, `GoldenCoprimeFactorOfFifthPower` is also an `abbrev : Prop`, so the hypothesis `hFactor` is directly callable as a function:

```lean
hFactor p.beta (goldenConj p.beta)
  (goldenOfInt ...)
  p.beta_relPrime_conj
  p.beta_mul_conj_eq_fifth
```

This is a clean example of transparent abbreviations and dependent field projections working together.

The expression `(p.exceptional.powerSplit.b : ℤ)` also crosses two representation boundaries: the packet stores `b` as a natural number, it is coerced to `ℤ`, and `goldenOfInt` then embeds that integer into `GoldenInt`.

## Redundancy and duplication

Logically, this is a very thin adapter. Any downstream proof could directly write

```lean
hFactor p.beta (goldenConj p.beta)
  (goldenOfInt ...)
  p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

and obtain the same result.

However, keeping a named theorem has clear API value:

- it gives a single name to the connection from the stripped packet to generic factor extraction;
- downstream code does not need to know the provenance of `beta_relPrime_conj` or `beta_mul_conj_eq_fifth`;
- the implementation of the generic factor theorem may change from gcd-based to UFD-based, valuation-based, or another approach without changing the consumer contract;
- the proof graph explicitly records that the generic factor-extraction contract is sufficient to produce the stripped fifth-power core.

So the redundancy is intentional and architectural rather than accidental.

## Optimization candidates

1. **Keep the current adapter theorem**
   - this gives the clearest module boundary.

2. **Compress with `simpa`**
   - a shorter formulation may be possible because the conclusion types line up exactly, although the current explicit `exact` is already clear.

3. **Turn it into a packet namespace helper**
   - an API such as `p.fifthPowerUpToUnit hFactor` could shorten consumers further.

4. **Use an `Associated`-based generic theorem**
   - this would require the adapter to recover an explicit unit witness from an association relation.

5. **Call the concrete generic theorem directly**
   - this removes one layer but sacrifices the dependency-inversion boundary that the current design preserves.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This theorem itself has a very small direct surface. It uses only upstream golden-order contracts and packet projections:

- `SignedGoldenFifthPowerUpToUnitCore`
- `GoldenCoprimeFactorOfFifthPower`
- `goldenConj`
- `goldenOfInt`
- packet certificate theorems

The concrete implementation of `GoldenCoprimeFactorOfFifthPower`, however, is proved later in `GoldenCoprimeFactor.lean` using gcd, `IsUnit`, and associated-power APIs, so the minimal import set for the whole module boundary is wider than the requirements of 0254 in isolation.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. This declaration is better suited to a comparison of **adapter architecture** than of proof tactics.

Possible variants are:

- A: current contract injection plus thin adapter;
- B: downstream directly calls the generic theorem;
- C: packet namespace method for factor extraction;
- D: `Associated`-based generic theorem plus witness-recovery adapter;
- E: exponent-generalized contract specialized at `n = 5`.

Useful comparison axes include dependency direction, consumer brevity, replaceability of the generic theorem, ease of obtaining explicit witnesses, elaboration burden, and standalone auditability.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenFifthPower.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0253 `GoldenCoprimeFactorOfFifthPower`; the `SignedGoldenFifthPower.lean` generated section ends immediately after this theorem.

The standalone artifact uses `import Mathlib`.

The target branch contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal adapter theorem was not identified in this run, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is the first declaration of the following module `GoldenFifthPowerCoordinates.lean`, **0255 `goldenFifthFstPoly`**:

```lean
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

Declaration 0254 completes the abstract extraction step `beta = epsilon * gamma^5`. From 0255 onward, the development expands `gamma = p + qφ` into explicit fifth-power coordinate polynomials and begins the arithmetic analysis of the five unit-class sectors.

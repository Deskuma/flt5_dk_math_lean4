# 0361 — `golden_phi_four_mul_inv_five`

## Declaration kind

This declaration is a **`private theorem`**.

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  decide
```

It certifies the wrap-around identity needed when a `GoldenUnitFifthClass` representative in sector `0` is multiplied by `φ⁻¹` and must be moved back to sector `4`.

## Lean type

```lean
golden_phi_four_mul_inv_five :
  goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv
```

This is a closed equality of concrete `GoldenInt` values, with no variables or hypotheses.

Because it is `private`, the theorem is a local helper for `GoldenUnitClassification.lean`, not part of the intended external API of the module.

## Mathematical statement

`goldenPhiInv` denotes the inverse of the golden unit `φ`; earlier results establish

$$
\varphi\varphi^{-1}=1,
\qquad
\varphi^{-1}\varphi=1.
$$

Thus the theorem states

$$
\varphi^4(\varphi^{-1})^5=\varphi^{-1}.
$$

At the level of exponents,

$$
\varphi^4\varphi^{-5}=\varphi^{-1},
$$

which is simply

$$
4-5=-1.
$$

Modulo fifth powers this is the unit-class wrap-around

$$
-1\equiv4\pmod5.
$$

In explicit coordinates one has

$$
\varphi^4=(2,3),
\qquad
(\varphi^{-1})^5=(-8,5).
$$

Using golden multiplication

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd),
$$

we obtain

$$
(2,3)(-8,5)=(-1,1)=\varphi^{-1}.
$$

## Role in the full proof

0360 `GoldenUnitFifthClass` introduced the finite classification target

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}.
$$

To combine that classification with the strict descent from 0359 `goldenUnit_descent`, multiplication by either `φ` or `φ⁻¹` must preserve membership in one of the five classes.

For multiplication by `φ⁻¹`, sectors `1,2,3,4` simply move by

$$
i\mapsto i-1.
$$

Sector `0` is the exceptional case because a negative natural exponent cannot be written directly. Instead one rewrites

$$
\varphi^{-1}=\varphi^4(\varphi^{-1})^5,
$$

and absorbs the fifth power into the fifth-power base:

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5.
$$

The next theorem, `golden_sector_zero_mul_phiInv`, uses this identity directly.

Thus 0361 is the minimal algebraic certificate implementing the cycle

$$
0\xrightarrow{\times\varphi^{-1}}4.
$$

## Direct dependencies

The project declarations named directly in the theorem statement are:

- `goldenPhi : GoldenInt` — the golden unit `φ`.
- `goldenPhiInv : GoldenInt` — the integral inverse of `φ`.

The ordinary `^` and `*` operations use the ring structure installed on `GoldenInt`. These operations are consistent with the explicit `goldenPow` / `goldenMul` API used elsewhere.

Conceptually, the theorem also rests on the earlier facts

- `golden_phi_mul_inv`,
- `golden_inv_mul_phi`,
- `goldenUnit_phiInv`,

which establish that `goldenPhiInv` is genuinely the inverse of `goldenPhi`. However, the Lean proof term does not invoke those lemmas explicitly; it closes by concrete computation with `decide`.

## Proof flow

The complete proof is

```lean
by
  decide
```

### 1. The proposition is fully concrete

There are no variables or assumptions. Both sides are fixed `GoldenInt` values.

### 2. Lean computes decidable equality

`GoldenInt` is a concrete integer-coordinate type, so equality is decidable.

Lean evaluates `goldenPhi`, `goldenPhiInv`, powers, and multiplication, then checks that the resulting coordinates agree.

Conceptually the computation is

```text
φ^4 = (2,3)
φInv^5 = (-8,5)
(2,3) * (-8,5) = (-1,1)
φInv = (-1,1)
```

and the kernel checks the resulting proof.

## Lean-specific processing

### `decide`

The distinctive feature is that the proof does not rewrite with inverse laws. Instead it asks the proposition's `Decidable` instance to compute the truth of the closed equality.

For a completely concrete equality, this keeps the proof extremely short while still producing a kernel-checked proof term.

The mathematical reason

$$
\varphi^4\varphi^{-5}=\varphi^{-1}
$$

is less visible in the source, however, so documenting the mod-5 exponent interpretation is useful.

### `private theorem`

The result exists only to support the subsequent sector-transition implementation. It is not a general-purpose theorem intended for users of the module, so `private` is a natural choice.

## Redundancy and overlap

The proof itself contains essentially no redundancy.

Mathematically, however, the earlier inverse identities

```lean
goldenPhi * goldenPhiInv = 1
goldenPhiInv * goldenPhi = 1
```

are already available, so the result could instead be derived structurally from power laws and inverse cancellation.

Conceptually one could argue

$$
\varphi^4(\varphi^{-1})^5
=(\varphi\varphi^{-1})^4\varphi^{-1}
=\varphi^{-1}.
$$

The present `decide` proof is shorter, but depends on the concrete coordinate realization rather than explicitly on inverse semantics.

## Optimization candidates

1. **Keep the current proof** — for a closed concrete equality, `by decide` is likely the smallest and most robust implementation.
2. **Use a structural proof** — deriving the result only from `golden_phi_mul_inv` and generic power laws would better expose the algebraic meaning and would be less tied to the concrete coordinates of `goldenPhi` and `goldenPhiInv`.
3. **Absorb it into a generic sector-transition theorem** — one could formulate exponent arithmetic directly in `Fin 5` so that the `0 → 4` wrap-around is handled abstractly. This may, however, be heavier than the current explicit finite-case implementation.

These are design candidates only; no Lean build was run, so alternative implementations were not validated here.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

For this theorem alone, once the `GoldenInt` ring instance, `goldenPhi`, and `goldenPhiInv` are available, the external requirements are essentially:

- natural-number powers,
- multiplication,
- decidable equality,
- `decide`.

Therefore the theorem itself does not require the whole of `Mathlib`. The real module `GoldenUnitClassification.lean` could likely depend on a much smaller set of imports centered on the golden-order API plus the decision/tactic infrastructure it uses.

The exact minimal import set is **not verified**, because no Lean build was performed.

## Comparator challenge suitability

**Yes — it is very suitable as a micro challenge.**

A challenge can fix the theorem statement and leave only the proof hole:

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  ?_
```

The shortest solution is

```lean
decide
```

but a Comparator exercise could contrast two styles:

- direct concrete computation with `decide`;
- a structural proof from inverse identities and power laws.

Because the theorem is tiny, it should be easy to run in either CLI or Web Comparator environments, and it cleanly exposes the tradeoff between proof-term brevity and algebraic abstraction.

## Next declaration to read

The next declaration is **0362 `golden_sector_zero_mul_phiInv`**, also a **`private theorem`**:

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  rw [mul_pow]
  calc
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
        goldenPhiInv * delta ^ 5 := by ring
    _ = (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5 := by
      rw [golden_phi_four_mul_inv_five]
    _ = goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5) := by ring
```

It lifts the concrete identity from 0361 to the actual sector transition

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5,
$$

thereby completing the witness transformation for the `0 → 4` wrap-around in `GoldenUnitFifthClass`.

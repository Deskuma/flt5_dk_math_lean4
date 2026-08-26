# 0207 — `goldenUnit_pow`

## Lean type

```lean
theorem goldenUnit_pow {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (goldenPow x n) := by
  induction n with
  | zero => exact goldenUnit_one
  | succ n ih => exact goldenUnit_mul ih hx
```

This is a `theorem` stating that if a golden integer `x` satisfies `GoldenUnit`, then every raw natural power `goldenPow x n` also satisfies `GoldenUnit`.

## Mathematical statement and meaning of the declaration

Mathematically, this is the standard closure of units under natural powers:

$$
GoldenUnit(x)\Longrightarrow GoldenUnit(x^n).
$$

Here `goldenPow` is the explicit recursive power operation introduced earlier:

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

Thus the induction performed in the theorem follows exactly the recursion defining the power itself.

For `n = 0`,

$$
x^0=1,
$$

so 0204 `goldenUnit_one` supplies the base case. For `n+1`,

$$
x^{n+1}=x^n x,
$$

and the induction hypothesis makes `x^n` a unit while the original hypothesis `hx` says that `x` is a unit. Declaration 0206 `goldenUnit_mul` then makes their product a unit.

In particular, substituting `n=5` immediately gives closure under fifth powers, which is directly relevant to the later FLT5 factorization arguments where unit factors and fifth-power factors are separated and recombined in the golden order.

## Role in the full proof

Declarations 0198–0207 complete the elementary API for `GoldenUnit`.

- 0198 `GoldenUnit` — unitness is defined by an explicit two-sided inverse.
- 0199–0202 — bidirectional characterization by norm `±1`.
- 0203 `goldenUnit_phi` — the generator `φ` is a unit.
- 0204 `goldenUnit_one` — `1` is a unit.
- 0205 `goldenUnit_neg` — negation preserves unitness.
- 0206 `goldenUnit_mul` — multiplication preserves unitness.
- 0207, the present theorem — natural powers preserve unitness.

This theorem is the final theorem in that unit block. It combines the base case from 0204 and the multiplicative step from 0206 by natural-number induction and exposes arbitrary powers through one reusable API.

Immediately afterward the source defines

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

so the source structure is deliberate: first finish the basic behavior of units, then use the completed `GoldenUnit` predicate to define relative primality as the condition that every common divisor is a unit.

In the later FLT5 golden-order argument, units must remain stable while conjugate factors and fifth powers are manipulated. The present theorem is the final basic closure result needed to carry unit information through those power operations.

## Direct dependencies

The current proof has a very small direct dependency surface:

- 0198 `GoldenUnit`
- 0125 `goldenPow`
- 0204 `goldenUnit_one`
- 0206 `goldenUnit_mul`
- Lean's natural-number induction machinery

The logical structure is simply to combine

$$
GoldenUnit(1)
$$

with

$$
GoldenUnit(a)\land GoldenUnit(x)
\Longrightarrow
GoldenUnit(ax)
$$

and recurse to obtain

$$
GoldenUnit(x^n).
$$

Also, 0160 `golden_pow_eq` already exposes the definitional equality between raw `goldenPow x n` and standard `x ^ n`. Therefore the theorem is stated in the raw API but has exactly the mathematical content of closure under standard powers.

## Proof / construction flow

The proof is structural induction on `n`.

### 1. The case `n = 0`

```lean
| zero => exact goldenUnit_one
```

By definition, `goldenPow x 0` is `goldenOne`, so 0204 `goldenUnit_one` closes the goal directly.

### 2. The case `n + 1`

```lean
| succ n ih => exact goldenUnit_mul ih hx
```

The induction hypothesis is

```lean
ih : GoldenUnit (goldenPow x n)
```

and the original assumption is

```lean
hx : GoldenUnit x.
```

Applying 0206 `goldenUnit_mul` to those two hypotheses yields unitness of

```lean
goldenMul (goldenPow x n) x.
```

But that expression is definitionally exactly `goldenPow x (n + 1)`, so no additional rewrite, `change`, or `simp` is needed.

## Lean-specific processing

The most important Lean-specific feature is the exact alignment between the induction shape and the recursive definition of `goldenPow`.

```lean
induction n with
| zero => ...
| succ n ih => ...
```

produces a successor goal whose definitional unfolding matches the output of

```lean
exact goldenUnit_mul ih hx.
```

This contrasts with 0196 `goldenConj_pow` and 0197 `goldenNorm_pow`. Those theorems are stated using standard powers `x ^ n`, so their successor cases need `pow_succ` and an explicit `change` to move between standard multiplication and raw `goldenMul`. Here the statement itself uses raw `goldenPow`, so definitional alignment is maximal and the proof is correspondingly tiny.

At the same time, 0160 provides

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

so downstream code can move to standard power notation whenever useful.

## Redundancy and duplication

Mathematically, the fact that powers of units are units is generic ring theory. Once `GoldenUnit` is connected to Mathlib's `IsUnit`, a golden-specific induction theorem could potentially be replaced by standard unit-power API.

There is also an API-level duplication between

- `GoldenUnit (goldenPow x n)`
- `GoldenUnit (x ^ n)`

because 0160 makes raw and standard powers definitionally equal. The current theorem deliberately chooses the first form.

That choice nevertheless has a concrete advantage: because the theorem is stated directly in the raw recursive API, its proof is exactly the recursion of `goldenPow` and needs only the base-unit theorem and multiplication closure. A statement directly in standard power notation could require additional bridge steps.

Thus the duplication is real, but it is useful redundancy in service of a transparent bootstrap layer and a minimal proof.

## Optimization candidates

1. **Keep the current raw-power theorem**
   - the recursive definition and induction line up exactly, giving the smallest proof.

2. **Add a standard-power wrapper theorem**
   - for example, conceptually:

```lean
theorem goldenUnit_pow_std {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (x ^ n) := by
  simpa using goldenUnit_pow hx n
```

   The exact `simpa` behavior is not build-verified in this museum pass.

3. **Use a `GoldenUnit ↔ IsUnit` bridge**
   - Mathlib's generic unit-power facts could then replace the custom induction proof.

4. **Bundle the unit criterion from 0201/0202 as an iff theorem**
   - together with `goldenNorm_pow`, one could prove power closure entirely through the norm side.

5. **Eventually absorb `goldenPow` into standard `Pow` API**
   - viable if the audit value of the explicit raw operation becomes less important later in the development.

Locally the current proof is already excellent; the main optimization opportunities concern organization of the raw and standard APIs rather than proof compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct surface used by this theorem is very small:

- `Nat` and natural-number induction
- `GoldenUnit`
- `goldenPow`
- `goldenUnit_one`
- `goldenUnit_mul`

The theorem itself does not directly use `ring`, `norm_num`, `simp`, or integer-divisibility results.

It is therefore very likely that the declaration in isolation requires much less than all of `Mathlib`. However, the surrounding `GoldenDivisibility.lean` module uses divisibility, conjugation, norms, and integer arithmetic, so actual import minimization should be measured at module scope.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Despite the small proof, it gives a clean API-design comparison.

Possible competitors are:

- A: the current direct induction on raw `goldenPow`
- B: induction on standard power `x ^ n`
- C: `GoldenUnit ↔ IsUnit` plus Mathlib's generic unit-power API
- D: a norm-based proof using `N(x)=±1` together with `goldenNorm_pow`
- E: directly construct a power of the inverse witness

Useful comparison axes include proof-term size, number of raw/standard API conversions, typeclass dependency depth, visibility of mathematical provenance, Mathlib reuse, and robustness under refactoring.

The contrast between A and D is particularly interesting: 0205–0206 prove closure through the norm criterion, while 0207 instead exploits the recursive structure of the power operation directly.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0206 `goldenUnit_mul` and immediately before the definition of `GoldenRelPrime`.

The standalone artifact lists `DkMath/FLT/Five/GoldenDivisibility.lean` among its ordered source modules and uses `import Mathlib` globally.

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified directly in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0208 `GoldenRelPrime`**:

```lean
/-- Relative primality expressed by saying that every common divisor is a unit, hence
has norm `±1`. -/
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

By 0207, the definition of `GoldenUnit`, its norm criterion, and its elementary closure properties are complete. Declaration 0208 uses that finished predicate to define relative primality by saying that every common divisor `d` of `x` and `y` must be a unit.

This avoids constructing Bézout coefficients directly and is tailored to the later proof that an element and its conjugate have no nonunit common divisor before the fifth-power factorization step.
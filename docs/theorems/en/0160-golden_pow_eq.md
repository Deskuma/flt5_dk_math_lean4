# 0160 — `golden_pow_eq`

## Lean type

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

This is a theorem exposing, as an `@[simp]` bridge, the definitional equality between the raw operation `goldenPow` and the standard power `x ^ n` provided by `CommRing GoldenInt`.

## Mathematical statement and meaning of the declaration

`goldenPow` explicitly defines natural powers on golden integers by recursion:

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

Thus mathematically,

$$
goldenPow(x,0)=1,
$$

$$
goldenPow(x,n+1)=goldenPow(x,n)\,x.
$$

When `goldenCommRing : CommRing GoldenInt` is constructed, however, its natural-power field is registered as

```lean
npow := fun n x => goldenPow x n
```

so the standard notation `x ^ n` is implemented by exactly the same function `goldenPow x n`. The theorem proves no new power law; it publishes this identity as a named API theorem.

## Role in the overall proof

Declarations 0156–0160 form the bridge block that normalizes raw operations into standard Mathlib notation:

```text
goldenAdd x y  →  x + y
goldenNeg x    →  -x
goldenSub x y  →  x - y
goldenMul x y  →  x * y
goldenPow x n  →  x ^ n
```

0160 is the final declaration in that block. At this point the bootstrap-oriented raw API of `GoldenOrder` can be translated into ordinary algebra notation before later arguments about rings, divisibility, units, and fifth powers.

The downstream source explicitly uses `golden_pow_eq` in rewrite sets for fifth-power factorization, unit-sector manipulations, and norm/power arguments. It is therefore not merely cosmetic: it acts as a stable rewrite contract from the raw API to the standard ring API.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenPow`
- `goldenOne`
- `goldenMul`
- `goldenCommRing : CommRing GoldenInt`
- the standard power notation supplied through Mathlib's algebra hierarchy

The crucial design fact is that the `npow` field of `goldenCommRing` is set to `goldenPow` itself. Consequently the theorem closes by `rfl` without invoking any auxiliary lemma.

## Proof / construction flow

The proof is only

```lean
:= rfl
```

After Lean expands the standard power `x ^ n` through the `CommRing GoldenInt` structure, its implementation is `goldenPow x n`. The two sides are therefore definitionally equal, so no induction or simplification is required.

The important content is not the short proof but the earlier structural decision to make the raw recursive power and the standard ring power share the same implementation.

## Lean-specific processing

The notation `^` is resolved through typeclass and algebraic structure machinery. In `goldenCommRing`, the relevant fields are constructed as

```lean
npow := fun n x => goldenPow x n
npow_zero := by intro x; rfl
npow_succ := by
  intro n x
  change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
  rfl
```

Thus even the standard zero and successor laws for natural powers are aligned definitionally with the raw recursion.

With the `@[simp]` attribute, an occurrence of `goldenPow x n` is normalized to the standard form `x ^ n`. This is useful when applying standard Mathlib results such as `mul_pow` or lemmas relating norms and powers.

## Redundancy and duplication

After `goldenCommRing` exists, `goldenPow` and `x ^ n` denote the same operation, so the two APIs may appear redundant. Their roles are nevertheless different.

`goldenPow` is a bootstrap operation available before the commutative-ring structure has been assembled, while `x ^ n` is the public interface of the completed algebra structure. The duplication is therefore deliberate layering rather than accidental repetition.

## Optimization candidates

1. Remove `goldenPow` and define the natural-power field directly inside the `CommRing` construction.
2. Keep the current design and retain `golden_pow_eq` as an explicit boundary between the raw and standard APIs.
3. Make the raw-operation layer private and expose only the standard algebra API after the bridge theorems.
4. Group `golden_add_eq` through `golden_pow_eq` into a clearly delimited API section so downstream `simp only` rewrite sets are easier to audit.

For an auditable FLT5 formalization, the current explicit bootstrap has a strong advantage: fifth powers can be followed from their recursive coordinate implementation all the way to the standard algebra layer without hiding the construction behind excessive abstraction.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself needs only `GoldenInt`, its `CommRing` instance, natural-power notation, and the simp-attribute infrastructure.

It is therefore unlikely that the whole `Mathlib` import is necessary merely for 0160. The complete `GoldenOrder` module, however, also uses facilities such as `ring`, `omega`, and `Zsqrtd`. Because this museum pass does not run a Lean build, the exact minimal import set is not verified; import reduction is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Three useful implementations could be compared:

- the current design: explicit `goldenPow`, registered as `npow`, with `golden_pow_eq` closing by `rfl`;
- a `CommRing` construction that defines natural powers directly and has no raw `goldenPow`;
- a more generic quadratic-order implementation using its standard `Pow` interface from the outset.

Possible metrics include the number of lemmas closed by `rfl`, the number of rewrites required in fifth-power theorems, simp normal forms, clarity of bootstrap dependencies, generalizability, and readability of downstream proofs.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this theorem appears immediately after `golden_mul_eq`, followed by the definition of the basis element `goldenPhi`.

Japanese and English PDFs are also present on the target branch, but the exact page corresponding to this small raw/standard API bridge theorem was not directly identified in this pass. No PDF page number is therefore inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
/-- The basis element `phi`. -/
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

With 0160 the raw-operation bridge block is complete. The development now moves to the golden-order-specific basis element $\varphi$, followed by conjugation and norm. The definition `goldenPhi = 0 + 1\varphi` reintroduces the arithmetic content specific to the golden order after the abstract `CommRing GoldenInt` interface has been established.

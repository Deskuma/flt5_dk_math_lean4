# 0388 `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`

## Declaration kind

`theorem`

This theorem lives in the `GoldenZeroSectorDescentPacket` namespace. It projects the pure fifth-power re-entry obtained in 0387 to the second coordinate and turns it into the product decomposition needed for the next descent step.

## Lean code

```lean
theorem fifthRoot_snd_factor_eq
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    p.base.snd ^ 2 =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := by
  have h := congrArg (fun x : GoldenInt => x.snd) hroot
  change (goldenZeroSectorLift p.base).snd =
    (goldenPow gamma 5).snd at h
  rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
    goldenFifthSndPoly_eq] at h
  exact h
```

## Lean type

Conceptually, the type is

```lean
GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  p.base.snd ^ 2 =
    5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

The inputs are a descent packet `p`, a golden integer `gamma`, and a proof `hroot` that the quadratic lift is the fifth power of `gamma`. The output is a product identity in `ℤ`.

## Mathematical statement

Write `p.base=(r,s)` and `gamma=(a,b)`.

The quadratic lift satisfies

$$
\operatorname{goldenZeroSectorLift}(r,s)_{\mathrm{snd}}=s^2.
$$

On the other hand, the second coordinate of the fifth power of a golden integer is

$$
(\gamma^5)_{\mathrm{snd}}
 = \operatorname{goldenFifthSndPoly}(a,b)
 = 5b\,H(a,b),
$$

where

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

Therefore, taking second coordinates in

$$
\operatorname{goldenZeroSectorLift}(r,s)=\gamma^5
$$

gives

$$
s^2=5bH(a,b).
$$

This is exactly the Lean conclusion

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

## Role in the full proof

In 0387 `exists_lift_eq_fifthPower`, the unit-sector ambiguity was eliminated and one obtained

$$
\operatorname{goldenZeroSectorLift}(p.base)=\gamma^5.
$$

That equality still lives in the golden-integer structure. By itself it is not yet the integer factorization needed for comparing descent measures.

0388 extracts only the second coordinate and converts the golden-integer identity into

$$
s^2=5bH(a,b).
$$

This makes the following steps possible:

- prove positivity of `H(a,b)`;
- prove coprimality between `b` and `H(a,b)`;
- use the fact that `5bH(a,b)` is a square to split powers;
- construct new fifth-power parameters;
- construct a packet with strictly smaller measure.

Thus this theorem is the **coordinate-projection bridge** reconnecting the fifth-power structure in the golden integer ring to the ordinary integer arithmetic used in strict descent.

## Direct dependencies

The main declarations used directly are:

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenZeroSectorLift_snd`
- `goldenPow_five_snd`
- `goldenFifthSndPoly_eq`
- `goldenFifthSndFactor`

In particular, the repository already contains the coordinate identities

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

and

```lean
theorem goldenFifthSndPoly_eq (r s : ℤ) :
    goldenFifthSndPoly r s =
      5 * s * goldenFifthSndFactor r s := by
  ...
```

Therefore 0388 performs no new polynomial expansion itself.

## Proof flow

1. Apply the second-coordinate projection to both sides of `hroot`.

   ```lean
   have h := congrArg (fun x : GoldenInt => x.snd) hroot
   ```

   Conceptually this gives

   $$
   T(r,s)_{\mathrm{snd}}=(\gamma^5)_{\mathrm{snd}}.
   $$

2. Use `change` to put the projected equality into the exact presentation expected by the rewrite lemmas.

   ```lean
   change (goldenZeroSectorLift p.base).snd =
     (goldenPow gamma 5).snd at h
   ```

3. Rewrite with the three existing coordinate identities.

   ```lean
   rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
     goldenFifthSndPoly_eq] at h
   ```

   The left side becomes `p.base.snd ^ 2` and the right side becomes

   ```lean
   5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
   ```

4. The rewritten hypothesis now matches the target exactly, so return it.

   ```lean
   exact h
   ```

## Lean-specific processing

### Coordinate projection with `congrArg`

`hroot` is an equality of `GoldenInt` values, while only the second coordinate is needed. The proof uses

```lean
congrArg (fun x : GoldenInt => x.snd) hroot
```

to transport equality through the projection map.

This is the standard Lean pattern for extracting an observable component from an equality of structures.

### Presentation control with `change`

After `congrArg`, elaboration may present the projection in a form that is not immediately convenient for the rewrite chain. The proof explicitly sets the local goal shape with

```lean
change (goldenZeroSectorLift p.base).snd =
  (goldenPow gamma 5).snd at h
```

This adds no mathematical content; it is a Lean-level normalization step.

### Reuse of certified polynomial identities

The proof does not expand the fifth power with `ring` locally. Instead it reuses `goldenPow_five_snd` and `goldenFifthSndPoly_eq`. This avoids duplicated polynomial algebra and keeps the canonical coordinate formulas centralized.

## Redundancy and duplication

The theorem is already very short, and there is essentially no mathematical duplication.

The one potentially removable line is the `change` after `congrArg`. Depending on the available projection simplification lemmas, a proof close to

```lean
have h := congrArg GoldenInt.snd hroot
simpa [goldenZeroSectorLift_snd, goldenPow_five_snd,
  goldenFifthSndPoly_eq] using h
```

may be possible.

This has not been checked because no Lean build is being run in this task, and the exact projection name and simplifier normal form matter.

## Optimization candidates

### 1. Shared projection helper

If later proofs repeatedly extract `fst` or `snd` from golden-integer equalities, one could introduce a helper such as

```lean
theorem goldenEq_snd {x y : GoldenInt} (h : x = y) : x.snd = y.snd :=
  congrArg (fun z => z.snd) h
```

However, this may be heavier than the one-line `congrArg` currently used, so it is not clearly an improvement here.

### 2. Factorized fifth-power second-coordinate lemma

The current API rewrites in two stages:

$$
(\gamma^5)_{\mathrm{snd}}
\to \operatorname{goldenFifthSndPoly}
\to 5bH(a,b).
$$

If this factorized form is used frequently, one could add

```lean
theorem goldenPow_five_snd_factorized (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := ...
```

Then 0388 would become even more direct.

The present two-layer API also has a legitimate design advantage: it separates the expanded coordinate polynomial from its factorized form.

## Required Mathlib imports and import optimization

The repository's standalone source `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`.

The proof body of 0388 directly needs only lightweight Lean/Mathlib functionality, mainly:

- equality congruence via `congrArg`;
- structure projections;
- `rw`;
- `change`.

Therefore importing all of `Mathlib` would be excessive for this theorem in isolation. In the actual source module, however, the theorem depends on the local golden-integer definitions, power operations, coordinate identities, and the zero-sector lift. The exact minimal import set must be checked against the module dependency graph and a Lean build. Since this task explicitly does not run a Lean build, that minimum is unverified.

Any import optimization should therefore be evaluated at the `SignedGoldenZeroSectorDescent.lean` module level rather than for this theorem alone.

## Comparator challenge suitability

**Yes.** It is a small challenge rather than a deep arithmetic one.

A reduced challenge could expose

```lean
-- given
hroot : goldenZeroSectorLift base = goldenPow gamma 5

-- prove
base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

while allowing only the APIs

- `goldenZeroSectorLift_snd`;
- `goldenPow_five_snd`;
- `goldenFifthSndPoly_eq`.

This tests whether Comparator can

1. project a structure equality to one coordinate;
2. choose `congrArg` or an equivalent projection argument;
3. assemble the shortest correct rewrite chain.

It is therefore more suitable for testing Lean API selection and proof compression than mathematical discovery.

## Next declaration to read

The next declaration is `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`.

```lean
theorem fifthRoot_H_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < goldenFifthSndFactor gamma.fst gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 :=
    sq_pos_of_ne_zero p.snd_ne_zero
  ...
```

Using the identity from 0388,

$$
s^2=5bH(a,b),
$$

together with the already established `p.snd_ne_zero`, the next theorem starts from positivity of the left-hand side and extracts

$$
H(a,b)>0.
$$

Thus the dependency order is: 0388 **extracts the product identity**, and the next declaration **extracts positivity from that product**.
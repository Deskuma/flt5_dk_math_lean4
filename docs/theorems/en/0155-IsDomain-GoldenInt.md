# 0155 — `instance : IsDomain GoldenInt`

## Lean type

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

This is not a theorem but an anonymous `instance` registering Mathlib's standard `IsDomain` typeclass for `GoldenInt`.

## Mathematical statement and meaning of the declaration

This declaration tells Mathlib that the `GoldenInt` structure developed so far can be treated as an integral domain.

By this point, `GoldenInt` already has a commutative-ring structure `CommRing GoldenInt`, a `NoZeroDivisors GoldenInt` instance expressing the zero-product property, and a `Nontrivial GoldenInt` instance guaranteeing `0 ≠ 1`.

Thus, mathematically, the declaration packages a commutative ring satisfying

$$
xy=0 \Longrightarrow x=0 \lor y=0
$$

and

$$
0 \neq 1
$$

into Mathlib's standard integral-domain interface.

## Role in the overall proof

Declarations 0148–0152 prove zero-divisor elimination concretely by transporting multiplication to `Zsqrtd 5` through the doubled embedding and then pulling the result back to `GoldenInt`. Declaration 0153 registers that theorem as `NoZeroDivisors GoldenInt`, while 0154 supplies `Nontrivial GoldenInt`.

0155 does not reprove any of those facts. Instead, it uses Mathlib's standard converter

```lean
NoZeroDivisors.to_isDomain
```

to package the already available instances as an `IsDomain` instance.

Conceptually, the flow is

$$
\texttt{CommRing GoldenInt}
+\texttt{NoZeroDivisors GoldenInt}
+\texttt{Nontrivial GoldenInt}
\longrightarrow
\texttt{IsDomain GoldenInt}.
$$

From this point onward, downstream proofs may use Mathlib's generic integral-domain lemmas and typeclass inference instead of relying only on golden-integer-specific zero-product theorems.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt`
- `goldenCommRing : CommRing GoldenInt`
- 0153 `NoZeroDivisors GoldenInt`
- 0154 `Nontrivial GoldenInt`
- Mathlib's `NoZeroDivisors.to_isDomain`

The term itself is only

```lean
NoZeroDivisors.to_isDomain _
```

so the previously registered algebraic structures are recovered through expected-type inference and typeclass search rather than named explicitly in the expression.

## Proof / construction flow

There is no proof script. The instance is defined in one line:

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

Lean reads the expected type `IsDomain GoldenInt`, infers that `_` is `GoldenInt`, and searches the current typeclass environment for the required commutative-ring, no-zero-divisors, and nontriviality instances.

Therefore this declaration is best viewed not as a new mathematical proof but as an interface registration promoting already proved properties into the standard hierarchy.

## Lean-specific processing

The key Lean mechanism here is typeclass inference.

In `NoZeroDivisors.to_isDomain _`, the target type does not need to be written explicitly because the expected type

```lean
IsDomain GoldenInt
```

determines it.

The prerequisites required by the conversion have already been registered as instances in earlier declarations, so the user does not need to wire the proof terms together manually.

After this declaration, later theorems can simply rely on typeclass search to know that `GoldenInt` is an integral domain. This removes the need to pass golden-integer-specific zero-product facts explicitly throughout the downstream development.

## Redundancy and duplication

Declarations 0152–0155 all concern aspects of integral-domain behavior, so they may look repetitive when read in sequence. Their API roles are nevertheless distinct:

- 0152: a reusable named zero-product theorem
- 0153: the standard `NoZeroDivisors` typeclass instance
- 0154: the standard `Nontrivial` typeclass instance
- 0155: integration into the `IsDomain` hierarchy

It would be possible to embed all of these arguments in one large `IsDomain` construction, but the present separation makes the responsibilities and dependency boundaries much easier to audit.

## Optimization candidates

Possible alternatives include:

1. Keep the current `NoZeroDivisors.to_isDomain _` formulation.
2. Write the target type explicitly, for example `NoZeroDivisors.to_isDomain GoldenInt`, if that improves readability.
3. Group declarations 0152–0155 into a tighter local section so the progression from zero-product theorem to domain instance is visually clearer.
4. If Mathlib changes its preferred hierarchy constructor, migrate to the new standard conversion rather than manually rebuilding `IsDomain`.

The current declaration is already extremely short and uses the standard Mathlib conversion directly, so there is little useful optimization available beyond presentation.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself requires the `IsDomain` and `NoZeroDivisors` hierarchy, the conversion `NoZeroDivisors.to_isDomain`, and the already constructed `CommRing` / `Nontrivial` instances for `GoldenInt`.

It is therefore unlikely that all of `Mathlib` is required solely for declaration 0155. The actual minimal import set is governed by the broader `GoldenOrder` module and the tactics used earlier in its construction.

Because no Lean build is performed in this museum pass, the exact minimal import set is unverified. This should be treated as an import-optimization hypothesis rather than a confirmed result.

## Suitability as a Comparator challenge

Yes, although the comparison concerns instance design rather than a mathematical algorithm.

Possible implementations are:

- promotion through `NoZeroDivisors.to_isDomain _`
- direct construction of an `IsDomain` structure literal
- derivation from some stronger existing algebraic structure, if one were already available

Useful comparison criteria include code size, transparency of prerequisite instances, resilience to Mathlib hierarchy changes, quality of error messages, and stability of downstream typeclass resolution.

For this declaration, the standard conversion is the natural winner; the challenge mainly illustrates the value of reusing Mathlib's hierarchy instead of reconstructing it manually.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` portion embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In the source, this `IsDomain GoldenInt` instance appears immediately after 0154 `Nontrivial GoldenInt`, and it is followed by `golden_add_eq`, which exposes the definitional agreement between the raw addition function and standard notation.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The concrete PDF page or section corresponding to this small instance was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

By 0155, the integral-domain structure of `GoldenInt` has been registered in the standard hierarchy. The next stage begins API cleanup, exposing through `@[simp]` the definitional equality between raw operations such as `goldenAdd` and the standard notation `x + y`.
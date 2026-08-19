# 0132 — `instance : Mul GoldenInt`

## Lean type

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

This is not a theorem. It is an anonymous `instance` registering the raw operation `goldenMul`, defined in 0124, as the standard Lean / Mathlib multiplication typeclass `Mul` on `GoldenInt`.

## Mathematical statement and meaning of the declaration

Read `GoldenInt` elements as $x=a+b\varphi$ and $y=c+d\varphi$, with the generator satisfying $\varphi^2=\varphi+1$. The upstream definition of `goldenMul` is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

This implements the coordinate reduction obtained from

$$
(a+b\varphi)(c+d\varphi)=ac+(ad+bc)\varphi+bd\varphi^2
$$

by substituting $\varphi^2=\varphi+1$, giving

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi.
$$

The present declaration connects this golden-integer-specific raw multiplication to the standard notation `x * y`.

## Role in the overall proof

The `GoldenOrder` layer first defines the raw coordinate API consisting of `goldenZero`, `goldenOne`, `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, and `goldenPow`. It then registers these operations with the standard Lean interfaces `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul`.

This declaration is the final primitive-operation registration in that sequence. It allows subsequent coordinate simp lemmas, `AddCommGroup GoldenInt`, `CommRing GoldenInt`, conjugation, norm, divisibility, Euclidean-domain structure, and fifth-power factorization to use the standard expression `x * y` rather than exposing the dedicated name `goldenMul x y`.

A particularly important design point is that the abstract ring structure is not assumed first. Instead, the concrete coordinate multiplication on golden integers is made explicit and only then connected to the standard algebra interface. This makes it easier to audit exactly which concrete operation the downstream ring laws concern.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0124 `goldenMul`
- Lean's standard `Mul` typeclass

The quadratic reduction $\varphi^2=\varphi+1$ has already been compiled into the definition of `goldenMul`, so this `instance` itself requires no new algebraic lemma.

Conceptually, the dependency chain is

$$
\texttt{GoldenInt}\longrightarrow\texttt{goldenMul}\longrightarrow\texttt{Mul GoldenInt}.
$$

## Proof / construction flow

There is no proof script.

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

The structure literal directly supplies `goldenMul` as the binary operation required by `Mul GoldenInt`. Conceptually, this is a one-step interface boundary from raw golden-coordinate multiplication to standard Lean multiplication notation.

## Lean-specific processing

`Mul` is a typeclass containing a multiplication operation, and `⟨goldenMul⟩` is elaborated from the expected type `Mul GoldenInt`, allowing Lean to infer the appropriate constructor and field.

After the instance has been registered, typeclass resolution interprets `x * y` using this multiplication and unfolds it definitionally to `goldenMul x y`. Therefore the coordinate lemmas appearing later in the source can take forms such as

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl

@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

and close with `rfl`, without inserting a theorem-level rewrite between the raw operation and standard notation. This definitional transparency is also advantageous for subsequent simp normalization.

## Redundancy and duplication

`goldenMul` and `Mul GoldenInt` expose the same multiplication through two API layers, so they appear redundant at first sight. Their roles are distinct:

- `goldenMul` is a raw bootstrap operation that can be referenced before the typeclass structure is assembled.
- `Mul GoldenInt` is the standard interface required for `*` notation and participation in Mathlib's generic algebra API.

Placing the reduced coordinate formula for $\varphi^2=\varphi+1$ in `goldenMul` once also avoids repeating the same algebraic expansion throughout downstream proofs.

## Optimization candidates

Four implementation families are worth considering.

1. Inline the coordinate formula directly into the `Mul` instance and remove `goldenMul`.
2. Retain the current separation between the raw operation and the typeclass layer in order to preserve a clear bootstrap structure.
3. Abstract coordinate multiplication for a general quadratic relation $\theta^2=p\theta+q$, then construct the golden case as the specialization $p=q=1$.
4. Recast the implementation through existing Mathlib infrastructure such as `AdjoinRoot` or a quadratic-algebra representation and reuse more generic algebraic structure.

The current approach is not minimal in line count, but it keeps the coordinate arithmetic fully visible and allows many downstream facts to be handled through definitional equality. For an auditable FLT5 formalization, preserving that transparency has significant value.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration itself directly requires only `GoldenInt`, `goldenMul`, and the standard `Mul` interface; it invokes no advanced Mathlib theorem.

A modular source therefore should not need all of `Mathlib` merely for this `instance`. However, the complete `GoldenOrder` module also uses integer arithmetic, ring structure, and later algebra-instance construction, so the true minimal import set is controlled by those dependencies. Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified and this point is explicitly an optimization hypothesis.

## Suitability as a Comparator challenge

Yes. Three implementation families can be compared:

- raw `goldenMul` plus a `Mul` instance
- direct coordinate formula inlined into the `Mul` instance
- a generic quadratic-order / `AdjoinRoot`-based implementation

Useful metrics include the number of coordinate lemmas closed by `rfl`, proof burden when constructing `CommRing`, simp normal forms, clarity of definitional unfolding, generalizability, and downstream FLT5 theorem size.

A specialized coordinate implementation has lower abstraction but greater definitional transparency, while a generic algebra implementation provides greater reuse at the cost of additional abstraction layers. This makes the declaration a small and clear Comparator challenge for measuring that trade-off.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In that source, `Mul GoldenInt` appears immediately after `Sub GoldenInt`, and it is followed by the `@[simp]` coordinate lemmas beginning with `golden_fst_zero`.

Japanese and English PDFs also exist on the target branch, but the concrete page corresponding to this anonymous instance was not identified directly in this pass. Therefore no PDF page or section number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
```

By 0132, the standard registrations for `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` are complete. The next stage begins exposing, through `@[simp]` lemmas, the fact that standard notation reduces definitionally to the raw coordinate definitions.

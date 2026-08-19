# 0153 — `instance : NoZeroDivisors GoldenInt`

## Lean type

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

This is not a theorem but an anonymous `instance` registering Mathlib's standard typeclass `NoZeroDivisors` for `GoldenInt`.

## Mathematical statement and meaning of the declaration

`NoZeroDivisors GoldenInt` exposes the property that if a product of two golden integers is zero, then at least one factor is zero.

Mathematically,

$$
xy=0 \Longrightarrow x=0 \lor y=0.
$$

The mathematical content itself was already proved in the immediately preceding declaration 0152:

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0
```

Declaration 0153 proves no new mathematics. Instead, it places that theorem into the field required by `NoZeroDivisors`, making the result available through Mathlib's generic algebra API.

## Role in the overall proof

Declarations 0148 through 0152 build the machinery needed to prove that `GoldenInt` has no zero divisors.

Schematically,

$$
\texttt{GoldenInt}
\xrightarrow{\texttt{goldenDoubleEmbedding}}
\texttt{Zsqrtd 5}
\longrightarrow
\text{zero-product splitting}
\longrightarrow
\texttt{GoldenInt}.
$$

After 0152 completes that argument as a theorem, 0153 registers the result in the algebra hierarchy. Downstream code can therefore use `NoZeroDivisors GoldenInt` as a standard typeclass assumption instead of referring explicitly to the project-specific theorem name each time.

Thus this declaration is an interface boundary from a concrete coordinate-and-embedding proof back into Mathlib's abstract algebraic world. It is also an important step toward the subsequent `Nontrivial GoldenInt` and `IsDomain GoldenInt` instances.

## Direct dependencies

The direct dependencies are:

- Mathlib's standard typeclass `NoZeroDivisors`;
- 0152 `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`.

The dependency chain is therefore simply

$$
\texttt{GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero}
\longrightarrow
\texttt{NoZeroDivisors GoldenInt}.
$$

Inside 0152, the proof depends on results such as `goldenDoubleEmbedding_mul`, `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`, and `goldenDoubleEmbedding_injective`, but those are indirect dependencies from the perspective of 0153.

## Proof / construction flow

There is no proof script.

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

The structure syntax simply assigns theorem 0152 to the zero-product field required by `NoZeroDivisors`.

Conceptually, the construction is

$$
\text{proved theorem}
\longrightarrow
\text{typeclass field}
\longrightarrow
\text{generic algebra API}.
$$

## Lean-specific processing

The key Lean-specific feature is typeclass registration.

Whenever downstream code requires `[NoZeroDivisors GoldenInt]`, typeclass search can automatically find this anonymous instance. As a result, downstream proofs can use generic Mathlib theorems and instance construction associated with `NoZeroDivisors` rather than explicitly invoking

```lean
GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero h
```

each time.

The `where` syntax also names the field `eq_zero_or_eq_zero_of_mul_eq_zero` explicitly, making the contract between theorem 0152 and the typeclass especially transparent.

## Redundancy and duplication

Declarations 0152 and 0153 contain the same proposition at two API layers, so they are superficially redundant.

Their roles are different:

- 0152 is a named theorem preserving the concrete proof and its provenance;
- 0153 publishes that proof through the standard algebra hierarchy as an instance.

Keeping the named theorem makes the concrete argument auditable. Registering the instance allows downstream abstract code to ignore the implementation details. This two-layer design is natural in Lean library engineering.

## Optimization candidates

Three designs are worth considering.

1. Keep the current design: prove 0152 as a named theorem, then register it in 0153.
2. Remove the independent theorem and prove the zero-product property directly inside the `NoZeroDivisors GoldenInt` instance field.
3. First prove a more general theorem transferring `NoZeroDivisors` across an injective map, then use that abstraction to build the `GoldenInt` instance.

Option 2 may reduce line count. The current design, however, keeps the nontrivial doubled-embedding proof available as a named, inspectable theorem while presenting only its result to the typeclass system. This improves readability and reuse.

For an FLT5 development where proof provenance matters, the existing theorem-to-instance separation is valuable.

## Required Mathlib imports and import optimization

The standalone artifact globally uses `import Mathlib`. This declaration itself directly requires only the definition of `NoZeroDivisors` and the already-established theorem `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`.

Therefore the whole of `Mathlib` should not be required merely for declaration 0153. The true minimal import set is governed by the algebra hierarchy containing `NoZeroDivisors` together with the imports required by the upstream `GoldenOrder` development.

Because no Lean build is performed in this museum pass, the exact minimal import set remains unverified. This is explicitly an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes, although the declaration by itself makes a very small challenge.

Possible implementations include:

- prove a named theorem first and register it as an instance;
- prove the property directly inside the instance field;
- construct the instance through a generic zero-product transfer lemma.

Useful comparison criteria are proof-provenance traceability, reusable theorem surface, simplicity of typeclass inference, code size, and how concise the downstream `IsDomain` construction becomes.

In particular, this is a useful Lean library-design challenge about whether substantive mathematics should remain visible as a named theorem or be embedded directly inside an instance.

## Relation to the PDFs and Lean source

The formal source of truth is the Lean source on the `docs/flt5-theorem-museum-v2` branch together with the immediately preceding 0152 document. The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The specific PDF page corresponding to this `NoZeroDivisors` instance was not identified directly in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order registers that `GoldenInt` is not the trivial one-element ring: the `Nontrivial GoldenInt` instance.

Conceptually it has the form

```lean
instance : Nontrivial GoldenInt := ...
```

and certifies `0 ≠ 1`.

Once 0153 `NoZeroDivisors` and this `Nontrivial` instance are both available, the algebra hierarchy is ready to proceed toward `IsDomain GoldenInt`.
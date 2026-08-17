# 0154 — `instance : Nontrivial GoldenInt`

## Lean type

```lean
instance : Nontrivial GoldenInt := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have := congrArg GoldenInt.fst h
  norm_num at this
```

This is not a theorem but an anonymous `instance` registering Mathlib's standard `Nontrivial` typeclass for `GoldenInt`.

## Mathematical statement and meaning of the declaration

`Nontrivial GoldenInt` states that `GoldenInt` contains at least two distinct elements. Here the proof chooses the standard elements `0` and `1` and proves

$$
0 \neq 1.
$$

`GoldenInt` is implemented by integral coordinates, with the standard zero and one corresponding to

$$
0=(0,0),\qquad 1=(1,0).
$$

Therefore, if these two golden integers were equal, comparison of the first coordinates would force the integer equality `0 = 1`, which is impossible.

## Role in the overall proof

The preceding declaration 0153 registers the zero-product result proved in 0152 as `NoZeroDivisors GoldenInt`. However, `NoZeroDivisors` alone does not assert that the ring is nondegenerate.

0154 supplies the missing standard typeclass saying that `GoldenInt` is nontrivial, preparing the immediately following declaration

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

Thus the conceptual flow through 0153–0155 is

$$
\texttt{NoZeroDivisors GoldenInt}
+\texttt{Nontrivial GoldenInt}
\longrightarrow
\texttt{IsDomain GoldenInt}.
$$

It is a short but important bridge from the concrete zero-divisor elimination developed since 0148 into Mathlib's integral-domain hierarchy.

## Direct dependencies

The declaration directly uses:

- `GoldenInt`
- `Zero GoldenInt`
- `One GoldenInt`
- the projection `GoldenInt.fst`
- the standard `Nontrivial` typeclass
- `congrArg`
- `norm_num`

Although 0153 `NoZeroDivisors GoldenInt` is mathematically paired with this declaration in the next `IsDomain` construction, it is not directly referenced by the proof term of 0154 itself.

## Proof / construction flow

The proof is very short.

```lean
refine ⟨⟨0, 1, ?_⟩⟩
```

chooses `0` and `1` as the witnesses required by `Nontrivial GoldenInt`, leaving the goal that they are distinct.

Next,

```lean
intro h
```

introduces the contrary assumption `h : 0 = 1`.

The equality is projected to the first coordinate by

```lean
have := congrArg GoldenInt.fst h
```

so an equality of golden integers becomes an equality of their integer first coordinates.

Finally,

```lean
norm_num at this
```

normalizes the resulting numerical equality `0 = 1` and closes the contradiction.

Mathematically the proof is simply

$$
(0,0)=(1,0)
\Longrightarrow
0=1
\Longrightarrow
\bot.
$$

Lean exposes the witness construction and the projection step explicitly.

## Lean-specific processing

`Nontrivial α` is a typeclass expressing the existence of two distinct elements. The term `⟨⟨0, 1, ?_⟩⟩` explicitly builds the internal witness for this class.

`congrArg GoldenInt.fst h` is a standard Lean pattern for reducing equality of a compound structure to equality of one selected coordinate. Instead of destructing the equality or using extensionality in reverse, the proof projects only the coordinate needed for the contradiction, keeping the proof state small.

The final `norm_num at this` does not need to reason about `GoldenInt` itself. Once the `Zero` / `One` instances and `fst` projection reduce definitionally to the integer equality `0 = 1`, the numerical tactic can discharge the contradiction.

## Redundancy and duplication

Because `GoldenInt` has explicit `ℤ × ℤ`-style coordinates, nontriviality is structurally obvious, so this instance carries little new mathematical content.

The proof could also choose the raw coordinates `⟨0,0⟩` and `⟨1,0⟩` directly. The present version instead uses the already registered standard notation `0` and `1`, keeping the declaration aligned with the public algebra API.

It would also be possible in principle to fold this nontriviality proof into a larger domain construction, but retaining `Nontrivial GoldenInt` as its own instance makes the typeclass hierarchy boundary explicit.

## Optimization candidates

Several alternatives are worth considering:

1. Keep the current proof using `0`, `1`, `congrArg GoldenInt.fst`, and `norm_num`.
2. Use a shorter constructor expression if the expected structure shape remains clear.
3. Reuse a generic `Nontrivial` instance inherited from a product, structure, or suitable equivalence if one is available without introducing dependency cycles.
4. If `zero_ne_one` is already derivable at this stage, construct `Nontrivial` directly from that theorem.

Options 3 and 4 require care because they may depend on algebraic instances that are themselves downstream of `Nontrivial`. The current proof has few prerequisites and makes the bootstrap dependency explicit, which is favorable for auditability.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration directly uses `Nontrivial`, `congrArg`, integer normalization through `norm_num`, and the upstream `Zero` / `One` instances for `GoldenInt`.

It is therefore unlikely that all of `Mathlib` is required solely for 0154. A narrower import set would primarily need the basic typeclass infrastructure and the module providing `norm_num`, in addition to the upstream `GoldenInt` definitions.

No Lean build is performed in this museum pass, so the exact minimal import set is unverified. This point should therefore be treated as an import-optimization hypothesis rather than a confirmed result.

## Suitability as a Comparator challenge

Yes, although it would be a very small Comparator challenge.

Possible implementations include:

- `congrArg GoldenInt.fst` followed by `norm_num`
- direct use of structure-constructor injectivity
- inheritance of a generic `Nontrivial` instance through a product, subtype, or `Equiv`
- an algebra-hierarchy-driven construction from `zero_ne_one`

Useful comparison criteria are the number of prerequisite instances, risk of bootstrap cycles, code size, transparency of the proof state, and coupling to the subsequent `IsDomain` construction.

The mathematics is elementary, but the declaration is a useful test of where nontriviality should enter a Lean typeclass hierarchy.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder` portion embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this `Nontrivial GoldenInt` instance appears immediately after 0153 `NoZeroDivisors GoldenInt` and immediately before `IsDomain GoldenInt`.

The branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and English PDF `FLT5-main-en-v0-r1.pdf`. The concrete PDF page or section corresponding to this small instance was not directly identified in this pass, so no page or section number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

With the zero-divisor result from 0153 and nontriviality from 0154 now registered, the next step packages them into the standard `IsDomain` hierarchy.
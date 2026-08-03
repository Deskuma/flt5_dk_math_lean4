# 0014 — `GN5_two_one`

> This is the English translation of the Japanese canonical edition.

## Lean type

```lean
theorem GN5_two_one : GN5 2 1 = 121 := by
  norm_num [GN5]
```

The fully qualified name is `DkMath.FLT.Five.GN5_two_one`.

## Mathematical statement

Evaluating `GN5` at gap $g=2$ and base coordinate $y=1$ gives $121=11^2$.

$$
GN5(2,1)=2^4+5\cdot2^3+10\cdot2^2+10\cdot2+5=121
$$

Since $g+y=3$, the cyclotomic form gives

$$
GN5(2,1)=3^4+3^3+3^2+3+1=121
$$

## Role in the complete proof

This is the second closed evaluation after `GN5_one_one`. It is a smoke test for the definition and numerical normalization on another input. The value $121=11^2$ has a different local prime-factor pattern from $31$. The following concrete clean-channel example nevertheless uses $(g,y,q)=(1,1,31)`, so this theorem is not a direct dependency of the general FLT5 reduction.

## Direct dependencies

- `DkMath.FLT.Five.GN5`
- the `norm_num` tactic

It could also be derived from `GN5_eq_homogeneous_cyclotomic 2 1`, but the current proof unfolds the definition directly.

## Proof flow

1. `norm_num [GN5]` unfolds `GN5`.
2. It substitutes $g=2$ and $y=1$.
3. It normalizes natural-number powers, multiplication, and addition.
4. It closes the equality with $121$.

## Lean-specific processing

`norm_num` reflectively normalizes a closed natural-number equality. `[GN5]` lists the definition to unfold. No variables, hypotheses, case splits, `ring`, `omega`, primality tests, or divisibility arguments are needed.

## Redundancy and duplication

The proof shape is identical to `GN5_one_one`. This is useful as an intentional smoke test, although its public-API value is mainly regression checking and illustration because the general proof does not reference it.

## Optimization candidates

A larger collection of concrete evaluations could be organized as `example`s or a table-driven test. Keeping a named theorem, however, makes reuse from documents and later proofs straightforward. Routing the proof through the cyclotomic identity would expose meaning but add a dependency to a simple closed computation.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. Direct requirements are natural-number arithmetic, powers, and `norm_num`. A narrower combination based on `Mathlib.Tactic.NormNum` may suffice, but the exact minimal imports are unverified because no Lean build was run.

## Comparator challenge suitability

Suitable approaches include:

1. `norm_num [GN5]`
2. `unfold GN5; norm_num`
3. rewriting with `GN5_eq_homogeneous_cyclotomic` and then using `norm_num`
4. testing whether `decide` or `native_decide` applies

Useful comparison axes are brevity, proof-term transparency, reuse of general lemmas, imports, and resilience to definition changes.

## Next declaration to read

The next major declaration is `DkMath.FLT.Five.CleanGN5Channel`. It is a `Prop`-valued structure rather than a theorem. It packages the conditions that a prime $q$ divides `GN5 g y`, does not divide the gap $g$, and has $q^2$ not dividing `GN5 g y`.

## Sources versus interpretation

The type, proof, declaration order, value $121$, and next major declaration are verified in `Flt5DkMath/FLT5StandAlone.lean`, including the generated `GN5.lean` and `CleanChannel.lean` sources. The role analysis, import minimization, and Comparator proposals include explanatory analysis or unverified suggestions. No Lean build was run.
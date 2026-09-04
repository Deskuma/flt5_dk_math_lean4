# 0126 — `GoldenInt.ext`

## Lean type

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all
```

`GoldenInt.ext` states that two `GoldenInt` values are equal as structures whenever both their `fst` and `snd` coordinates agree.

## Mathematical statement

`GoldenInt` represents the integral pair

$$
x=a+b\varphi
$$

with `fst = a` and `snd = b`. Hence, if

$$
a=c
$$

and

$$
b=d,
$$

then

$$
a+b\varphi=c+d\varphi.
$$

This theorem expresses uniqueness of the coordinate representation as Lean structure equality.

At this point no separate proof of linear independence of $1,\varphi$ is needed. `GoldenInt` is itself defined as a structure with two integer fields, so equality of those two fields is enough to obtain equality of the structures.

## Role in the whole proof

By 0125 `goldenPow`, the carrier and raw arithmetic of `GoldenInt` have been defined. This theorem marks the transition to proving equalities of those operations by reducing a `GoldenInt` equality to two integer-coordinate equalities.

Immediately afterward, instances for `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` are registered, followed by additive-group and ring laws, integer embeddings, conjugation, norm identities, and related equality proofs. Because this theorem carries the `@[ext]` attribute, the `ext` tactic can split a `GoldenInt` equality goal into its `fst` and `snd` coordinate goals.

Thus this theorem is the proof interface that turns golden-integer algebraic laws into coordinate calculations.

## Direct dependencies

The only direct mathematical declaration required is `GoldenInt` itself.

The proof also uses Lean's structure case analysis and simplifier infrastructure:

1. `GoldenInt`
2. `cases`
3. `simp_all`
4. the `@[ext]` attribute

It does not directly depend on 0120–0125 (`goldenOne`, `goldenAdd`, `goldenNeg`, `goldenSub`, `goldenMul`, or `goldenPow`). It appears after them in dependency-reading order, but its logical content follows from the carrier structure alone.

## Proof flow

The proof has three steps.

1. `cases x` exposes the two integer fields of `x`.
2. `cases y` does the same for `y`.
3. `simp_all` uses `hfst` and `hsnd` to simplify the remaining structure equality to reflexivity.

Conceptually, it proves the injectivity principle

$$
(x.fst=x'.fst)\land(x.snd=x'.snd)\Longrightarrow x=x'.
$$

## Lean-specific processing

### 1. The `@[ext]` attribute

`@[ext]` registers this theorem as an extensionality rule. Later proofs can therefore use a style such as

```lean
ext <;> simp [goldenAdd, goldenMul]
```

So this theorem is not merely an ordinary lemma; it is also a type-specific equality decomposition rule used by the `ext` tactic.

### 2. Structure `cases`

`cases x` and `cases y` return the abstract `GoldenInt` values to constructor form. Since `GoldenInt` has only two fields, no branching occurs; the coordinate values simply become explicit in the local context.

### 3. `simp_all`

After the structures are decomposed, `hfst` and `hsnd` become integer equalities. `simp_all` simplifies both the goal and the local hypotheses using those equalities and closes the final reflexive equality.

No algebra tactic is involved. There is no need for `ring`, `omega`, `norm_num`, or cast manipulation.

### 4. Implicit arguments

`x` and `y` are implicit binders `{x y : GoldenInt}`. In ordinary uses they are inferred from the coordinate-equality hypotheses, so callers do not need to provide them explicitly.

## Redundancy and duplication

Lean can often generate or derive extensionality theorems for structures, so the mathematical content of `GoldenInt.ext` is highly standard.

The proof script

```lean
cases x
cases y
simp_all
```

could also potentially be replaced by direct constructor injectivity or by a proof based on `cases hfst; cases hsnd; rfl`.

Nevertheless, explicitly providing `GoldenInt.ext` and registering it with `@[ext]` stabilizes the downstream proof API. Later code can invoke `ext` without depending on details of the internal representation, so this is not merely pointless duplication.

## Optimization candidates

### Candidate A — keep the current form

This is the clearest option. It explicitly records extensionality for the two-field structure and guarantees downstream `ext` support.

### Candidate B — rely on a generated ext theorem

One could let Lean / Mathlib generate an extensionality rule and remove the handwritten theorem.

The benefit is less boilerplate. The downside is that the generated name, attribute registration, and behavior under future structure changes become less explicit than with a stable handwritten API.

### Candidate C — move closer to equality elimination

A proof based on `cases hfst; cases hsnd; rfl` may reduce dependence on `simp_all` and stay closer to kernel reduction. The exact shortest form has not been Lean-build-verified in this museum pass.

### Candidate D — standardize later proofs around extensionality

Subsequent ring laws could consistently use patterns such as

```lean
apply GoldenInt.ext <;> simp [goldenAdd, goldenMul, goldenNeg]
```

This improves uniformity, though larger polynomial identities may still be clearer when coordinate decomposition is followed by `ring`.

## Required Mathlib import and import optimization

The branch's `Flt5DkMath/FLT5StandAlone.lean` imports

```lean
import Mathlib
```

for the standalone development as a whole.

This theorem's mathematical dependency is only structure equality for `GoldenInt`. Its implementation additionally uses the `@[ext]` attribute and the `simp_all` tactic, so the relevant Lean / Mathlib infrastructure for those features must be imported.

A narrower import containing extensionality infrastructure and basic tactics is a plausible optimization candidate, but the exact minimal module set was not verified by a Lean build in this pass. Therefore this article does not claim either that all of `Mathlib` is necessary or that a specific fine-grained import is sufficient.

## Comparator challenge suitability

 **Suitable.** The theorem is small, but it makes a useful comparison challenge for alternative ways of proving structure equality in Lean.

Candidate implementations include:

1. the current `cases` + `simp_all`
2. constructor injectivity / equality elimination
3. a generated extensionality theorem
4. explicit field rewriting ending in `rfl`

Useful evaluation criteria are proof-term simplicity, dependence on `simp`, maintainability if fields are added, reuse through the `@[ext]` API, and consistency with downstream algebraic proofs.

## Correspondence with existing materials

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

This pass did not directly inspect the exact PDF page or section corresponding to `GoldenInt.ext`, so no page number or PDF-specific narrative is inferred.

The formal source of truth is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

Immediately after this theorem, typeclass-instance registration begins. The first declaration is

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

By 0126 the raw carrier, raw arithmetic, and equality interface are all available. The next step connects the raw definition `goldenZero` to Lean's standard `Zero GoldenInt` API.
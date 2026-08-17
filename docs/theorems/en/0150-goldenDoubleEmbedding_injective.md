# 0150 — `goldenDoubleEmbedding_injective`

## Lean type

```lean
theorem goldenDoubleEmbedding_injective :
    Function.Injective goldenDoubleEmbedding := by
  intro x y h
  have hsnd : x.snd = y.snd := congrArg Zsqrtd.im h
  have hfst : 2 * x.fst + x.snd = 2 * y.fst + y.snd :=
    congrArg Zsqrtd.re h
  apply GoldenInt.ext
  · omega
  · exact hsnd
```

This is a `theorem`. It proves that the function `goldenDoubleEmbedding : GoldenInt → Zsqrtd 5`, defined in 0148, is injective.

## Mathematical statement and meaning of the declaration

Write an element of `GoldenInt` as

$$
x=a+b\varphi,\qquad \varphi=\frac{1+\sqrt5}{2}.
$$

The doubled embedding from 0148 corresponds to

$$
2x=(2a+b)+b\sqrt5,
$$

so in coordinates it is

$$
(a,b)\longmapsto(2a+b,b).
$$

The theorem says that this coordinate transformation loses no information.

Indeed, if

$$
(2a+b,b)=(2c+d,d),
$$

then equality of the second coordinates gives $b=d$. Substituting this into the first-coordinate equality gives

$$
2a+b=2c+b,
$$

hence $a=c$. Therefore the original coordinates agree and $x=y$.

This map is not the ordinary ring embedding sending $x$ itself into `Zsqrtd 5`; rather, it clears the denominator $2$ and sends the doubled element $2x$ into integral `Zsqrtd 5` coordinates. Injectivity is nevertheless exactly what the downstream argument needs in order to pull zero information back from `Zsqrtd 5` to `GoldenInt`.

## Role in the overall proof

0148 `goldenDoubleEmbedding` provides an auxiliary map connecting the explicit golden-integer ring to the domain structure available on `Zsqrtd 5`. In 0149, the development supplies the instance `Zsqrtd.Nonsquare 5`, expressing that $5$ is not a square. The present theorem then proves that this connection is injective, so the target representation still distinguishes source elements.

The immediately following theorem `goldenDoubleEmbedding_mul` establishes the multiplication relation

$$
E(x)E(y)=2E(xy).
$$

Later, `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` uses the fact that a zero product in `Zsqrtd 5` forces one factor to be zero. At the final step, the present injectivity theorem converts

$$
E(x)=E(0)\Longrightarrow x=0.
$$

Thus this theorem is the return path in the transfer of the no-zero-divisors property from `Zsqrtd 5` back to `GoldenInt`.

## Direct dependencies

The direct dependencies are:

- 0148 `goldenDoubleEmbedding`
- `GoldenInt.ext`
- `Function.Injective`
- `Zsqrtd.re`
- `Zsqrtd.im`
- `congrArg`
- `omega`

The definition of `goldenDoubleEmbedding` is

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

so applying `Zsqrtd.im` and `Zsqrtd.re` to an equality `h : goldenDoubleEmbedding x = goldenDoubleEmbedding y` yields exactly the two integer coordinate equalities needed for the proof.

## Proof / construction flow

The proof has four steps.

1. `intro x y h` unfolds injectivity and introduces two golden integers together with equality of their embedded images.
2. `congrArg Zsqrtd.im h` extracts the equality `x.snd = y.snd` of the second coordinates.
3. `congrArg Zsqrtd.re h` extracts the transformed first-coordinate equality `2*x.fst+x.snd = 2*y.fst+y.snd`.
4. `GoldenInt.ext` reduces equality of the source structures to equality of their two coordinates; the first coordinate is discharged by `omega`, and the second by `hsnd`.

For the first coordinate, `omega` uses `hfst` together with `hsnd` as local hypotheses and derives `x.fst = y.fst` by linear integer arithmetic.

## Lean-specific processing

`Function.Injective goldenDoubleEmbedding` is definitionally of the form

```lean
∀ ⦃a b⦄, goldenDoubleEmbedding a = goldenDoubleEmbedding b → a = b
```

so it can be opened directly with `intro x y h`.

`congrArg` is the standard congruence operation that applies the same function to both sides of an equality. Here, using `Zsqrtd.im` and `Zsqrtd.re` extracts coordinate equalities from equality of the entire target structures without manually destructuring them.

Finally, `apply GoldenInt.ext` changes equality of `GoldenInt` structures into two coordinate goals. `omega` is well suited to the first goal because it is linear arithmetic over integers involving the coefficient `2` and the already-known equality of second coordinates.

## Redundancy and duplication

Introducing `hsnd` and `hfst` separately has a small amount of boilerplate: mathematically it is simply unpacking the two coordinates of the embedding equality. The explicit form is nevertheless valuable because it makes completely visible which coordinate preserves which information.

The proof also crosses two extensionality layers manually: `Zsqrtd.re/im` on the target side and `GoldenInt.ext` on the source side. Since the theorem is short, abstracting this pattern further could make the simple coordinate mechanism harder rather than easier to audit.

## Optimization candidates

The current proof is already a strong candidate for the preferred form: it is short and exposes the mathematics directly.

One alternative would be to package `goldenDoubleEmbedding` as an additive homomorphism or linear-map-like structure and prove injectivity from a trivial kernel. However, the downstream development mainly needs injectivity and a special doubled multiplication relation; the map is not being used as an ordinary ring homomorphism, so the additional abstraction may provide limited benefit.

The use of `omega` could also be replaced by a more manual integer-cancellation proof, but the current tactic exactly matches the nature of the goal: linear integer arithmetic. A structure-level abstraction would become more attractive only if later code repeatedly needed additive-hom or embedding APIs for the same map.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. Directly, this theorem uses `Function.Injective`, `congrArg`, the coordinate API for `Zsqrtd`, the `omega` tactic, and the already-defined `GoldenInt`, `goldenDoubleEmbedding`, and `GoldenInt.ext`.

A modular source could therefore potentially replace the broad import with the upstream `GoldenOrder` dependencies plus the Mathlib module providing `Zsqrtd` and the import providing `omega`. Because no Lean build is performed in this museum pass, the exact minimal import set for the Mathlib v4.33.0 line is not verified. Any concrete import reduction should therefore be treated as an import-audit candidate and checked by building the isolated module.

## Suitability as a Comparator challenge

Yes. Although small, it supports a useful three-way comparison:

- the current `congrArg re/im` + `GoldenInt.ext` + `omega` proof;
- direct target-side destructuring with `cases` or extensionality followed by coordinate arithmetic;
- promoting `goldenDoubleEmbedding` to an additive-hom / linear-map-like structure and proving injectivity through its kernel.

Useful comparison metrics include proof length, amount of definitional unfolding, dependence on automation, reusability, and how cleanly each version connects to the later zero-divisor transfer. The current proof has low abstraction but makes the information-preserving transformation $(a,b)\mapsto(2a+b,b)$ maximally explicit.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this theorem appears immediately after 0149 `goldenFiveNonsquare` and is followed by `goldenDoubleEmbedding_mul` and `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`.

The branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The specific PDF page corresponding to this small injectivity lemma was not identified in this pass, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem goldenDoubleEmbedding_mul (x y : GoldenInt) :
    goldenDoubleEmbedding x * goldenDoubleEmbedding y =
      (2 : Zsqrtd 5) * goldenDoubleEmbedding (goldenMul x y) := by
  ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

0150 proves that the doubled embedding preserves enough information to distinguish source elements. The next theorem supplies the multiplication bridge between `GoldenInt` and `Zsqrtd 5`. Together they complete the setup needed to transfer zero-product information from the target ring back to the source ring.
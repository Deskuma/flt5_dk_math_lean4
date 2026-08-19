# 0148 — `goldenDoubleEmbedding`

## Lean type

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

This is not a theorem but a `def`. It defines an explicit coordinate map sending an element of `GoldenInt` into `Zsqrtd 5`.

## Mathematical statement and meaning of the declaration

Read an element of `GoldenInt` as

$$
x=a+b\varphi
$$

and interpret the golden generator as

$$
\varphi=\frac{1+\sqrt5}{2}.
$$

Then

$$
2x=2a+b+b\sqrt5.
$$

`goldenDoubleEmbedding` records this doubled expression as the integral `Zsqrtd 5` coordinate pair

$$
(2a+b,\ b).
$$

The word `DoubleEmbedding` in the name is therefore essential. The map does not send $x$ itself directly into $\mathbb Z[\sqrt5]$; it sends the denominator-cleared element $2x$. It is an integral coordinate change between the golden order $\mathbb Z[\varphi]$ and `Zsqrtd 5` that avoids introducing a denominator of $2$.

## Role in the overall proof

The map is introduced immediately after `goldenCommRing`, where `GoldenInt` has been completed as a commutative ring. Its purpose is not to identify `GoldenInt` outright with Mathlib's `Zsqrtd 5`, but to transfer the later zero-divisor argument to the `Zsqrtd 5` side.

The declarations following it are `goldenFiveNonsquare`, `goldenDoubleEmbedding_injective`, and `goldenDoubleEmbedding_mul`, followed by

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  ...
```

Thus the conceptual flow is

$$
\mathbb Z[\varphi]
\xrightarrow{\;x\mapsto 2x\;}
\mathbb Z[\sqrt5]
\longrightarrow
\text{zero-divisor control}.
$$

The standalone source commentary explicitly states that this doubled map is used only to certify the absence of zero divisors. Accordingly, this definition is not itself the FLT5 descent step; it is an infrastructure bridge used to move the golden coordinate ring toward domain and Euclidean-domain structure.

## Direct dependencies

The declaration directly depends on:

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`
- `Zsqrtd 5`
- integer addition and multiplication and the numeral `2`

The definition itself has no theorem-level dependency. Although it appears immediately after 0147 `goldenCommRing`, its defining expression only needs the coordinates of `GoldenInt`; it does not intrinsically require the `CommRing GoldenInt` instance.

Mathematically, its background identity is

$$
2(a+b\varphi)=(2a+b)+b\sqrt5.
$$

Lean does not prove this identity by expanding `φ` or a square root at this point. Instead, the integral coordinate formula `⟨2*a+b,b⟩` is adopted directly.

## Proof / construction flow

Because this is a `def`, there is no proof script. The function reads the two coordinates of `x : GoldenInt` and directly constructs the two coordinates of an element of `Zsqrtd 5`:

```lean
⟨2 * x.fst + x.snd, x.snd⟩
```

The first coordinate is $2a+b$ and the second is $b$. This directly produces the denominator-cleared golden expression.

## Lean-specific processing

`Zsqrtd 5` can be constructed from two integer coordinates using constructor notation `⟨_, _⟩`, so the map remains definitionally transparent.

An important design point is that the map is not packaged here as a `RingHom` or `AlgHom`. Indeed, its later multiplicative compatibility is not the ordinary homomorphism law

$$
f(xy)=f(x)f(y),
$$

but, because of the doubling,

$$
f(x)f(y)=2f(xy),
$$

proved separately as `goldenDoubleEmbedding_mul`. Therefore forcing `goldenDoubleEmbedding` into the standard `RingHom` interface would be mathematically inappropriate for this target.

The later injectivity proof applies `congrArg` to `Zsqrtd.im` and `Zsqrtd.re` to recover coordinate equalities. This confirms that the present definition is intentionally a concrete coordinate map designed for easy unfolding in downstream proofs.

## Redundancy and duplication

The coordinate transformation

$$
(2a+b,b)
$$

is unfolded again in later injectivity and multiplication proofs, so the same linear change of coordinates becomes visible more than once. However, the raw formula is centralized in this definition, and later theorems merely unfold `goldenDoubleEmbedding`, so the mathematical duplication is limited.

There is also a naming subtlety: `Embedding` in `goldenDoubleEmbedding` is descriptive mathematics, not Lean's `Embedding` structure. At this point the declaration is merely a function, and its injectivity is only proved later. Readers should distinguish the mathematical name from the actual Lean type.

## Optimization candidates

Three main alternatives are worth considering.

1. Keep the present simple function and prove injectivity and multiplicative compatibility as separate theorems.
2. After injectivity is established, additionally package the map as `GoldenInt ↪ Zsqrtd 5` so that injectivity becomes part of the API.
3. Abstract the construction as a basis-change map between quadratic integer orders of discriminant $5$.

Turning this exact map into a `RingHom` is not directly appropriate. Because of the doubling, ordinary multiplicativity does not hold; the source instead proves `f(x)f(y)=2f(xy)`. A genuine ring embedding would require a different target, such as a suitable subring or a type in which division by $2$ is represented.

For the local purpose of excluding zero divisors, the current design is therefore compact and efficient.

## Required Mathlib imports and import optimization

The standalone artifact uses `Mathlib` globally. This declaration itself requires only the `GoldenInt` definition, the `Zsqrtd` type and constructor, and basic integer arithmetic.

Therefore importing all of `Mathlib` should not be necessary for this definition alone. A modular source would likely need only the Mathlib module providing `Zsqrtd`, together with the upstream `GoldenInt` definitions.

However, no Lean build is run in this pass, and the import lines of the original modular `GoldenOrder.lean` were not directly inspected during this run. Consequently, the exact minimal module name is left unasserted and this remains an import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. Useful variants include:

- the current raw coordinate function;
- a version packaged as an injective `Embedding`;
- an abstraction as a general quadratic-order basis change;
- a genuine ring embedding into a target that permits the denominator $2$.

Comparison metrics include the size of the downstream zero-divisor proof, transparency under unfolding, structural/typeclass overhead, natural expression of the multiplicative relation, and reusability for other quadratic orders.

This is a good example where more packaging is not automatically better. For the present goal, explicitly retaining the nonstandard doubled multiplicative law may make the proof architecture clearer than forcing the map into a standard homomorphism structure.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this definition occurs immediately after `goldenCommRing`, and the module commentary explicitly states that the doubled map is used to certify the absence of zero divisors.

The target branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this definition was not identified directly in this run, so no page number is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
instance goldenFiveNonsquare : Zsqrtd.Nonsquare 5 := by
  refine ⟨fun n h => ?_⟩
  ...
```

Before `Zsqrtd 5` can be used for zero-divisor control, the development first supplies an instance asserting that $5$ is not a natural-number square. After that come `goldenDoubleEmbedding_injective` and `goldenDoubleEmbedding_mul`, leading to the zero-divisor theorem for `GoldenInt` itself.
# 0152 — `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`

## Lean type

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have hemb : goldenDoubleEmbedding x * goldenDoubleEmbedding y = 0 := by
    rw [goldenDoubleEmbedding_mul]
    rw [show goldenMul x y = 0 by exact h]
    rfl
  rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hemb with hx | hy
  · left
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding x = 0 := hx
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl
  · right
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding y = 0 := hy
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl
```

This is a theorem. It states that if a product in `GoldenInt` is zero, then at least one factor is zero. In other words, it proves the zero-product property in exactly the form required by the subsequent `NoZeroDivisors GoldenInt` instance.

## Mathematical statement

The statement is

$$
xy=0 \Longrightarrow x=0 \lor y=0.
$$

Here `GoldenInt` is the coordinate ring of elements $a+b\varphi$ with $\varphi^2=\varphi+1$. The proof uses the doubled embedding from 0148,

$$
E(a+b\varphi)=(2a+b)+b\sqrt5.
$$

By 0151,

$$
E(x)E(y)=2E(xy).
$$

Therefore, if $xy=0$, then the product $E(x)E(y)$ is zero in `Zsqrtd 5`. The zero-product theorem already available on the `Zsqrtd 5` side, supported by the nonsquare instance from 0149, yields $E(x)=0$ or $E(y)=0$. Finally, injectivity from 0150 pulls this back to $x=0$ or $y=0$.

Thus the theorem is a bridge theorem transferring absence of zero divisors from the established $\mathbb Z[\sqrt5]$ setting back to the explicit golden-integer coordinate ring.

## Role in the overall proof

The doubled-embedding machinery prepared in 0148–0151 is collected here for the first time into a direct algebraic consequence.

Conceptually the dependency chain is

$$
\texttt{goldenDoubleEmbedding}
\rightarrow
\texttt{goldenFiveNonsquare}
\rightarrow
\texttt{goldenDoubleEmbedding\_injective}
\rightarrow
\texttt{goldenDoubleEmbedding\_mul}
\rightarrow
\texttt{GoldenInt.eq\_zero\_or\_eq\_zero\_of\_mul\_eq\_zero}.
$$

Immediately afterward, the source registers

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

and then proceeds to `Nontrivial GoldenInt` and `IsDomain GoldenInt`. Hence this theorem is the decisive bridge upgrading `GoldenInt` from a commutative ring toward an integral-domain structure.

The later FLT5 development uses norm arithmetic, divisibility, units, Euclidean-domain structure, gcd theory, and fifth-power factorization, so the absence of zero divisors is a foundational algebraic prerequisite.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt`
- `goldenDoubleEmbedding`
- `goldenDoubleEmbedding_mul`
- `goldenDoubleEmbedding_injective`
- `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`
- `GoldenInt.ext`

In addition, the ability to use the zero-product theorem on `Zsqrtd 5` is supported in this section by 0149 `goldenFiveNonsquare : Zsqrtd.Nonsquare 5`.

## Proof flow

The proof first transports the hypothesis

```lean
h : x * y = 0
```

to the doubled-embedding side by constructing

```lean
hemb : goldenDoubleEmbedding x * goldenDoubleEmbedding y = 0.
```

It does so through

```lean
rw [goldenDoubleEmbedding_mul]
rw [show goldenMul x y = 0 by exact h]
rfl
```

The first rewrite applies the scaled multiplicative law from 0151. The second converts the standard multiplication hypothesis into the raw multiplication form expected in that formula. The remaining equality is definitional.

Next,

```lean
rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hemb with hx | hy
```

splits the zero product in `Zsqrtd 5` into two branches.

In the first branch one has $E(x)=0$; in the second one has $E(y)=0$. In each branch, 0150 injectivity is applied, and the equality

```lean
goldenDoubleEmbedding 0 = 0
```

is established by `ext <;> rfl`, pulling the zero conclusion back to the original `GoldenInt` value.

## Lean-specific processing

### `show goldenMul x y = 0 by exact h`

The hypothesis `h` is expressed using the standard notation `x * y = 0`, while the right-hand side of the 0151 formula contains the raw function `goldenMul x y`. Since the `Mul GoldenInt` instance is defined by `goldenMul`, these expressions are definitionally equal, so `exact h` suffices.

### `rcases ... with hx | hy`

The disjunction returned by the `Zsqrtd` zero-product theorem is split into two branches, and `left` or `right` selects the corresponding side of the final disjunction.

### `apply goldenDoubleEmbedding_injective`

Injectivity is used in the usual direction: to prove equality of original values, it is enough to prove equality of their images. Thus a goal such as `x = 0` becomes `E(x)=E(0)`.

### `by ext <;> rfl`

The equality between the zero element of `Zsqrtd 5` and `goldenDoubleEmbedding 0` is checked coordinatewise by extensionality and definitional reduction. There is almost no mathematical content here; the step simply connects two concrete zero representations for Lean.

## Redundancy and duplication

The proof contains two symmetric branches that differ only by exchanging `x` and `y`. This is deliberate duplication produced by the disjunctive zero-product theorem and keeps the proof structure explicit.

The line

```lean
rw [show goldenMul x y = 0 by exact h]
```

could potentially be written using a bridge lemma such as `golden_mul_eq`. The current form, however, directly exploits definitional equality between the raw operation and the standard multiplication instance and therefore avoids an extra theorem-level rewrite dependency.

Likewise, a dedicated simp lemma for `goldenDoubleEmbedding 0 = 0` could remove the repeated `ext <;> rfl`, but the local expression is already very small.

## Optimization candidates

1. Add a `[simp]` lemma for `goldenDoubleEmbedding 0 = 0` and shorten both branches with `simpa`.
2. Abstract a reusable theorem transferring the zero-product property along an injective scaled multiplicative map.
3. Represent the doubled embedding with a more structured map carrying injectivity and scaled multiplicative compatibility as reusable data.
4. Build `GoldenInt` through a generic quadratic-order / `AdjoinRoot` construction and inherit an existing domain structure where possible.

The current implementation, however, keeps the exact FLT5-relevant coordinates and proof provenance highly visible. A more abstract implementation could reduce line count while making the concrete reason for the domain property harder to audit.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, as confirmed in the generated repository source.

This theorem itself effectively needs the `Zsqrtd` type and zero-product theorem, `Function.Injective`, typeclass-based ring operations, extensionality, and basic rewriting. The tactics `ring` and `omega` are not used directly here, although they occur in the proofs of its immediate dependencies 0150 and 0151.

Therefore the module could likely use a narrower import set than all of `Mathlib`. The exact minimal imports are not verified here because no Lean build is performed in this museum pass, so this remains an explicit optimization hypothesis.

## Comparator challenge suitability

Yes. At least three approaches can be compared:

- the current transfer through the doubled embedding;
- a direct coordinate proof of the zero-product property in `GoldenInt`;
- reuse of an existing domain structure from a generic quadratic-order / `AdjoinRoot` implementation.

Useful metrics include proof length, dependence on nonlinear integer arithmetic, amount of reused Mathlib infrastructure, definitional transparency, simplicity of the downstream `NoZeroDivisors` / `IsDomain` instances, and auditability of the FLT5-specific code.

A direct coordinate proof is likely to require heavier polynomial reasoning, whereas the doubled-embedding approach delegates the difficult domain property to `Zsqrtd` and keeps the local proof compact. This trade-off makes an especially clear Comparator challenge.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. The standalone artifact uses `import Mathlib` and lists `DkMath/FLT/Five/GoldenOrder.lean` among its ordered source modules.

The target branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The concrete PDF page or section corresponding to this theorem was not identified directly in this pass, so no PDF location is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

Now that 0152 proves the zero-product theorem, the next step is the one-line interface declaration registering that result as the standard `NoZeroDivisors GoldenInt` typeclass instance.
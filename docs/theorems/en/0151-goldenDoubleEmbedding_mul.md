# 0151 — `goldenDoubleEmbedding_mul`

## Lean type

```lean
theorem goldenDoubleEmbedding_mul (x y : GoldenInt) :
    goldenDoubleEmbedding x * goldenDoubleEmbedding y =
      (2 : Zsqrtd 5) * goldenDoubleEmbedding (goldenMul x y) := by
  ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

This is a theorem. It states the exact multiplicative compatibility law for 0148 `goldenDoubleEmbedding`, including the correction factor that appears because the map is not an ordinary ring homomorphism.

## Mathematical statement and meaning

Write

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

with $\varphi=(1+\sqrt5)/2$. If we denote the doubled embedding from 0148 by $E$, then

$$
E(a+b\varphi)=(2a+b)+b\sqrt5.
$$

Thus $E$ represents $2x$ in $\mathbb Z[\sqrt5]$ coordinates. Therefore

$$
E(x)E(y)=(2x)(2y)=4xy,
$$

while

$$
2E(xy)=2(2xy)=4xy.
$$

Hence the theorem expresses

$$
E(x)E(y)=2E(xy).
$$

On the Lean side, the golden-integer product on the right is written explicitly as the raw operation `goldenMul x y`.

The factor $2$ is therefore not an artifact of the proof. It records the fact that `goldenDoubleEmbedding` sends $x$ to the integral-coordinate representative of $2x`, rather than being a genuine multiplicative embedding of $x$ itself.

## Role in the overall proof

This theorem is the central bridge used to transport a zero-product argument from `GoldenInt` to `Zsqrtd 5`.

The immediately following theorem is

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
```

Its proof first rewrites with `goldenDoubleEmbedding_mul` to obtain

$$
E(x)E(y)=0.
$$

It then applies `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero` to deduce

$$
E(x)=0\quad\text{or}\quad E(y)=0,
$$

and finally uses 0150 `goldenDoubleEmbedding_injective` to pull that conclusion back to $x=0$ or $y=0$ in `GoldenInt`.

Thus the 0148–0151 sequence is conceptually

$$
\text{doubled embedding}
\longrightarrow
\text{nonsquare infrastructure}
\longrightarrow
\text{injectivity}
\longrightarrow
\text{multiplicative compatibility},
$$

followed immediately by the construction of `NoZeroDivisors` and then `IsDomain` for `GoldenInt`.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- 0124 `goldenMul`
- 0148 `goldenDoubleEmbedding`
- multiplication on `Zsqrtd 5`
- the extensionality and coordinate simp API for `Zsqrtd`
- the `ring` tactic

0149 `goldenFiveNonsquare` and 0150 `goldenDoubleEmbedding_injective` are not used directly in this theorem's proof. However, 0150 is paired with this theorem immediately afterward in the zero-divisor argument.

## Proof / construction flow

The entire proof is compressed into one line:

```lean
ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

Expanded conceptually, the proof proceeds in three stages.

1. `ext` reduces equality in `Zsqrtd 5` to equality of its two coordinates.
2. `simp [goldenDoubleEmbedding, goldenMul]` unfolds the doubled embedding and golden multiplication and reduces both coordinates to integer polynomial expressions.
3. `ring` normalizes and closes the remaining commutative-ring polynomial identities.

Thus the formal proof follows the pipeline

$$
\text{quadratic-integer equality}
\longrightarrow
\text{coordinate equalities}
\longrightarrow
\text{integer polynomial identities}.
$$

## Lean-specific processing

`ext` uses the extensionality principle for `Zsqrtd 5`, so the proof does not manipulate equality in the quadratic-integer structure directly. Instead, it works coordinatewise.

The `simp` step explicitly unfolds `goldenDoubleEmbedding` and `goldenMul`. Existing simp lemmas for `Zsqrtd` multiplication then expose its real and imaginary coordinates, leaving polynomial identities over `ℤ`.

The final `ring` call is deterministic polynomial normalization, not a search-heavy proof procedure. This theorem is therefore computationally transparent: definitions are unfolded, structures are projected to coordinates, and the resulting algebra is normalized.

The explicit type annotation `(2 : Zsqrtd 5)` fixes the numeral `2` as an element of the target quadratic ring.

## Redundancy and duplication

Both sides of the identity contain `goldenDoubleEmbedding`, and an extra factor `2` remains compared with the familiar ring-homomorphism law

$$
f(xy)=f(x)f(y).
$$

This is not mathematical redundancy. It is forced by the doubled design of 0148.

At the proof-script level, the pattern `ext <;> simp [...] <;> ring` is likely to recur for coordinate identities. A dedicated API for the doubled embedding could potentially reduce this repetition, although the current explicit form is highly auditable.

## Optimization candidates

Four natural implementation strategies can be compared.

1. Keep the current raw doubled embedding and state the factor-corrected multiplicative theorem explicitly.
2. Map into a coefficient ring where division by $2$ is available and construct a genuine `RingHom` representing $x$ itself.
3. Package the doubled embedding as an additive morphism or related structure and retain `E(x)E(y)=2E(xy)` as a dedicated compatibility theorem.
4. Represent `GoldenInt` using `AdjoinRoot` or quadratic-algebra infrastructure and derive the relation through a standard algebraic embedding.

The main advantage of the present design is that the proof remains entirely in integral coordinates and never introduces denominator management. If the immediate goal is only zero-divisor elimination, carrying one explicit factor of $2$ is very efficient.

## Required Mathlib imports and import optimization

The standalone source uses `import Mathlib`. Directly, this theorem needs the definition, multiplication, extensionality, and simp API for `Zsqrtd`, integer-ring simplification, the `ring` tactic, and the upstream `GoldenInt` / `goldenMul` / `goldenDoubleEmbedding` definitions.

A modular source should therefore be able to use imports substantially narrower than all of `Mathlib`. However, the exact minimal combination containing the relevant `Zsqrtd` declarations and `ring` tactic has not been verified in this museum pass because no Lean build is performed. This remains an explicit import-optimization hypothesis.

## Suitability as a Comparator challenge

Yes. Useful implementations to compare include:

- the current doubled embedding with coordinate `ext/simp/ring` proof;
- a genuine `RingHom` into a rational or field-valued quadratic extension;
- an `AdjoinRoot` / quadratic-algebra-based standard embedding.

Comparison metrics can include the number of lemmas needed before zero-divisor elimination, denominator-management overhead, the proportion of proofs closed by `rfl` / `simp` / `ring`, typeclass burden, generalizability, and auditability.

In particular, this makes a clear challenge between increasing abstraction to obtain a genuine homomorphism and retaining a single factor $2$ in exchange for fully explicit integral-coordinate proofs.

## Relation to the PDFs and Lean source

The formal source of truth is the `GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. In source order, this theorem appears immediately after 0150 `goldenDoubleEmbedding_injective` and immediately before `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`.

Japanese and English PDFs are present on the target branch, but the concrete PDF page corresponding to this theorem was not identified directly in this pass. Therefore no PDF page or section number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  ...
```

By 0151, the doubled embedding has both injectivity and the exact multiplicative compatibility law needed downstream. The next theorem combines these facts with zero-product elimination in `Zsqrtd 5` and pulls the result back to `GoldenInt`, establishing the concrete theorem from which the `NoZeroDivisors` instance is built.

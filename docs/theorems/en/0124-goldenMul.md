# 0124 — `goldenMul`

## Lean type

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

`goldenMul` defines multiplication on `GoldenInt` as coordinate multiplication reduced by the basis relation

$$
\varphi^2=\varphi+1.
$$

## Mathematical statement

Let two elements of `GoldenInt` be

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

Expanding the ordinary product gives

$$
xy=ac+(ad+bc)\varphi+bd\varphi^2.
$$

Using the defining golden relation

$$
\varphi^2=\varphi+1,
$$

we obtain

$$
xy=(ac+bd)+(ad+bc+bd)\varphi.
$$

Therefore, in coordinates,

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd),
$$

which is exactly the formula implemented by the Lean definition.

The first coordinate `x.fst * y.fst + x.snd * y.snd` corresponds to $ac+bd$, while the second coordinate `x.fst * y.snd + x.snd * y.fst + x.snd * y.snd` corresponds to $ad+bc+bd$.

## Role in the overall proof

From 0118 `GoldenInt` through 0123 `goldenSub`, the introduced zero, one, addition, negation, and subtraction can essentially be understood as the additive structure of `ℤ × ℤ`. With `goldenMul`, the quadratic relation specific to the golden integer order

$$
\varphi^2=\varphi+1
$$

enters the operations themselves for the first time.

This multiplication is later connected to Lean's standard multiplication by

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

and is also used by the recursion defining `goldenPow`, the construction of `CommRing GoldenInt`, conjugation `goldenConj`, the norm `goldenNorm`, norm multiplicativity, divisibility, units, the Euclidean-domain structure, and ultimately fifth-power extraction.

Thus `goldenMul` is the central primitive operation that turns `GoldenInt` from a mere integer pair into the golden integer ring `ℤ[φ]`.

## Direct dependencies

The direct dependencies are very small:

1. `GoldenInt`
2. integer addition and multiplication
3. the relation $\varphi^2=\varphi+1$ as the mathematical interpretation of the chosen basis

Item 3 is not invoked as a Lean theorem on the right-hand side. Instead, the relation is **compiled into the definition itself** as the already-reduced coordinate formula.

`goldenMul` does not directly depend on `goldenAdd`, `goldenNeg`, or `goldenSub`.

## Definition flow

This declaration is a `def`, so it has no tactic proof. The mathematical derivation is:

1. Read `x = a+bφ` and `y = c+dφ`.
2. Expand the product as $ac+(ad+bc)φ+bdφ^2$.
3. Apply $φ^2=φ+1$.
4. Collect the constant coordinate as $ac+bd$.
5. Collect the $φ$ coordinate as $ad+bc+bd$.
6. Store these two integers in the `fst` and `snd` fields of `GoldenInt`.

Lean does not re-prove this derivation each time. It adopts the final coordinate formula as primitive multiplication.

## Lean-specific processing

### 1. Coordinate operations through structure projections

The implementation uses `x.fst`, `x.snd`, `y.fst`, and `y.snd` directly, so multiplication is completely explicit. No quotient machinery or abstract algebra-extension reduction is involved.

### 2. Constructor inference from the expected type

The right-hand side

```lean
⟨..., ...⟩
```

is inferred as `GoldenInt.mk` from the expected type `GoldenInt`.

### 3. Compiling the defining relation

`φ^2 = φ + 1` is not executed as a theorem rewrite. Since the reduced coordinate formula is already the definition, evaluation of `goldenMul` itself needs no `rw` or `ring`.

By contrast, later proofs of associativity, distributivity, and norm multiplicativity can expand this coordinate definition with `simp [goldenMul]` and then use `ring` for integer polynomial normalization.

### 4. Separation of raw and typeclass APIs

At this stage multiplication is the explicit function `goldenMul x y`. A later `Mul GoldenInt` instance connects it to the standard notation `x * y`. This two-layer design matches the earlier `goldenAdd` API.

## Redundancy and duplication

The coordinate formula

$$
(ac+bd,\ ad+bc+bd)
$$

is expanded repeatedly in later ring-law proofs. In that sense, proofs of the form `simp [goldenMul] <;> ring` may recur.

However, the definition of `goldenMul` itself contains essentially no redundant component. Its two coordinates are the minimal reduced formula forced by `φ^2=φ+1`.

A later theorem

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) : goldenMul x y = x * y := rfl
```

creates both a raw-function API and a typeclass-notation API. This duplication is best viewed as intentional: the raw name preserves definitional traceability while the typeclass notation enables standard algebraic statements.

## Optimization candidates

### Candidate A — Keep the current design

This is the most transparent option. Multiplication in `ℤ[φ]` is immediately readable from coordinates and works well with downstream `ring`-based proofs.

### Candidate B — Inline multiplication directly into the `Mul` instance

One could write

```lean
instance : Mul GoldenInt :=
  ⟨fun x y =>
    ⟨x.fst * y.fst + x.snd * y.snd,
      x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩⟩
```

but this would remove the explicit name `goldenMul`, reducing traceability in theorem statements and debugging.

### Candidate C — Use a generic quadratic-order implementation

For a basis element satisfying $θ^2=pθ+q$, a generic coordinate multiplication is

$$
(a,b)(c,d)=(ac+qbd,\ ad+bc+pbd).
$$

`GoldenInt` could then be specialized with $p=q=1$.

This improves reuse, but introduces abstraction overhead in code dedicated to FLT5. A Comparator challenge can evaluate this trade-off.

### Candidate D — Move to `AdjoinRoot` or another quadratic algebra structure

Using Mathlib's algebraic structures, `φ` could be represented as a root of the polynomial $X^2-X-1$, delegating the defining relation to the ambient structure. However, the current explicit coordinate model has strong local transparency for computation, `ring`, norm formulas, and proof debugging.

## Required Mathlib imports and import optimization

The formal source verified on the target branch is `Flt5DkMath/FLT5StandAlone.lean`, whose standalone construction uses `Mathlib`. The declaration `goldenMul` by itself only needs `GoldenInt`, the integer type `ℤ`, integer `+` and `*`, and ordinary structure construction/projection.

Therefore importing all of `Mathlib` is not necessary merely for this declaration. The larger `GoldenOrder` development later uses `ring`, `norm_num`, `Zsqrtd`, Euclidean-domain structures, and other facilities, so the complete module naturally needs broader imports.

The exact minimal Mathlib module set is not asserted here because no Lean build is performed in this installment.

## Comparator challenge suitability

**Highly suitable.** This declaration is a representative design point for `GoldenInt`.

Possible implementations to compare are:

1. the current explicit coordinate multiplication
2. specialization of a generic quadratic-order multiplication with $θ^2=pθ+q$
3. use of an existing algebraic structure such as `AdjoinRoot (X^2-X-1)`
4. use of `ℤ × ℤ` as the carrier with multiplication defined separately

Evaluation criteria include definitional transparency, strength of `rfl` / `simp`, compatibility with `ring`, import size, ease of proving norm and conjugation results, ease of Euclidean-domain construction, and mathematical reusability.

For the FLT5 proof pipeline specifically, the current explicit formula is a strong design choice.

## Correspondence with existing materials

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`.

The body of the PDFs was not directly analyzed for the `goldenMul` entry in this installment, so no page number, section number, or PDF-specific prose is inferred. The final formal authority for this article is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

It recursively combines 0120 `goldenOne` and this article's 0124 `goldenMul` to define natural powers. Downstream it is connected to the standard power API for `GoldenInt` / `CommRing GoldenInt`, and `goldenPow gamma 5` appears directly in fifth-power extraction.

Therefore 0125 should read `goldenPow` next in dependency order.

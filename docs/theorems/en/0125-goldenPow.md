# 0125 — `goldenPow`

## Lean type

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

`goldenPow` defines natural powers on `GoldenInt` directly by recursion from 0120 `goldenOne` and 0124 `goldenMul`.

## Mathematical statement

Mathematically this is the usual natural-number power law

$$
x^0=1,
$$

$$
x^{n+1}=x^n x.
$$

If `GoldenInt` is read as the coordinate model $a+b\varphi$ with $\varphi^2=\varphi+1$, then `goldenPow x n` is the element obtained by multiplying `x` by itself `n` times using `goldenMul`.

For example, directly from the definition,

$$
\operatorname{goldenPow}(x,0)=\operatorname{goldenOne},
$$

$$
\operatorname{goldenPow}(x,1)=\operatorname{goldenMul}(\operatorname{goldenOne},x).
$$

Once the multiplicative identity laws are proved later, these become the familiar equations $x^0=1$ and $x^1=x$.

The important point is that the `CommRing GoldenInt` instance has not yet been constructed at this declaration. Therefore the definition does not depend on the standard notation `x ^ n`; instead it builds powers first from the raw golden-order API alone.

## Role in the overall proof

`goldenPow` is a bridge between the explicit coordinate API for `GoldenInt` and Mathlib's standard ring API.

Later, in `goldenCommRing : CommRing GoldenInt`, natural powers are registered as

```lean
npow := fun n x => goldenPow x n
```

and the corresponding power axioms are discharged by

```lean
npow_zero := by intro x; rfl
npow_succ := by
  intro n x
  change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
  rfl
```

Thus the recursive equations of this declaration become the ring power laws by definitional equality.

After that,

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

identifies the raw API `goldenPow` with the standard notation `x ^ n` by `rfl`.

Fifth-power extraction is central in the later FLT5 proof, so `goldenPow gamma 5` appears directly in many important interfaces. Examples include preservation of fifth powers by the integer embedding, fifth-power-up-to-unit statements for coprime factors, fifth-power classes of golden units, and the final coordinate formulas `goldenPow_five_fst` / `goldenPow_five_snd`.

Therefore this declaration is a simple recursive function, but it is also the foundational common API for every use of a golden-integer fifth power in the proof.

## Direct dependencies

The direct dependencies are:

1. `GoldenInt`
2. 0120 `goldenOne`
3. 0124 `goldenMul`

It also uses Lean's recursion on natural numbers.

It does not directly depend on 0121 `goldenAdd`, 0122 `goldenNeg`, or 0123 `goldenSub`.

It also does not depend on a `CommRing GoldenInt` instance or on the standard `Pow` API. The dependency goes in the opposite direction: the later `CommRing` instance adopts `goldenPow` as its `npow` implementation.

## Proof / definition flow

This declaration is a `def`, so there is no tactic proof. Its flow is straightforward.

1. Fix the base `x : GoldenInt`.
2. At exponent `0`, return `goldenOne`.
3. At exponent `n + 1`, right-multiply the already computed `goldenPow x n` by `x` using `goldenMul`.
4. The recursive call decreases the exponent from `n + 1` to `n`, so Lean accepts it as structural recursion.
5. These two recursive equations later match `CommRing`'s `npow_zero` and `npow_succ` fields directly.

No separate induction theorem is being proved here; the recursion rules for natural powers are themselves taken as the definition.

## Lean-specific processing

### 1. Curried type

The type is

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
```

so after fixing the base `x`, the result is a function from exponents to `GoldenInt`.

This makes `goldenPow x` itself a value of type `ℕ → GoldenInt` and keeps the recursive definition compact.

### 2. Pattern matching and structural recursion

```lean
| 0 => goldenOne
| n + 1 => goldenMul (goldenPow x n) x
```

is primitive recursion on `ℕ`. Because the recursive call is made on the structurally smaller argument `n`, no explicit termination proof is required.

### 3. Strong definitional equality

The zero and successor equations are not rewrite theorems; they reduce definitionally. This is why the later fields

```lean
npow_zero := by intro x; rfl
```

and `npow_succ` can be closed by `rfl`.

This does more than shorten the proof script: it avoids creating conversion-lemma debt between the custom power API and the standard `CommRing` API.

### 4. Recursion by right multiplication

The recursive step is

```lean
goldenMul (goldenPow x n) x
```

so it uses $x^n x$, not $x x^n$.

This shape directly matches the later `CommRing` `npow_succ` requirement, allowing the proof to reduce to `change ...; rfl`. It also avoids needing a commutativity rewrite before multiplicative commutativity has itself been established.

### 5. Avoiding an early use of standard `^`

If powers were defined here using standard `x ^ n`, the construction could become circular when `CommRing GoldenInt` later needs an `npow` implementation. By closing the definition over only `goldenOne` and `goldenMul`, the raw layer stays independent of the ring instance that it will later help construct.

## Redundancy and duplication

Mathematically, `goldenPow` duplicates the ordinary monoid power recursion already present in Mathlib.

Moreover, the later theorem

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

creates two APIs for the same operation: the raw `goldenPow` and the standard notation `x ^ n`.

This duplication is intentional. Powers are needed **before** the `CommRing GoldenInt` instance exists, and then that exact implementation is installed as `CommRing.npow`. After the instance is built, the two APIs coincide definitionally.

Thus the duplication is best understood as a bootstrap layer that avoids a dependency cycle.

## Optimization candidates

### Candidate A — keep the current implementation

This is the most natural option. The dependencies remain limited to `goldenOne` and `goldenMul`, while later `npow_zero`, `npow_succ`, and `golden_pow_eq` all reduce to `rfl`.

### Candidate B — introduce a generic raw-power helper

A generic primitive-recursion helper taking `one` and `mul` as arguments could be defined, and `goldenPow` could then specialize it.

This would increase reuse, but in this FLT5-specific development the gain is small. It would also add another unfolding layer and could make `simp` / `rfl` behavior less transparent.

### Candidate C — construct typeclass instances first and use standard power recursion

One could expose `One` and `Mul` instances first and delegate to a standard `npowRec`-style implementation.

However, the dependency order around the final `CommRing` construction would need careful handling, and the result could be less transparent than the current explicit bootstrap.

### Candidate D — define only a fifth-power operation

Since FLT5 ultimately needs exponent five, one could define a fixed function such as `goldenFifth x` and expand four multiplications explicitly.

That would make local fifth-power computation explicit, but it would not support general unit powers, arbitrary natural powers in the ring API, or later powers of `goldenPhi`. Across the full proof, the current natural-power API is clearly more reusable.

## Required Mathlib imports and import optimization candidates

The verified standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the full generated artifact.

By itself, `goldenPow` needs only `GoldenInt`, `ℕ`, `goldenOne`, `goldenMul`, and ordinary pattern matching / structural recursion on natural numbers. This declaration itself does not require `ring`, `omega`, `norm_num`, `Zsqrtd`, or similar heavier facilities.

Therefore importing all of `Mathlib` is not necessary merely for this declaration. The complete `GoldenOrder` module needs broader imports because the following development proves ring laws and constructs embeddings, conjugation, and norms.

The exact minimal Mathlib module set has not been build-tested in this museum entry, so no unverified minimal import list is asserted.

## Comparator challenge suitability

 **Suitable.** This is a good challenge for comparing implementations that are mathematically identical but differ in Lean dependency order and definitional equality.

Possible variants are:

1. the current explicit primitive recursion,
2. specialization of a generic raw-power helper,
3. standard power recursion after introducing `One` / `Mul` typeclasses first,
4. an FLT5-specific fixed fifth-power function.

Useful evaluation criteria are dependency cycles, strength of `rfl`, transparency under `simp`, ease of connection to `CommRing.npow`, readability of fifth-power calculations, and reuse in later theorems.

A particularly strong feature of the current implementation is that its right-multiplication recursion already matches the later `CommRing` successor-power law, so the connection can be made by `rfl` before multiplicative commutativity is used.

## Correspondence with existing material

The target branch contains the existing Japanese PDF

`docs/pdf/FLT5-main-ja-v0-r1.pdf`

and English PDF

`docs/pdf/FLT5-main-en-v0-r1.pdf`.

The exact PDF page or section corresponding to `goldenPow` was not directly analyzed in this run, so no page number or PDF-specific wording is guessed.

The final formal authority for this entry is the `GoldenOrder.lean` generated section inside `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all
```

Up through `goldenPow`, the development has been defining the raw carrier and primitive operations. `GoldenInt.ext` is the extensionality theorem that reduces equality of two golden integers to equality of their two coordinates, and it becomes a basic tool for later proofs of ring laws, embeddings, conjugation, and norm identities.
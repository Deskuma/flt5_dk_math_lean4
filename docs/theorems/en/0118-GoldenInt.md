# 0118 — `GoldenInt`

## Lean type

```lean
structure GoldenInt where
  fst : ℤ
  snd : ℤ
deriving DecidableEq
```

`GoldenInt` is a structure with two integer coordinates, `fst` and `snd`. According to the Lean source commentary, it is the carrier used to represent

$$
a+b\varphi,\qquad a,b\in\mathbb Z,
$$

in the basis $1,\varphi$, with multiplication later defined according to

$$
\varphi^2=\varphi+1.
$$

`deriving DecidableEq` gives a computable equality test for two `GoldenInt` values.

## Mathematical statement

This declaration is not itself a theorem. It defines the foundational data type used for the golden integer order. Mathematically, it is the entry point for a direct coordinate implementation of

$$
\mathbb Z[\varphi]
 = \{a+b\varphi\mid a,b\in\mathbb Z\}.
$$

An important qualification is that merely defining `GoldenInt` does not yet establish a ring structure, the relation $\varphi^2=\varphi+1$, or an isomorphism with the ring of integers of $\mathbb Q(\sqrt5)$. The module comment explicitly states that the development does not first construct a field-level isomorphism; instead, it proves the ring, norm, divisibility, and Euclidean-domain structure directly for this coordinate model.

Thus, saying that `GoldenInt` is $\mathbb Z[\varphi]$ refers to the mathematical meaning obtained after the later operations and laws are installed. In isolation, this structure declaration is simply a type of integer pairs.

## Role in the full proof

Up through 0117, the development has reached an interface where Branch B closes once a `SignedSquareGoldenExceptionalCore` is supplied. From `GoldenOrder.lean` onward, the proof begins constructing the golden-integer arithmetic that will eventually provide such a contradiction core.

`GoldenInt` is the bottom-level carrier of that arithmetic. The subsequent declarations define zero, one, addition, negation, multiplication, conjugation, and norm on this type, then proceed toward absence of zero divisors, integral-domain structure, divisibility, and a Euclidean structure.

The module comment also identifies two distinguished elements used later:

$$
\sqrt5\text{-direction}:\quad 2\varphi-1,
$$

$$
\tau=2+\varphi.
$$

These are represented inside the same coordinate ring and are later used to express the ramification identities required by the FLT5 packets.

Therefore 0118 is the entry point into a new algebraic universe: information previously stored in natural-number and integer packets is now prepared for factorization, divisibility, and descent inside the golden integer order.

## Direct dependencies

The declaration itself has very few direct dependencies.

- `ℤ` — the coordinate type.
- Lean `structure` — generates a data type with the projections `fst` and `snd`.
- `DecidableEq` — automatically derived for equality testing.

It has no direct dependency on an earlier FLT5-specific theorem or packet. This is deliberate: `GoldenOrder.lean` builds an algebraic foundation that is largely independent of the earlier reduction layer.

## Construction flow

There is no proof script. The structure declaration conceptually generates:

1. `GoldenInt.mk : ℤ → ℤ → GoldenInt`
2. `GoldenInt.fst : GoldenInt → ℤ`
3. `GoldenInt.snd : GoldenInt → ℤ`
4. a `[DecidableEq GoldenInt]` instance

Thus `⟨a, b⟩ : GoldenInt` can later be used as the coordinate representation of $a+b\varphi$.

Immediately afterward the source defines

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩

def goldenOne : GoldenInt := ⟨1, 0⟩
```

so 0118 is immediately followed by the construction of concrete ring elements on this carrier.

## Lean-specific processing

### Why use a dedicated `structure`?

A plain `ℤ × ℤ` could store the same two coordinates, but a dedicated structure fixes a domain-specific API with the projections `fst` and `snd`, and later permits `Add`, `Mul`, `Neg`, `Zero`, `One`, and other instances to be defined specifically for `GoldenInt`.

The dedicated type also prevents Lean from confusing an arbitrary integer pair with a golden-integer coordinate.

### `deriving DecidableEq`

Since `ℤ` has decidable equality, Lean can automatically derive equality checking for the whole structure. This is convenient for concrete equality checks and for later `simp` processing.

### Extensionality

Equality of structure values ultimately reduces to equality of both coordinates. Later source theorems use `GoldenInt.ext` to split equality goals into `fst` and `snd` components and then close them coordinatewise with `simp` and `ring`.

## Redundancy and duplication

There is almost no proof-level redundancy in this declaration. It is a minimal two-coordinate carrier with equality decidability.

At the design level, one could regard the introduction of a custom pair structure as duplicating more general quadratic-algebra infrastructure. However, the source explicitly chooses not to begin with a field-level isomorphism to the integers of $\mathbb Q(\sqrt5)$. Instead, the arithmetic needed for FLT5 is proved directly in a transparent coordinate model. The apparent duplication is therefore largely intentional.

## Optimization candidates

### 1. Use `ℤ × ℤ` as the carrier

A product type or type synonym could reduce declaration boilerplate. However, the semantic meaning of the projections, instance isolation, and theorem readability would become weaker. For the current proof architecture, the dedicated structure is likely preferable.

### 2. Connect to a general quadratic algebra

A future extension could prove an isomorphism to a Mathlib representation based on `AdjoinRoot`, `QuadraticAlgebra`, or related general infrastructure. That would let the coordinate theorems interoperate with a broader mathematical API.

This would be better treated as an interoperability layer rather than as a replacement of the present carrier. Keeping the explicit coordinate model while proving an external isomorphism preserves the locality and auditability of the FLT5 proof.

### 3. Named coordinate semantics

`fst` and `snd` are generic names. Auxiliary accessors with names corresponding to the coefficients of $1$ and $\varphi$ could make some later statements more semantic. On the other hand, if the existing proof already uses `x.fst` and `x.snd` extensively, the migration cost may exceed the readability gain.

## Required Mathlib imports and import optimization

The standalone source begins with

```lean
import Mathlib
```

for the complete generated artifact.

For the `GoldenInt` declaration alone, only integers, structures, and derivation of `DecidableEq` are directly needed, so importing all of Mathlib is clearly broader than necessary. It is likely possible to reduce the declaration-level dependency to Lean/Init plus the minimal integer support.

The whole `GoldenOrder.lean` module needs more: later declarations build ring structure, use a map into `Zsqrtd 5`, and prove identities using tools such as `ring` and `simp`. Therefore the module-level minimal import set will be larger than the minimum needed by 0118 alone.

No Lean build is run in this museum pass, so the exact minimal import set is not verified. This point is explicitly an optimization hypothesis.

## Comparator challenge suitability

Yes. The choice of representation for golden integers is a useful implementation-comparison problem.

Possible variants include:

1. the current dedicated `structure GoldenInt := (fst snd : ℤ)`;
2. a lightweight carrier based on `ℤ × ℤ`;
3. a representation using Mathlib's general quadratic/adjoin-root infrastructure.

Useful comparison axes are declaration size, ease of `simp`, compatibility with `ring`, expression of norm and conjugation, difficulty of proving Euclidean-domain structure, length of downstream FLT5 theorems, and interoperability with general mathematics.

The most useful challenge is not merely to minimize lines of code, but to compare which carrier makes the later FLT5 proof most transparent.

## Sources and scope of inference

The formal source is the `DkMath/FLT/Five/GoldenOrder.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its module commentary explicitly describes `GoldenInt` as the direct coordinate model for $a+b\varphi$, with later multiplication, conjugation, and norm based on $\varphi^2=\varphi+1$.

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. Their specific `GoldenInt` pages were not directly inspected in this pass, so no page number, section number, or wording from the PDFs is inferred.

The import-minimization proposal and the possible connection to a general quadratic algebra are design candidates, not claims about the current implementation.

## Next declaration to read

The next declaration in dependency order is

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

It provides the first concrete ring element, $0$, on the `GoldenInt` carrier. Together with the following `goldenOne`, it begins the construction of the golden-order arithmetic API. Therefore `goldenZero` is the natural subject for the next article.

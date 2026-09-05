# 0316 — `GoldenZeroSectorCandidate.A0`

## Declaration kind

This declaration is a **`def`**.

By 0314 `GoldenZeroSectorCandidate.A_pos` and 0315 `GoldenZeroSectorCandidate.A_lt_B`, the lower inversion factor

$$
A=U-W
$$

has already been established over the integers to satisfy

$$
0<A<B.
$$

This definition is the boundary object that extracts the positive integer factor $A$ as a natural-number representative for the arithmetic developed downstream:

$$
A_0=|A|\in\mathbb N.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Natural representative of the positive lower factor. -/
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

Its type is

```lean
GoldenZeroSectorCandidate → ℕ
```

For a candidate `p`, it forms the integer factor

```lean
zeroSectorA p.r p.s p.d : ℤ
```

from the stored coordinates `r : ℤ`, `s : ℤ`, and `d : ℕ`, then returns its `Int.natAbs`.

## Mathematical meaning

`zeroSectorA` is defined by

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

so mathematically

$$
A=U-W.
$$

The present definition implements

$$
A_0:=|A|
$$

as a value of type `ℕ`.

The important point is that $A>0$ has already been proved immediately before this definition. Consequently the following theorem `A0_cast` reconstructs the original signed factor exactly:

$$
(A_0:\mathbb Z)=A.
$$

Viewed in isolation, `natAbs` forgets the sign of the integer input. In the actual proof architecture, however, the sign information is preserved separately by `A_pos` and is recombined with `A0` through `A0_cast`.

## Role in the full proof

The zero-sector inversion developed through 0309–0315 is primarily carried out over `ℤ`. It produces signed factor data such as

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

and

$$
0<A<B.
$$

The downstream exact factor splitting, coprimality arguments, two-adic branch analysis, and fifth-power ownership are largely stated over `ℕ`. The signed integer factors therefore need to be transported to natural representatives.

`A0` is the first such boundary definition. It is immediately followed by the symmetric `B0`, and then by

```lean
theorem A0_cast ...
theorem B0_cast ...
theorem A0_pos ...
theorem B0_pos ...
theorem A0_mul_B0 ...
theorem B0_eq_A0_add ...
```

Thus `A0` is the **bridge object that moves the integer inversion factorization into natural-number factor arithmetic**.

## Direct dependencies

### `zeroSectorA`

This is the project definition directly called by `A0`:

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

`A0` applies `natAbs` to this integer value.

### `Int.natAbs`

This is the Lean/Mathlib absolute-value map from integers to naturals:

$$
\operatorname{natAbs}:\mathbb Z\to\mathbb N.
$$

Because it is total on all integers, the definition of `A0` itself does not need a proof argument establishing `A_pos`.

### `GoldenZeroSectorCandidate.A_pos`

This theorem is not used in the body of the `def`, but it is a direct semantic dependency of the interpretation of `A0` and is essential in the next theorem:

```lean
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

It guarantees that the natural representative obtained by `natAbs` is exactly the original positive integer factor when cast back to `ℤ`.

## Construction flow

1. Read `r`, `s`, and `d` from the candidate `p`.
2. Evaluate `zeroSectorA p.r p.s p.d : ℤ` to obtain the lower inversion factor $A$.
3. Apply `Int.natAbs` to obtain the natural number $A_0$.
4. The definition itself ends here.
5. The following theorem `A0_cast` uses `A_pos` to prove $(A_0:ℤ)=A$.
6. `A0_pos`, `A0_mul_B0`, and the later factor packets then continue entirely in natural-number arithmetic where appropriate.

## Lean-specific aspects

### A total definition rather than a proof-dependent value

Since $A>0$ is already known, one could imagine a subtype-style representation carrying a positivity proof. The present implementation instead uses

```lean
Int.natAbs
```

so that `A0` remains a simple total function returning ordinary arithmetic data. Correctness of the representation is separated into the theorem `A0_cast`.

This keeps the data definition proof-irrelevant and makes later use of ordinary `Nat` APIs straightforward.

### Explicit `ℤ` / `ℕ` boundary

The signed FLT5 algebraic identities are convenient over `ℤ`, while later factorization, `Nat.Coprime`, parity, divisibility, and fifth-power splitting are naturally expressed over `ℕ`. This definition makes that type boundary explicit.

### Dot notation

Downstream code writes

```lean
p.A0
```

because the definition is declared in the namespace with the candidate as its first argument. This gives a natural object-style API.

## Redundancy and overlap

The implementation is one line and has essentially no syntactic redundancy.

Conceptually, because `A_pos : 0 < A` is already known, the design first applies the general sign-forgetting operation `natAbs` and then uses positivity in `A0_cast` to recover the original integer. This may look indirect, but in Lean it is a practical separation of data from correctness.

An alternative based on `Int.toNat` is conceivable, but its behavior on negative inputs and the available cast lemmas differ. The meaning of `natAbs` is especially transparent for a signed-to-natural representative.

## Optimization candidates

There is little to optimize in the definition itself.

Because `A0` and the following `B0` are perfectly symmetric, one could introduce a helper such as

```lean
def positiveIntRepresentative (z : ℤ) : ℕ := z.natAbs
```

and define both through it. This would merely rename `natAbs`, however, while adding another API layer, so the benefit is small.

Another possible design is to return a subtype or a positive-natural structure that stores positivity together with the value. That could eliminate a separate `A0_pos` theorem, but it would complicate later interaction with standard `Nat.Coprime`, powers, divisibility, and factorization APIs.

Accordingly, the present design

```lean
ℤ --natAbs--> ℕ
```

with positivity and cast correctness kept as separate theorems is reasonable both for simplicity and for interoperability with Mathlib.

These alternatives are **unverified design candidates** in this run because no Lean build is performed.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The Mathlib-side functionality directly required by this definition is very small, principally

- `Int.natAbs`
- the basic `ℤ` and `ℕ` types.

`zeroSectorA` itself is a project definition, and the minimal module-level import set must also account for its upstream definitions. Therefore the exact smallest import list cannot be inferred from this `def` alone.

It is highly plausible that `import Mathlib` could be narrowed substantially for this individual declaration, but the exact minimal import set is **not confirmed**, since Lean build checks are excluded from this task.

## Comparator challenge suitability

**Suitable, though more as an API/representation-design comparison than as a theorem-proving challenge. Difficulty: introductory.**

Useful comparison axes include:

- the current `Int.natAbs` design;
- an `Int.toNat` design;
- a subtype carrying a positivity proof;
- defining raw data in `A0` and separating correctness into `A0_cast`;
- keeping all signed arithmetic in `ℤ` and delaying or avoiding the move to `ℕ`.

The declaration is especially useful for comparing the Lean design principle of keeping a definition total while moving semantic justification into a theorem.

## PDF cross-check

The target branch contains the existing Japanese and English PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

Their presence was confirmed in the repository. However, the ordinary GitHub connector text fetch does not return binary PDF contents, so this run could not directly verify the exact page, section, or equation location. No such location is guessed here.

The Lean code, declaration order, direct dependencies, and relationship to following declarations were checked against the current branch's `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0317 `GoldenZeroSectorCandidate.B0`, also a **`def`**:

```lean
/-- Natural representative of the positive upper factor. -/
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

Where 0316 transports the lower factor $A$ to $A_0$, 0317 transports the upper factor $B$ to

$$
B_0=|B|\in\mathbb N.
$$

Once both natural representatives are available, 0318 `A0_cast` begins reconstructing the exact natural factor identities.
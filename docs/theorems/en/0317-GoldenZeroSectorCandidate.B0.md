# 0317 — `GoldenZeroSectorCandidate.B0`

## Declaration kind

This declaration is a **`def`**.

Where 0316 `GoldenZeroSectorCandidate.A0` introduced the natural-number representative of the lower inversion factor $A$, the present definition introduces the corresponding natural representative of the upper inversion factor $B$.

By this point the integer inequalities

$$
0<A<B
$$

have already been established, so in particular $B>0$. The definition transports this positive integer factor to natural-number arithmetic as

$$
B_0=|B|\in\mathbb N.
$$

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Natural representative of the positive upper factor. -/
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

Its type is

```lean
GoldenZeroSectorCandidate → ℕ
```

For a candidate `p`, the stored data

```lean
p.r : ℤ
p.s : ℤ
p.d : ℕ
```

are used to form

```lean
zeroSectorB p.r p.s p.d : ℤ
```

and `Int.natAbs` is then applied.

## Mathematical meaning

The upstream definition of `zeroSectorB` is

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

so mathematically

$$
B=U+W.
$$

The present declaration implements the natural representative

$$
B_0:=|B|.
$$

The proof has already established `B_pos`, hence

$$
B>0.
$$

Therefore the downstream theorem `B0_cast` recovers the original integer factor exactly:

$$
(B_0:\mathbb Z)=B.
$$

Thus `B0` should not be viewed as weakening the information by discarding the sign. Rather, the sign information is retained separately by `B_pos`, while this definition changes only the arithmetic carrier from `ℤ` to `ℕ`.

## Role in the full proof

The signed phase of the zero-sector inversion has already produced, over `ℤ`, data such as

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
$$

and

$$
0<A<B.
$$

Definitions 0316 `A0` and 0317 `B0` form a matched pair of bridge objects transporting those two positive integer factors into `ℕ`.

Afterward, `A0_cast` and `B0_cast` prove

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B.
$$

Positivity, product, difference, and order identities can then be reconstructed on the natural-number side. This makes the factors available to Mathlib's `Nat` infrastructure for coprimality, two-adic splitting, exact factorization, divisibility, and fifth-power ownership.

Accordingly, `B0` does not itself impose a new mathematical constraint, but it is an **essential type-boundary object connecting signed inversion data with natural-number factorization machinery**.

## Direct dependencies

### `zeroSectorB`

This is the project definition called directly by `B0`:

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

Hence the raw value represented by `B0` is $|U+W|$.

### `Int.natAbs`

This is the Lean/Mathlib absolute-value map from integers to naturals:

$$
\operatorname{natAbs}:\mathbb Z\to\mathbb N.
$$

Because it is total on all integers, the definition itself does not need a positivity proof as an argument.

### `GoldenZeroSectorCandidate.B_pos`

This theorem does not occur syntactically in the body of `B0`, but it is a semantic dependency of the intended interpretation of the definition and is required downstream by `B0_cast`.

It has already established

```lean
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

which guarantees that `natAbs` represents the original positive factor rather than merely its unsigned magnitude.

### `GoldenZeroSectorCandidate.A0`

`B0` does not call `A0`, so this is not a direct definitional dependency. Architecturally, however, the two declarations are a perfectly symmetric pair:

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

Together they transport the signed pair $(A,B)$ to the natural pair $(A_0,B_0)$.

## Construction flow

1. Read `r`, `s`, and `d` from the candidate `p`.
2. Evaluate `zeroSectorB p.r p.s p.d : ℤ` to obtain the upper inversion factor $B$.
3. Apply `Int.natAbs` to define $B_0\in\mathbb N$.
4. The `def` itself ends here and requires no proof argument.
5. The later theorem `B0_cast` uses the already-proved `B_pos` to recover $(B_0:ℤ)=B$.
6. Once both `A0` and `B0` are identified with their integer counterparts, the signed product, difference, and order identities can be transported to natural-number arithmetic.

## Lean-specific aspects

### Total carrier conversion via `natAbs`

Because $B>0$ is already known, a subtype carrying a positivity proof would be possible. The current implementation instead uses `Int.natAbs`, yielding the very simple total function

```lean
GoldenZeroSectorCandidate → ℕ
```

This separates raw data from correctness and makes ordinary `Nat` APIs directly available downstream.

### Correctness is separated into a following theorem

`B_pos` does not occur in the body of `B0`. This is not an omission of sign information; rather, the design separates

- data construction: `B0`;
- semantic recovery: `B0_cast`.

This keeps the definition compact and avoids embedding proof terms into the arithmetic value.

### Explicit `ℤ` / `ℕ` boundary

`zeroSectorB` belongs to the signed inversion framework, where `ℤ` is natural because the surrounding algebra includes signed differences. Downstream gcd, coprimality, divisibility, and power decomposition are more naturally expressed through Mathlib's `Nat` APIs.

`B0` marks this type boundary explicitly.

### Dot notation

Since the definition is in the `GoldenZeroSectorCandidate` namespace with the candidate as its first argument, later code can write

```lean
p.B0
```

using object-style dot notation.

## Redundancy and overlap

The implementation is a single line and contains essentially no local redundancy.

Structurally, however, `A0` and `B0` are perfectly symmetric. Both merely apply

```lean
(z : ℤ).natAbs
```

to one of the two inversion factors.

That duplication is useful rather than accidental: it preserves the mathematical distinction between the lower and upper factors in the API. Introducing one generic helper would save almost no code and could make the downstream naming pattern `A0_cast`, `B0_cast`, `A0_pos`, `B0_pos`, and later factor identities less transparent.

Thus the paired definitions are best understood as **intentional API-level duplication reflecting the two-factor mathematical structure**.

## Optimization candidates

There is little to optimize in the definition itself.

One possible abstraction would be a shared helper

```lean
def naturalRepresentative (z : ℤ) : ℕ := z.natAbs
```

used by both `A0` and `B0`. This would only rename `Int.natAbs`, however, while introducing another API layer, so the benefit is small.

Another alternative would be a positive-natural subtype carrying positivity in the data. That could absorb a theorem such as `B0_pos`, but it would likely increase coercion and projection overhead whenever the later proof uses standard `Nat.Coprime`, powers, or divisibility lemmas.

An `Int.toNat` design is also conceivable, but its behavior on negative integers differs from `natAbs`. Since positivity is stored separately by theorem in the present architecture, such a design may be workable, yet its cast-lemma and simplification behavior has not been tested here.

The current `natAbs` bridge is therefore a reasonable minimal design. All alternatives above are **unverified design candidates**, since this task does not run Lean builds.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The Mathlib-side functionality directly required by this definition is small, primarily

- `Int.natAbs`;
- the basic `ℤ` and `ℕ` types and coercion infrastructure.

`zeroSectorB`, `GoldenZeroSectorCandidate`, and its fields are project declarations, so the exact smallest import set for the containing module also depends on their upstream definitions.

It is highly plausible that the broad `import Mathlib` could be narrowed for this local declaration, but the exact minimal import set is **not confirmed**, because Lean build checks are explicitly excluded from this task.

## Comparator challenge suitability

**Suitable, primarily as a representation/API-design comparison rather than a theorem-proving challenge. Difficulty: introductory.**

Useful comparison axes include:

- the current `Int.natAbs` design;
- an `Int.toNat` design;
- returning a subtype that carries positivity;
- keeping the signed factor in `ℤ` and delaying conversion to `ℕ`;
- keeping separate named APIs `A0` and `B0` versus routing both through a generic helper.

The declaration is especially useful for illustrating the Lean design principle of separating a total data definition from the theorem that certifies its intended semantic interpretation.

## PDF cross-check

The target branch contains the existing Japanese and English PDFs

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`;
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

Their presence was confirmed in the repository. However, the ordinary GitHub connector text fetch does not return binary PDF contents, so this run could not directly verify the exact page, section, or equation location. No such location is guessed here.

The Lean code, declaration order, direct dependencies, symmetry with `A0`, and connection to the following `A0_cast` theorem were checked against the latest branch version of `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is 0318 `GoldenZeroSectorCandidate.A0_cast`, a **`theorem`**:

```lean
/-- Cast equation for the positive lower natural representative. -/
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

Now that both natural representatives $A_0$ and $B_0$ have been introduced in 0316–0317, the proof proceeds to cast bridges that identify them exactly with the signed factors.

0318 first recovers the lower factor identity

$$
(A_0:\mathbb Z)=A,
$$

and the corresponding later `B0_cast` then completes the pair, preparing the natural-number reconstruction of the exact factor identities.
# 0286 — `zeroSectorB`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It defines the upper inversion factor `B` used in the zero-sector inversion layer. The preceding declaration 0285 `zeroSectorA` introduced

$$
A=U-W,
$$

whereas this declaration introduces

$$
B=U+W.
$$

Together they complete the symmetric inversion factor pair

$$
A=U-W,
\qquad
B=U+W.
$$

## Lean type

```lean
/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

Its full Lean type is

```lean
zeroSectorB : ℤ → ℤ → ℕ → ℤ
```

The coordinates `r,s` are integers, `d` is a natural number, and the result is an integer. The cast from `d : ℕ` to `ℤ` is not written directly in this definition; it is encapsulated inside the directly used definition 0284 `zeroSectorW`.

## Mathematical meaning

Using the preceding definitions

$$
X=2r+s,
$$

$$
U=X^2+5s^2,
$$

$$
W=4d^5,
$$

we obtain

$$
B=U+W,
$$

hence

$$
B=(2r+s)^2+5s^2+4d^5.
$$

Together with 0285 `zeroSectorA`, this gives

$$
A=U-W,
\qquad
B=U+W.
$$

Thus `A` and `B` are symmetrically placed around the center `U`, with deviation `W`.

The main advantage of this form is that the standard difference-of-squares and sum-difference identities become available immediately:

$$
AB=(U-W)(U+W)=U^2-W^2,
$$

$$
B-A=2W=8d^5,
$$

$$
A+B=2U.
$$

Therefore `B` is not merely a notational abbreviation. It is the upper factor in the symmetric coordinate system that converts the zero-sector quadratic quantity `U` and the fifth-power deviation `W` into a factorization-friendly form.

## Role in the full proof

`zeroSectorB` completes the inversion factor pair begun by 0285 `zeroSectorA`.

In the Lean source, the subsequent theorem `factor_product_twenty` uses these two factors to prove

$$
AB=20s^4.
$$

Its first algebraic step unfolds the definitions and reduces the product to

$$
AB=U^2-W^2,
$$

then uses the diagonal identity available from the zero-sector candidate to normalize the right-hand side to $20s^4$.

The following theorem `factor_product` combines this with the tenth-power split inherited from 0281 and rewrites the product as

$$
AB=4Q^5,
$$

where `Q=5^5c^8` is introduced next.

The source also proves positivity of `B`, and later passes to a natural-number factor via a definition of the form

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

This natural-number upper factor is then used as structural data in the later fifth-power factorization / inversion packet.

Thus 0286 is the point that **completes the symmetric factor pair and makes its exact product, difference, and sum relations available to the inversion argument**.

## Direct dependencies

### 0283 `zeroSectorU`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

This supplies the central quantity

$$
U=X^2+5s^2.
$$

### 0284 `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

This supplies the deviation added in the definition:

$$
W=4d^5.
$$

### 0282 `zeroSectorX`

This declaration is not referenced directly in the body of `zeroSectorB`; it is a **transitive dependency** through `zeroSectorU`.

### 0285 `zeroSectorA`

`zeroSectorA` is not a direct Lean dependency of the definition body. However, mathematically `A` and `B` form a symmetric pair, so 0285 is tightly coupled to the role of this declaration in the proof.

### Theorem dependencies

Because this is a `def`, it directly uses no theorem. The mathematical source of `d` lies in 0281 `zeroSector_tenthPower_split`, but that information is not encoded in the type or body of `zeroSectorB` itself.

## Construction flow

### 1. Accept `r,s,d`

```lean
(r s : ℤ) (d : ℕ)
```

The definition receives the integer coordinates `r,s` of the zero-sector data and the natural number `d` coming from the tenth-power-root side.

### 2. Compute the central quantity `U`

```lean
zeroSectorU r s
```

This is

$$
(2r+s)^2+5s^2.
$$

### 3. Compute the deviation `W`

```lean
zeroSectorW d
```

This is, as an integer,

$$
4d^5.
$$

### 4. Add them in `ℤ`

```lean
zeroSectorU r s + zeroSectorW d
```

defines

$$
B=U+W.
$$

The source later proves positivity of `B` under the hypotheses of a zero-sector candidate, but positivity is not part of this definition itself.

## Lean-specific handling

There is no tactic proof in this declaration; the right-hand side is the definitional equation itself. Consequently,

```lean
example (r s : ℤ) (d : ℕ) :
    zeroSectorB r s d = zeroSectorU r s + zeroSectorW d := by
  rfl
```

is provable by `rfl`.

To expand all the way to

$$
B=(2r+s)^2+5s^2+4d^5,
$$

one must explicitly unfold several definitions, for example

```lean
unfold zeroSectorB zeroSectorU zeroSectorX zeroSectorW
```

or

```lean
simp only [zeroSectorB, zeroSectorU, zeroSectorX, zeroSectorW]
```

In `factor_product_twenty`, the source unfolds `zeroSectorA` and `zeroSectorB`, then lets `ring` normalize

$$
(U-W)(U+W)=U^2-W^2.
$$

This separates two useful layers: named definitions preserve the mathematical structure, while local unfolding exposes polynomial identities to automation only where needed.

## Redundancy and duplication

The body is a single line and contains no local redundancy.

In principle, later theorems could inline

```lean
zeroSectorU r s + zeroSectorW d
```

and eliminate the name `zeroSectorB`. However, the source uses `B` repeatedly in declarations including

- `factor_product_twenty`,
- `factor_product`,
- factor difference / factor sum relations,
- `B_pos`,
- `A_lt_B`,
- `B0`,
- `B0_cast`.

Moreover, the symmetry

$$
A=U-W,
\qquad
B=U+W
$$

is itself part of the proof architecture. Keeping two parallel named definitions therefore improves readability over inlining them.

## Optimization candidates

### Prefer the symmetric factor-pair API

Downstream code should prefer the named product, difference, and sum theorems over repeatedly unfolding `zeroSectorA` and `zeroSectorB`.

In particular, relations such as

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

form a cleaner API for later stages of the proof.

### Be conservative with `@[simp]`

Since `zeroSectorB` already unfolds definitionally, there is little need for a dedicated `[simp]` theorem.

Aggressive automatic unfolding could erase the useful abstraction `B` too early and produce large expressions, obscuring the symmetric factor-pair structure. The current pattern of explicit `unfold` / `simp only` at selected points is therefore reasonable.

### Possible factor-pair structure

One could package `U,W,A,B` into a structure to reduce repeated arguments. However, the later source already introduces structures such as `GoldenZeroSectorCandidate` and inversion packets. The benefit of adding another structure at this early stage has not been verified.

This is therefore only a possible design direction, not a demonstrated improvement.

## Required Mathlib imports and import optimization

The repository's standalone source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

at the top level.

`zeroSectorB` itself only adds two already defined integer-valued quantities, `zeroSectorU` and `zeroSectorW`. The definition does not intrinsically require the whole Mathlib umbrella.

However, this run deliberately does not perform a Lean build, and the generated source has not been recompiled as an isolated module with minimized imports. Therefore the exact minimal import set is **unverified**.

A proper import optimization pass would need to analyze the complete dependency graph of `SignedGoldenZeroSectorInversion`, replace the umbrella import with narrower integer, natural-number, and algebra-normalization imports, and verify the result with Lean. That verification is outside this run.

## Comparator challenge suitability

### Verdict: low suitability in isolation, high suitability when paired with 0285

The isolated definitional equation

```lean
zeroSectorB r s d = zeroSectorU r s + zeroSectorW d
```

is solved by `rfl`, so it provides almost no meaningful Comparator challenge.

In contrast, pairing it with 0285 `zeroSectorA` and asking for

$$
AB=U^2-W^2,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

creates a useful challenge involving the choice between `unfold`, `simp only`, and `ring`, as well as the question of how long to preserve the named abstractions.

The first algebraic step of `factor_product_twenty` is especially suitable: it is short, local, and directly compares proof-normalization strategies.

## PDF cross-check

The target branch contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

For the Japanese PDF, repository existence and the file blob SHA were confirmed. Accessing the English PDF through the GitHub connector's UTF-8 path produced a binary decoding error, so its body could not be inspected in text form.

Therefore the exact PDF page, section, and wording corresponding to `B=U+W` are **unverified**, and no page-level claim is inferred.

The technical content of this note is grounded in the Lean source `Flt5DkMath/FLT5StandAlone.lean` and the theorem-museum material currently present in the repository.

## Next declaration to read

The next declaration is **0287 `zeroSectorQ`**, also a `def`.

```lean
/-- The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`. -/
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

It introduces the fifth-power mass

$$
Q=5^5c^8
$$

so that the completed inversion factor pair can be summarized by

$$
AB=4Q^5.
$$

Thus 0285–0286 finish the `A,B` side, while 0287 begins naming the fifth-power mass on the product side.

# 0284 — `zeroSectorW`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It introduces the fifth-power scale `W` used in the zero-sector inversion. The preceding declaration 0283 `zeroSectorU` introduces the quadratic quantity on the `r,s` side,

$$
U=X^2+5s^2,
$$

whereas this declaration takes the natural number `d` supplied by 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split`, namely

$$
|H(r,s)|=d^{10},
$$

and forms the integer

$$
W=4d^5.
$$

## Lean type

```lean
/-- The quantity `W = 4*d^5` supplied by `|H(r,s)| = d^10`. -/
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

Thus its full Lean type is

```lean
zeroSectorW : ℕ → ℤ
```

The input is `d : ℕ`, while the output is an integer. The body explicitly casts `d` to `ℤ` as `(d : ℤ)`.

## Mathematical meaning

The definition is simply

$$
W=4d^5.
$$

Although `d` is accepted as an arbitrary natural number by the definition itself, in the zero-sector inversion it is supplied by the tenth-power split of 0281,

$$
|H(r,s)|=d^{10}.
$$

Since

$$
d^{10}=(d^5)^2,
$$

the construction extracts the fifth-power half `d^5` and multiplies it by the normalization factor `4`:

$$
W=4d^5.
$$

The coefficient `4` is chosen for the symmetric inversion factors

$$
A=U-W,
\qquad
B=U+W.
$$

The generated-source chapter comment states that this coordinate system is designed to produce

$$
AB=4Q^5
$$

and

$$
B=A+8d^5.
$$

The latter is immediately consistent with this definition because

$$
B-A=2W=8d^5.
$$

## Role in the full proof

Up through 0281, the arithmetic layer establishes the exact tenth-power split

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

Declarations 0282–0284 then convert this data into inversion coordinates:

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5.
$$

Here `U` is the central quantity built from `r,s`, while `W` is the deviation built from the tenth-power factor `d`. The next declarations 0285 `zeroSectorA` and 0286 `zeroSectorB` define

$$
A=U-W,
\qquad
B=U+W.
$$

Thus `W` measures the symmetric displacement from the common center `U` to the factor pair `(A,B)`.

In this sense, 0284 is the **bridge that transfers tenth-power information from the arithmetic layer into the linear difference coordinate used by the inversion layer**.

## Direct dependencies

### Cast from naturals to integers

The only explicit type conversion in the definition is

```lean
(d : ℤ)
```

### Integer fifth power

The definition uses

```lean
(d : ℤ) ^ 5
```

with natural exponent `5`.

### Integer constant `4` and multiplication

The final expression is

```lean
4 * (d : ℤ) ^ 5
```

### Relation to 0281

The code does not directly mention the name of theorem 0281. However, the source docstring explicitly says

```text
supplied by `|H(r,s)| = d^10`
```

so the intended provenance of `d` is the tenth-power split produced there.

### Relation to 0283

The body of `zeroSectorW` does not depend on 0283 `zeroSectorU`. They are parallel base definitions and are first combined in `zeroSectorA` and `zeroSectorB`.

## Construction flow

### 1. Receive `d : ℕ`

```lean
(d : ℕ)
```

The tenth-power root obtained in zero-sector arithmetic remains a natural number.

### 2. Cast `d` to `ℤ`

```lean
(d : ℤ)
```

The later quantities `U`, `A`, and `B` are integer-valued, so the type is aligned here.

### 3. Take the fifth power

```lean
(d : ℤ) ^ 5
```

This is the half-exponent corresponding to the square decomposition of `d^10`.

### 4. Multiply by `4`

```lean
4 * (d : ℤ) ^ 5
```

The result is named `W`.

### 5. Feed it to the symmetric factors

The repository source continues immediately with

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

## Lean-specific behavior

There is no proof term: the right-hand side is the definition itself.

Therefore

```lean
example (d : ℕ) :
    zeroSectorW d = 4 * (d : ℤ) ^ 5 := by
  rfl
```

holds by definitional equality alone.

Because Lean inserts the coercion from `ℕ` to `ℤ` inside the definition, the result can be added to or subtracted from `zeroSectorU r s : ℤ` without any further type conversion.

By contrast, if one later wants to compare the result directly with a natural-number expression such as

```lean
4 * d ^ 5
```

then cast lemmas or tactics such as `norm_cast` / `exact_mod_cast` may be needed. No such processing occurs in this declaration itself.

## Redundancy and duplication

The definition is one line and contains no computational redundancy.

In principle one could inline

```lean
4 * (d : ℤ) ^ 5
```

directly into `zeroSectorA` and `zeroSectorB`. That would, however, obscure the symmetric structure

$$
A=U-W,
\qquad
B=U+W,
$$

and would make the later relation

$$
B-A=2W=8d^5
$$

less explicit.

Thus the independent definition of `zeroSectorW` is valuable not primarily as abbreviation, but as a **named deviation quantity in the inversion geometry**.

## Optimization candidates

### Nonnegativity lemma

Since `d : ℕ`, one always has

$$
W=4d^5\ge0.
$$

If later proofs repeatedly establish this fact, a lemma such as

```lean
theorem zeroSectorW_nonneg (d : ℕ) : 0 ≤ zeroSectorW d := by
  simp [zeroSectorW]
  positivity
```

could be useful.

Whether the fact is repeated often enough to justify a dedicated API lemma has not been comprehensively audited here.

### Positivity lemma

Under `0 < d`, one could similarly expose

```lean
theorem zeroSectorW_pos {d : ℕ} (hd : 0 < d) : 0 < zeroSectorW d := ...
```

This may be useful because later candidate data contains positivity provenance for the arithmetic quantities.

### Normalization lemma for `2 * W`

If the difference between `A` and `B` is used repeatedly, one could introduce

```lean
theorem two_mul_zeroSectorW (d : ℕ) :
    2 * zeroSectorW d = 8 * (d : ℤ) ^ 5 := by
  simp [zeroSectorW]
  ring
```

This is easy to regenerate with `ring`, so whether it deserves a permanent API lemma remains unverified.

## Required Mathlib imports and import optimization

The repository's standalone canonical file `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. The generated-source boundary identifies this declaration as belonging to

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The definition by itself needs only `ℕ`, `ℤ`, the natural-to-integer cast, integer multiplication, and natural-exponent powers, so it is unlikely that all of Mathlib is intrinsically required for this single declaration.

However, the individually generated source module is not available in the repository layout through the path checked in this run, and the task explicitly excludes a Lean build. Therefore a minimal import set has not been experimentally verified.

The only confirmed statement is that the standalone canonical source uses **`import Mathlib`**. A more specific minimal-import recommendation would be speculative.

## Comparator challenge suitability

### Verdict: low suitability for the definition alone

The statement

```lean
zeroSectorW d = 4 * (d : ℤ) ^ 5
```

is closed by `rfl`, so the definition itself offers little proof-strategy variety.

Derived tasks are more suitable, for example proving

$$
W\ge0,
$$

$$
0<d\Longrightarrow W>0,
$$

or, after introducing `A,B`,

$$
B-A=8d^5.
$$

Those versions can compare `simp`, `ring`, `positivity`, and coercion handling.

Thus **the definition itself is not a strong Comparator challenge, but a derived `A,B` difference identity would be**.

## Cross-check against the PDFs

The target branch repository tree contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

However, the available retrieval path in this run could not obtain the binary PDF contents in an analyzable form, and direct raw-PDF retrieval also failed. Therefore the exact page, section, and wording where `W=4d^5` appears in the PDFs could not be verified.

No PDF-specific detail is guessed here. The technical interpretation above is grounded in the canonical Lean generated source and the verifiable theorem-museum context in the repository.

## Declaration to read next

The next declaration is **0285 `zeroSectorA`**, also a `def`:

```lean
/-- The lower inversion factor `A = U-W`. -/
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

That is,

$$
A=U-W.
$$

It is the first declaration that combines the central quantity `U` from 0283 with the deviation `W` introduced here into a single inversion factor.
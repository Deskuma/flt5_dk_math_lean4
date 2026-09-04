# 0283 — `zeroSectorU`

## Declaration kind

This declaration is a **`def`**.

It is not a theorem. It introduces the quadratic quantity `U` used in zero-sector inversion. Using the preceding declaration 0282 `zeroSectorX`, which defines

$$
X=2r+s,
$$

it fixes the named integer quantity

$$
U=X^2+5s^2.
$$

## Lean type

```lean
/-- The positive quadratic quantity `U = X^2+5*s^2`. -/
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

Hence its full Lean type is

```lean
zeroSectorU : ℤ → ℤ → ℤ
```

## Mathematical meaning

For inputs `r,s : ℤ`, substituting the definition from 0282,

$$
X=2r+s,
$$

gives

$$
\operatorname{zeroSectorU}(r,s)
=(2r+s)^2+5s^2.
$$

Expanding,

$$
U=4r^2+4rs+6s^2
=2(2r^2+2rs+3s^2).
$$

Thus `U` is a quadratic form in `r,s`.

The source docstring calls it `The positive quadratic quantity`, but **this `def` alone does not imply $U>0$ for every input**. In fact, when `r=s=0`, one has $U=0$. On the other hand,

$$
U=X^2+5s^2,
$$

so for integer `r,s` one always has

$$
U\ge 0.
$$

Moreover, if `U=0`, then `X=0` and `s=0`, hence `r=0`. In that sense the underlying quadratic form is positive definite and becomes strictly positive on nonzero inputs.

However, this declaration itself contains neither a nonzero hypothesis nor a positivity theorem, so the word “positive” in the docstring is best understood as anticipating the later candidate conditions rather than as a theorem bundled into this definition.

## Role in the overall proof

By 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split`, the zero-sector arithmetic has produced the tenth-power decomposition

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}.
$$

The `SignedGoldenZeroSectorInversion` layer beginning at 0282 reorganizes that factorization data into inversion coordinates. The source-level design starts with

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

and then defines

$$
A=U-W,
\qquad
B=U+W.
$$

Thus 0283 `zeroSectorU` is the step that **lifts the linear coordinate `X` into a quadratic quantity**.

The later definitions `zeroSectorA` and `zeroSectorB` use `U` as their common center:

$$
A=U-W,
\qquad
B=U+W.
$$

Algebraically, `U` is therefore the midpoint quantity of the inversion-factor pair `(A,B)`, while `W` is the symmetric offset from that center.

The generated-source chapter comment further states that the diagonal quartic identity and the tenth-power split lead to

$$
AB=4Q^5.
$$

`zeroSectorU` is one of the basic definitions needed to build the central expression underlying that factorization.

## Direct dependencies

### 0282 `zeroSectorX`

The only custom DkMath declaration directly referenced is

```lean
zeroSectorX r s
```

with the preceding definition

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

so `zeroSectorU` is written as

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

rather than expanding the linear coordinate inline.

### Integer squaring, addition, and multiplication

The body uses only squaring via

```lean
^ 2
```

together with the integer literal `5`, multiplication, and addition.

### Relation to 0281

The code of `zeroSectorU` does not directly reference 0281. At the proof-design level, however, 0281 supplies the parameter `d` used by the next declaration 0284 `zeroSectorW`; that `W` is paired with 0283's `U` to define `A` and `B`. Thus 0281 is the arithmetic data source, while 0283 belongs to the coordinate system that receives and reorganizes that data.

## Construction flow

### 1. Accept signed integer coordinates `r,s`

```lean
(r s : ℤ)
```

The inversion layer returns to signed integer coordinates rather than staying solely in natural absolute values, so the sign of `s` is preserved.

### 2. Evaluate the diagonal coordinate from 0282

```lean
zeroSectorX r s
```

namely

$$
X=2r+s.
$$

### 3. Square `X`

```lean
zeroSectorX r s ^ 2
```

This produces a sign-independent nonnegative quadratic contribution.

### 4. Add `5s²`

```lean
+ 5 * s ^ 2
```

which yields

$$
U=X^2+5s^2.
$$

### 5. Feed the result into the symmetric inversion factors

Immediately afterward the canonical source defines

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5


def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d


def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

so `U` is reused as the common central term in `A` and `B`.

## Lean-specific details

There is no proof term in this declaration; the right-hand side is the definition itself.

Therefore

```lean
zeroSectorU r s
```

definitionaly unfolds to

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

and, after also unfolding `zeroSectorX`, to

```lean
(2 * r + s) ^ 2 + 5 * s ^ 2
```

For example,

```lean
example (r s : ℤ) :
    zeroSectorU r s = zeroSectorX r s ^ 2 + 5 * s ^ 2 := by
  rfl
```

closes by definitional equality alone.

To prove an expanded identity such as

```lean
zeroSectorU r s = 4 * r ^ 2 + 4 * r * s + 6 * s ^ 2
```

a natural Lean approach would be `simp [zeroSectorU, zeroSectorX]` followed by `ring` or `ring_nf`, although such a theorem is not part of this declaration itself.

## Redundancy and duplication

The definition body is one line and contains essentially no internal redundancy.

In principle, later definitions `zeroSectorA` and `zeroSectorB` could inline

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

and eliminate `zeroSectorU`. Doing so, however, would obscure the symmetric structure

$$
A=U-W,
\qquad
B=U+W.
$$

Thus the separate `zeroSectorU` definition is useful primarily for **structural naming and reuse**, not merely for reducing character count. The current design is therefore well justified.

## Optimization candidates

### A dedicated expansion lemma

If later proofs repeatedly need the expanded form, one could introduce a lemma such as

```lean
theorem zeroSectorU_expanded (r s : ℤ) :
    zeroSectorU r s = 4 * r ^ 2 + 4 * r * s + 6 * s ^ 2 := by
  simp [zeroSectorU, zeroSectorX]
  ring
```

This could make later algebraic transformations more explicit.

However, the complete usage frequency has not been audited here, and the identity can be regenerated easily with `ring`, so it is not yet clear that adding another API theorem would be beneficial.

### Positivity lemmas

Because the source docstring calls `U` a positive quadratic quantity, it may be useful to expose that property explicitly through lemmas such as

```lean
theorem zeroSectorU_nonneg (r s : ℤ) : 0 ≤ zeroSectorU r s := ...
```

or

```lean
theorem zeroSectorU_pos_of_ne_zero
    (r s : ℤ) (h : r ≠ 0 ∨ s ≠ 0) : 0 < zeroSectorU r s := ...
```

The first follows directly from nonnegativity of squares. Whether later proofs actually need either lemma has not been established from this declaration alone, so these remain optimization candidates rather than recommendations.

### Converting to `abbrev`

As with 0282, one could theoretically make the declaration an `abbrev`, but the current `def` provides a useful and explicit unfold/rewrite boundary for the named inversion coordinate. There is no clear evidence that changing it would improve the development.

## Required Mathlib imports and import optimization

The repository's standalone canonical artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its manifest places this declaration in

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The declaration itself only requires integer arithmetic, powers, and 0282 `zeroSectorX`, so importing all of Mathlib is unlikely to be intrinsically necessary for this one line.

However, the repository does not store the original pre-concatenation source module as a separate file, so the exact import list of the original module could not be inspected. In addition, this run deliberately does not perform a Lean build, so no proposed minimal import set has been experimentally verified.

Accordingly, the only confirmed statement is that the standalone artifact uses **`import Mathlib`**. No specific reduced import list is asserted as proven.

## Comparator challenge suitability

### Verdict: low suitability as a standalone challenge

`zeroSectorU` is a one-line definition rather than a theorem. Turning the definition itself into a Comparator challenge would amount to proving

```lean
zeroSectorU r s = zeroSectorX r s ^ 2 + 5 * s ^ 2
```

by `rfl`, which offers little proof-strategy diversity.

A derived challenge would be more meaningful. For example, competitors could prove

$$
U=4r^2+4rs+6s^2,
$$

or

$$
U\ge0,
\qquad
U=0\iff r=0\land s=0.
$$

Those formulations would allow comparison among `ring`, `positivity`, and explicit integer square arguments.

Hence **the definition itself is not a good Comparator challenge, while derived quadratic-form theorems are suitable**.

## Cross-check against the PDFs

The target branch contains the existing files

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

as confirmed from the repository tree.

However, the available GitHub connector cannot return binary PDF contents as UTF-8 text, and the raw-PDF retrieval route also failed in this run. Therefore the exact page, section, and wording in the PDFs corresponding to `U=X^2+5s^2` could not be verified.

This document consequently does not invent a PDF page or section reference. Its technical interpretation is restricted to what is confirmed by the Lean canonical source and the existing theorem-museum material in the repository.

## Next declaration to read

The next declaration is **0284 `zeroSectorW`**, also a `def`:

```lean
/-- The quantity `W = 4*d^5` supplied by `|H(r,s)| = d^10`. -/
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

That is,

$$
W=4d^5.
$$

Where 0283 `U` is a quadratic central quantity constructed from `r,s`, 0284 `W` brings the `d` obtained from the tenth-power split

$$
|H(r,s)|=d^{10}
$$

into the inversion coordinates at fifth-power scale.

Once both are available, the following symmetric factor pair can be defined:

$$
A=U-W,
\qquad
B=U+W.
$$

Thus the natural dependency order is

$$
\texttt{zeroSectorX}
\to
\texttt{zeroSectorU}
\to
\texttt{zeroSectorW}
\to
(\texttt{zeroSectorA},\texttt{zeroSectorB}).
$$
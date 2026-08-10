# 0101 — `SquareGoldenN`

## Lean type

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

## Mathematical statement

`SquareGoldenN` is not a theorem but the second coordinate definition in `SquareGoldenNormalForm.lean`.

From natural numbers `z,y`, it constructs the integer

$$
N=zy.
$$

In Lean, the product is fixed in the integer world, so the right-hand side is written as

```lean
(z : ℤ) * (y : ℤ)
```

Where 0100 `SquareGoldenM` provides the endpoint-square mass

$$
M=z^2+y^2,
$$

this definition provides the endpoint cross-beam

$$
N=zy.
$$

The later square/golden normal form uses this pair $(M,N)$ as its basic coordinate system.

## Role in the overall proof

In 0093–0099, inside `SquareGoldenBridge.lean`, the coordinates used to pass to the golden norm were written directly inside formulas as

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y.
$$

In `SquareGoldenNormalForm.lean`, the endpoints are rewritten generically as `z,y`, and 0100 together with the present definition promotes

$$
M:=\mathrm{SquareGoldenM}(z,y)=z^2+y^2,
$$

$$
N:=\mathrm{SquareGoldenN}(z,y)=zy
$$

to named APIs.

This $N$ is not merely a product. It is the second coordinate appearing in all four invariants used later:

$$
M-2N,
$$

$$
M^2-4N^2,
$$

$$
\mathrm{GoldenNorm}(M,N),
$$

$$
(2M+N)^2-5N^2.
$$

Thus `SquareGoldenN` carries the cross term connecting the square world with the golden-ratio quadratic form.

## Direct dependencies

There are no project-local direct dependencies. The definition itself uses only:

1. `ℕ` and `ℤ`.
2. The coercions `(z : ℤ)` and `(y : ℤ)` from naturals to integers.
3. Integer multiplication.

Conceptually, it can be read as a renaming of the second coordinate

$$
(g+y)y
$$

that appeared in 0096 `GN5_eq_goldenNorm_squareLink`, now expressed as the generic endpoint coordinate $zy$. This is not a direct source dependency, however, but an architectural correspondence in the proof.

## Proof flow

Because this is a `def`, there is no theorem proof script. Lean only performs definitional unfolding.

Unfolding

```lean
SquareGoldenN z y
```

gives

```lean
(z : ℤ) * (y : ℤ)
```

The reason to isolate such a simple definition is not to shorten computation, but to give all later theorem statements a common coordinate vocabulary.

## Lean-specific processing

### 1. The codomain is `ℤ` from the beginning

The inputs are in `ℕ`, but the output is in `ℤ`. This makes later expressions such as

$$
M-2N
$$

and

$$
M^2-4N^2
$$

natural to state.

If `SquareGoldenN` had type `ℕ → ℕ → ℕ`, later subtraction would require additional conditions or casts to avoid the truncation behavior of `Nat.sub`.

### 2. The cast location is fixed at the API boundary

Because the definition performs the casts in

```lean
(z : ℤ) * (y : ℤ),
```

callers can simply write `SquareGoldenN z y` instead of repeating coercions each time.

### 3. Definitional reduction remains available

`SquareGoldenN` is a `def`, not an opaque theorem, so it can be reduced back to the product using `unfold SquareGoldenN` or `simp [SquareGoldenN]`. The immediately following theorem `squareGolden_tenth_boundary_base` unfolds both `SquareGoldenM` and `SquareGoldenN` and then closes the resulting identity with `ring`.

## Redundancy and duplication

The expression $zy$ already appears in 0096 as

```lean
↑((g + y) * y) : ℤ
```

so from a purely computational perspective this definition repackages an expression that already exists.

The duplication is naturally understood as intentional. The role of 0096 is to bridge `GN5` to `GoldenNorm`, whereas this section is building the public coordinate API for `SquareGoldenNormalForm`. The expression is the same, but its architectural role is different.

Also, 0100 `SquareGoldenM` and the present definition almost always appear together, so keeping them as two separate functions introduces a small amount of boilerplate.

## Optimization candidates

### Candidate A — Bundle the coordinate pair into a structure

Conceptually, one could introduce

```lean
structure SquareGoldenCoords where
  M : ℤ
  N : ℤ
```

and construct both coordinates from `z,y` at once.

This would reduce repeated occurrences of `SquareGoldenM z y` and `SquareGoldenN z y` in later theorem statements. On the other hand, the current two-function design has very simple unfolding behavior and keeps every statement completely explicit. A structure is therefore not automatically superior.

### Candidate B — Add a common endpoint-coordinate constructor

A smaller change would be to add a constructor returning the pair

```lean
(SquareGoldenM z y, SquareGoldenN z y)
```

while leaving the current API intact. This would allow later bundling without breaking existing statements.

### Candidate C — Keep the current design

The definition is one line and has predictable reduction behavior. From a proof-audit perspective, the present form is strong because it keeps $M=z^2+y^2$ and $N=zy$ directly visible instead of hiding them behind additional abstraction. At this stage, keeping the current design is a conservative and reasonable choice.

## Required Mathlib imports and import-optimization candidates

The standalone artifact uses

```lean
import Mathlib
```

for the whole file.

For `SquareGoldenN` alone, however, only natural numbers, integers, the `Nat`-to-`Int` coercion, and integer multiplication are needed. Thus `import Mathlib` is much broader than necessary for this declaration by itself.

The full `SquareGoldenNormalForm.lean` module immediately uses `ring`, `exact_mod_cast`, and previously established FLT5 theorems. Therefore the exact minimal import set for the module should not be asserted without Lean build verification.

A safe import-optimization process would first restore the project-local source module explicitly, then narrow the umbrella `Mathlib` import incrementally while checking the build at each step. No Lean build is performed in this museum entry.

## Comparator challenge suitability

Yes, although this is better suited to an API-design challenge than to a theorem-proving challenge.

Three designs can be compared:

1. The current independent functions `SquareGoldenM` / `SquareGoldenN`.
2. A constructor returning a pair.
3. A `SquareGoldenCoords` structure.

Useful comparison metrics include later theorem-statement length, ease of unfolding, `simp` behavior, localization of casts, and proof-audit readability.

A small Lean challenge could also be

```lean
example (z y : ℕ) :
    SquareGoldenN z y = (z : ℤ) * (y : ℤ) := by
  rfl
```

which checks that the statement is definitionally true and can be closed by `rfl`.

## Next theorem to read

The Lean source places the following theorem immediately after this definition:

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

It is the first theorem to use the two coordinates prepared in 0100 and 0101 simultaneously, extracting the square boundary

$$
M-2N=z^2+y^2-2zy=(z-y)^2.
$$

Therefore `squareGolden_tenth_boundary_base` is the natural next declaration in dependency order.

## Sources and notes

The formal basis for this entry is the `SquareGoldenNormalForm.lean` section embedded in the generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch.

The standalone manifest records the original source as `DkMath/FLT/Five/SquareGoldenNormalForm.lean`, but that path could not be fetched directly from this branch in this run. Therefore this article does not make claims about the current contents of the split source file; the Lean code embedded in the generated artifact is treated as the primary formal evidence.

A concrete page-level correspondence for this declaration in the existing Japanese and English PDFs was not confirmed in this run. No PDF section number, page number, or narrative correspondence has therefore been guessed.
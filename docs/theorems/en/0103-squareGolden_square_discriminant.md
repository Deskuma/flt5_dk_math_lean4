# 0103 — `squareGolden_square_discriminant`

## Lean type

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

## Mathematical statement

Writing 0100 `SquareGoldenM` and 0101 `SquareGoldenN` as

$$
M=z^2+y^2,\qquad N=zy,
$$

the theorem states

$$
M^2-4N^2=(z^2-y^2)^2.
$$

The left-hand side factors as a difference of squares,

$$
M^2-4N^2=(M-2N)(M+2N).
$$

After substituting the endpoint coordinates,

$$
M-2N=(z-y)^2,
$$

and

$$
M+2N=(z+y)^2,
$$

so their product is

$$
(z-y)^2(z+y)^2=(z^2-y^2)^2.
$$

The Lean proof, however, does not reconstruct this factorization route. It directly reuses 0098 `endpoint_square_discriminant`.

## Role in the overall proof

`SquareGoldenNormalForm.lean` projects the Branch-B fifth-power normal form into square/golden coordinates $(M,N)$ and packages several invariants simultaneously.

Where 0102 `squareGolden_tenth_boundary_base` provides the lower-degree square boundary

$$
M-2N=(z-y)^2,
$$

this theorem provides the independent square discriminant

$$
M^2-4N^2=(z^2-y^2)^2.
$$

Later, `exists_branchB_squareGoldenNormalForm` obtains the result directly as

```lean
have hSquare := squareGolden_square_discriminant z y
```

and passes it into the square-discriminant component of the final `BranchBSquareGoldenNormalForm` packet.

Thus the theorem's role is to preserve, at the new coordinate API level, the already established fact that the endpoint-square discriminant is a perfect square.

## Direct definitions and lemmas used

There are three project-local direct dependencies.

1. 0100 `SquareGoldenM`
2. 0101 `SquareGoldenN`
3. 0098 `endpoint_square_discriminant`

The coordinate definitions are

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2

def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

and the reused lemma is

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

## Proof flow

The proof has two steps.

### 1. Unfold the square/golden coordinates

```lean
unfold SquareGoldenM SquareGoldenN
```

The goal then becomes, over the integers, essentially

```lean
(((z : ℤ) ^ 2 + (y : ℤ) ^ 2) ^ 2
    - 4 * (((z : ℤ) * (y : ℤ)) ^ 2)) =
  (((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2)
```

### 2. Apply the existing endpoint lemma

```lean
exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

After unfolding, the goal matches the type of 0098, so its proof term closes the theorem directly.

The important point is that this theorem itself does not run `ring`. The calculation is centralized in 0098, while the present theorem only performs API adaptation.

## Lean-specific processing

### 1. The `ℕ` to `ℤ` boundary is absorbed by the coordinate definitions

The inputs `z y` are natural numbers, but `SquareGoldenM` and `SquareGoldenN` return integers. After `unfold`, `(z : ℤ)` and `(y : ℤ)` are explicit and can be passed directly to the integer-valued theorem 0098.

### 2. No cast tactic is required

The proof uses none of `push_cast`, `norm_cast`, or `exact_mod_cast`. The necessary coercions are explicit in the theorem application

```lean
(z : ℤ) (y : ℤ)
```

itself.

### 3. Successful `exact` is itself an API-alignment audit

Because the proof closes with `exact` rather than letting `simpa` or `ring` absorb discrepancies, it makes clear that, after unfolding the coordinate definitions, the statement is definitionally aligned with 0098.

## Redundancy and duplication

Mathematically, this theorem and 0098 express the same identity. The present theorem is a wrapper that lifts 0098 into the `(SquareGoldenM, SquareGoldenN)` API and adds no new calculation.

If minimizing proof code were the only objective, later code could call 0098 directly every time. That would force clients of the `SquareGoldenNormalForm` layer to descend back to the endpoint representation, however, weakening the abstraction boundary.

The duplication is therefore best understood as intentional API duplication: a lower-level fact is being lifted into the vocabulary of a higher layer.

The theorem is also close to 0102. Article 0102 preserves

$$
M-2N=(z-y)^2,
$$

whereas the present theorem preserves

$$
M^2-4N^2=(z^2-y^2)^2.
$$

Both are square identities, but the later packet stores them as separate invariants, so their proof roles are independent.

## Optimization candidates

### Candidate A — use `simpa` to unfold the coordinate API

The current proof is

```lean
unfold SquareGoldenM SquareGoldenN
exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

A one-expression alternative is

```lean
simpa [SquareGoldenM, SquareGoldenN] using
  endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

This is shorter, while the current version more visibly separates “unfold the coordinates” from “apply the established fact,” which is useful for auditing.

### Candidate B — package endpoint coordinates as a pair or structure

If `SquareGoldenM` and `SquareGoldenN` continue to appear almost exclusively together, a coordinate pair or structure could expose this theorem as one of its invariants.

At the current stage, however, two lightweight definitions plus wrapper theorems keep the proof surface smaller.

### Candidate C — derive it from 0102 by factorization

One could combine 0102 with

$$
M^2-4N^2=(M-2N)(M+2N)
$$

and prove separately that $M+2N=(z+y)^2$. Since 0098 already exists, this route only lengthens the proof.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

The present theorem itself directly needs natural/integer coercions, `SquareGoldenM` / `SquareGoldenN`, and the already proved `endpoint_square_discriminant`. It does not invoke `ring` itself.

The dependency closure still needs the facilities used by 0098, whose proof is `ring`, so a `Mathlib.Tactic.Ring`-class import is plausibly part of a minimized setup.

The surrounding `SquareGoldenNormalForm.lean` module also uses later tactics such as `exact_mod_cast`, so the module-wide minimum import set should not be asserted without a Lean build. A safe import-optimization process would first separate the project-local `SquareGoldenBridge` dependency from tactic imports and then validate reductions incrementally. No Lean build is performed in this article.

## Comparator challenge suitability

This theorem is highly suitable, especially because the comparison concerns wrapper-theorem design rather than merely polynomial automation.

Useful variants include:

1. the current `unfold ...; exact ...` proof;
2. `simpa [SquareGoldenM, SquareGoldenN] using ...`;
3. `unfold ...; ring`, deliberately not reusing 0098;
4. a factorization proof built from 0102.

Evaluation should consider not only proof-term length, but also reuse, abstraction boundaries, auditability, and stability under lower-level changes.

For this theorem, the current approach of reusing the existing theorem with `exact` is likely to express the architecture better than recomputing the identity.

## Next declaration to read

The next major declaration in the Lean source is

```lean
structure BranchBSquareGoldenNormalForm
    (x y z a b : ℕ) : Prop where
  normal : BranchBFifthPowerNormalForm x y z a b
  golden_eq :
    GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
  tenth_boundary :
    SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
  square_discriminant :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
  discriminant_five :
    (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
        5 * (SquareGoldenN z y) ^ 2 = 4 * (b : ℤ) ^ 5
```

Here the tenth-power boundary from 0102, the square discriminant from 0103, and the golden-norm/discriminant-five information are collected into one packet.

Therefore `BranchBSquareGoldenNormalForm` is the natural next declaration in dependency order.

## Sources and notes

The formal source is the generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch, specifically its `SquareGoldenNormalForm.lean` section. There this theorem follows `squareGolden_tenth_boundary_base`, and later `exists_branchB_squareGoldenNormalForm` uses it directly via `have hSquare := squareGolden_square_discriminant z y`.

A concrete page-level correspondence with the existing Japanese and English PDFs could not be established in this run. GitHub code search returned an upstream error, so no PDF page, section number, or narrative correspondence has been filled in by conjecture.

The standalone artifact is generated and records `DkMath/FLT/Five/SquareGoldenNormalForm.lean` as the split-source name. This article treats the current standalone content fetched from the target branch as its primary formal evidence.
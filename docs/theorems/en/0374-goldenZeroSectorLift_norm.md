# 0374 `goldenZeroSectorLift_norm`

## Declaration kind

`theorem`

## Lean code

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

## Lean type

```lean
goldenZeroSectorLift_norm :
  (x : GoldenInt) →
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd
```

For every golden integer `x : GoldenInt`, the theorem states that the golden norm of 0372 `goldenZeroSectorLift` is exactly the quartic factor `goldenFifthSndFactor` appearing in the second coordinate of a fifth power.

Writing `x=(r,s)` and

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr),
$$

the theorem is the identity

$$
N\bigl(T(r,s)\bigr)=H(r,s).
$$

## Mathematical meaning

This theorem is the **algebraic re-entry point** of the zero-sector descent.

The second coordinate of `gamma^5` factors into a visible factor `5s` and a quartic factor `H(r,s)`. The quadratic lift `T` from 0372 is designed precisely so that this quartic factor becomes the norm of a golden integer.

Writing the golden norm as

$$
N(a,b)=a^2+ab-b^2
$$

and substituting

$$
a=r^2+rs+s^2,
\qquad
b=s^2,
$$

gives

$$
N(T(r,s))
=
(r^2+rs+s^2)^2
+(r^2+rs+s^2)s^2
-s^4.
$$

After expansion and collection of terms, this is exactly the quartic polynomial `goldenFifthSndFactor r s`.

Thus an integer polynomial `H(r,s)` is reinterpreted as a norm in the golden integer ring. Downstream, the information `H(r,s)=D^5` can therefore be transported into a factorization problem saying that a product in the golden integers is a fifth power.

## Role in the overall proof

`SignedGoldenZeroSectorDescent.lean` does not finish the remaining zero-sector quartic equation purely in integer coordinates. Instead, it sends that equation back into the golden integer ring.

Conceptually the chain is

$$
H(r,s)=D^5
\Longrightarrow
N(T(r,s))=D^5
\Longrightarrow
T(r,s)\overline{T(r,s)}=D^5.
$$

The present theorem supplies the first arrow, namely

$$
H(r,s)
\longleftrightarrow
N(T(r,s)).
$$

The immediately following 0375 `goldenZeroSectorLift_mul_conj` combines this theorem with `golden_mul_conj` to obtain

```lean
goldenMul (goldenZeroSectorLift x)
  (goldenConj (goldenZeroSectorLift x)) =
    goldenOfInt (goldenFifthSndFactor x.fst x.snd)
```

so that the norm identity becomes a product identity inside the golden ring.

## Direct dependencies

### `goldenZeroSectorLift`

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

This is the quadratic map deliberately constructed so that its norm reproduces the quartic factor.

### `goldenNorm`

The golden norm on `GoldenInt`, given in explicit coordinates by a quadratic form. It is unfolded by `simp only` in this proof.

### `goldenFifthSndFactor`

The quartic polynomial obtained from the second coordinate of a golden fifth power after removing the visible factor `5*s`. It is the right-hand side of the theorem.

### `ring`

A Mathlib tactic that closes the resulting polynomial identity by normalization in the commutative ring of integers.

## Proof flow

The proof has two stages.

First,

```lean
simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
```

unfolds exactly the three relevant definitions and reduces the structure projections. The goal becomes a pure polynomial identity in `x.fst` and `x.snd` over `ℤ`.

Then

```lean
ring
```

normalizes both sides to the same polynomial normal form and closes the goal.

No divisibility, coprimality, valuation, or descent theorem is used yet. The content here is the exact verification that the chosen lift has the algebraic shape required by the later descent.

## Lean-specific processing

### `simp only`

The proof deliberately uses `simp only` rather than unrestricted `simp`. This keeps the unfolding dependency explicit and avoids relying on unrelated simp lemmas, which is useful for standalone extraction and Comparator-style challenges.

### Structure projection reduction

After `goldenZeroSectorLift x` is unfolded, a `GoldenInt` constructor appears. Its `.fst` and `.snd` projections reduce by Lean's computation rules to the corresponding coordinate expressions.

### Reflective polynomial reasoning with `ring`

Instead of writing a sequence of hand-expanded algebra lemmas, the proof delegates the polynomial equality to normalization. Since the coefficients live in `ℤ`, the commutative-ring requirements of `ring` are satisfied.

## Redundancy and overlap

The proof itself is short and contains no obvious tactic-level redundancy.

The definition of `goldenZeroSectorLift` is tightly coupled to this norm identity, so the definition and theorem encode closely related information. Together with 0373 `goldenZeroSectorLift_snd`, they expose the two properties of the lift that downstream proofs actually need.

This is better viewed as an intentional API boundary than as accidental duplication: downstream code can use the named theorem without repeatedly unfolding the lift implementation.

## Optimization candidates

### 1. Adding `[simp]`

Marking this theorem `[simp]` is possible but should be treated cautiously. Automatic rewriting from the norm form to the quartic form may be convenient in some places, but later descent arguments may intentionally want to preserve the norm representation. The current explicit rewrite API makes the re-entry step visible.

### 2. Replacing the two-step proof

One could investigate alternatives such as `ring_nf`, but the current

```lean
simp only [...]
ring
```

separates definition unfolding from polynomial normalization very clearly. It is already close to an optimal proof for readability.

### 3. Factoring out a pure quartic identity

If the same polynomial equality were needed outside the golden-ring context, a separate lemma over `ℤ` could state the expanded quartic identity directly, with the present theorem as a corollary. The current repository evidence does not establish that such an abstraction would be reused, so this remains only an optimization candidate.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

for the generated development as a whole.

This theorem itself needs essentially:

- `GoldenInt` and its coordinate projections;
- `goldenZeroSectorLift`;
- `goldenNorm`;
- `goldenFifthSndFactor`;
- integer arithmetic and powers;
- `simp only`;
- the `ring` tactic.

Therefore `import Mathlib` is much broader than necessary for this declaration alone. The main tactic-side dependency is whatever import supplies `ring`.

However, the full `SignedGoldenZeroSectorDescent.lean` module later uses divisibility, coprimality, `omega`, `norm_num`, `exact_mod_cast`, and other facilities, so its minimal module-level import set is wider. Because this task does not run a Lean build, the exact minimal import set is not certified here.

## Comparator challenge suitability

**Very suitable.**

A compact challenge can provide only the three relevant definitions and ask for

```lean
example (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  ?_
```

A good solution must identify the required definitions to unfold, reduce structure projections, and recognize that the remaining nontrivial quartic equality is a `ring` goal.

Compared with 0373, which mainly tests definitional equality, this theorem has more value as a Comparator challenge because it exercises three distinct steps:

1. controlled definition unfolding;
2. coordinate reduction;
3. polynomial normalization.

Combining it with 0375 would additionally test the ability to assemble an API chain from coordinate identity to norm identity to conjugate-product identity.

## Technical significance

The essential point is that the zero-sector quartic factor is brought back inside the golden integer ring.

As a bare integer equation,

$$
H(r,s)=D^5
$$

looks like a quartic-equals-fifth-power Diophantine condition. After rewriting

$$
H(r,s)=N(T(r,s)),
$$

it becomes

$$
T(r,s)\overline{T(r,s)}=D^5,
$$

which exposes a factorization structure.

This makes it possible to reuse machinery developed earlier in the FLT5 proof: relative-prime factorization, extraction of a unit times a fifth power, and classification into five unit sectors. In that sense, this theorem is the bridge that recursively restarts the golden-integer machinery inside the zero-sector descent.

## Next declaration to read

The next declaration is **`goldenZeroSectorLift_mul_conj`**.

Its declaration kind is `theorem`.

```lean
theorem goldenZeroSectorLift_mul_conj (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x) (goldenConj (goldenZeroSectorLift x)) =
      goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

Where 0374 reinterprets the quartic factor as a norm, 0375 expands that norm as `x * conjugate(x)` and therefore produces the exact product form consumed by the subsequent coprime-factor argument.

# 0375 `goldenZeroSectorLift_mul_conj`

## Declaration kind

`theorem`

## Lean code

```lean
theorem goldenZeroSectorLift_mul_conj (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x) (goldenConj (goldenZeroSectorLift x)) =
      goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

## Lean type

```lean
goldenZeroSectorLift_mul_conj :
  (x : GoldenInt) →
    goldenMul (goldenZeroSectorLift x)
      (goldenConj (goldenZeroSectorLift x)) =
        goldenOfInt (goldenFifthSndFactor x.fst x.snd)
```

For every `x : GoldenInt`, the product of the quadratic lift `goldenZeroSectorLift x` with its conjugate is equal to the golden-integer embedding of the quartic factor `goldenFifthSndFactor x.fst x.snd` appearing in the second coordinate of a fifth power.

Writing `x=(r,s)` and

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr),
$$

0374 `goldenZeroSectorLift_norm` gives

$$
N(T(r,s))=H(r,s).
$$

The present theorem additionally applies the golden-order identity

$$
\alpha\overline{\alpha}=N(\alpha)
$$

and realizes

$$
T(r,s)\overline{T(r,s)}=H(r,s)
$$

as an equality internal to `GoldenInt`. On the Lean side, the integer `H(r,s)` is embedded back into `GoldenInt` with `goldenOfInt`.

## Mathematical meaning

0374 recognized the quartic factor as a norm, but a norm is still an `ℤ`-valued object. This theorem returns that integer value to `GoldenInt` and turns it into a **product identity**.

Conceptually, the re-entry is

$$
H(r,s)
\xleftarrow{\;0374\;}
N(T(r,s))
\xleftarrow{\;\alpha\bar\alpha=N(\alpha)\;}
T(r,s)\overline{T(r,s)}.
$$

This matters because the downstream fifth-power factorization machinery works directly with a product in the golden order,

$$
A\overline A=B^5,
$$

rather than merely with an integer equation saying that a norm is a fifth power. Thus 0375 is the connection between quartic arithmetic and relative-prime factorization in the golden integer ring.

## Role in the overall proof

The purpose of `SignedGoldenZeroSectorDescent.lean` is to reconstruct a smaller candidate of the same type from a surviving zero-sector candidate and then exclude it by infinite descent.

To do that, the lift `T(r,s)` built from zero-sector coordinates must first be returned to a fifth-power factorization problem inside the golden order.

This theorem is the bridge. Downstream, `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower` uses it in the form

```lean
calc
  goldenMul (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) =
      goldenOfInt (goldenFifthSndFactor p.base.fst p.base.snd) :=
    goldenZeroSectorLift_mul_conj p.base
  _ = goldenOfInt ((p.D : ℤ) ^ 5) := by rw [p.H_eq]
  _ = goldenPow (goldenOfInt (p.D : ℤ)) 5 :=
    goldenOfInt_pow_five (p.D : ℤ)
```

Hence the conceptual chain is

$$
H(r,s)=D^5
\Longrightarrow
T(r,s)\overline{T(r,s)}=D^5
\Longrightarrow
\text{coprime fifth-power factorization}
\Longrightarrow
T(r,s)=\varepsilon\gamma^5.
$$

The present theorem supplies the entrance to the second stage.

## Direct dependencies

### `goldenZeroSectorLift`

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

The quadratic lift designed to re-express the quartic factor as a golden norm.

### `goldenConj`

The conjugation operation on golden integers. It supplies the second factor in `golden_mul_conj`.

### `goldenMul`

Multiplication on `GoldenInt`; it constructs the product on the left-hand side.

### `goldenOfInt`

The embedding of integers into `GoldenInt`. Since the norm is `ℤ`-valued, this embedding is required to state the equality as one inside the golden order.

### `golden_mul_conj`

```lean
theorem golden_mul_conj (x : GoldenInt) :
    goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x) := by
  ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

The general Lean theorem expressing

$$
\alpha\overline\alpha=N(\alpha).
$$

It is the first rewrite in the present proof.

### `goldenZeroSectorLift_norm`

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

The preceding theorem 0374 identifying the norm of the quadratic lift with the quartic factor. It is the second rewrite in the proof.

## Proof flow

The proof is a single line:

```lean
rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

The first rewrite changes

```lean
goldenMul (goldenZeroSectorLift x)
  (goldenConj (goldenZeroSectorLift x))
```

into

```lean
goldenOfInt (goldenNorm (goldenZeroSectorLift x)).
```

The second rewrite applies 0374 to the norm occurring inside `goldenOfInt`, replacing it by

```lean
goldenFifthSndFactor x.fst x.snd.
```

The resulting expression is exactly the right-hand side, so the proof closes.

No new use of `ring`, `omega`, divisibility, or coprimality is needed in this theorem. All algebraic computation has already been encapsulated in `golden_mul_conj` and 0374.

## Lean-specific processing

### Composition with `rw`

`rw [golden_mul_conj, goldenZeroSectorLift_norm]` applies two abstract rewrite APIs in sequence. The proof closes without unfolding any implementation definitions directly.

### Rewriting under a surrounding function

The second rewrite acts not on the whole goal but on the subexpression

```lean
goldenNorm (goldenZeroSectorLift x)
```

inside `goldenOfInt (...)`. This is a standard example of Lean rewriting through congruence under an outer function.

### Avoiding definitional unfolding

The proof never unfolds the coordinate definitions of `goldenMul`, `goldenConj`, `goldenNorm`, or `goldenZeroSectorLift`. Using prior theorems as APIs decouples this result from implementation details.

## Redundancy and overlap

There is essentially no code-level redundancy. The two rewrites reflect the mathematical structure directly.

Logically, this theorem is only the composition of 0374 with `golden_mul_conj`, so it introduces no independent new mathematical fact. Nevertheless, naming the composition is useful: downstream proofs avoid repeating the same two rewrites, and the product-form re-entry property of `goldenZeroSectorLift` becomes an explicit API boundary.

## Optimization candidates

### 1. Shortening with `simpa`

One could attempt a `simpa`-style proof built from the preceding theorems, but the current

```lean
rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

makes the transformation order transparent and is arguably clearer.

### 2. Marking lemmas `[simp]`

If `golden_mul_conj` or `goldenZeroSectorLift_norm` were simp lemmas, this theorem might collapse to `simp`. However, some later proofs may intentionally want to preserve either the norm form or the conjugate-product form. The repository code does not establish that global automatic rewriting would be an improvement, so the current explicit rewrite is safer.

### 3. Keep the named bridge

Because downstream `exists_lift_eq_fifthPower` refers to this theorem directly, deleting it and inlining the rewrites would make the dependency structure less visible. Retaining the named bridge is therefore a useful abstraction rather than gratuitous duplication.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

for the whole generated file.

For this theorem alone, the effective requirements are mainly

- `GoldenInt`
- `goldenMul`
- `goldenConj`
- `goldenOfInt`
- `goldenZeroSectorLift`
- `goldenFifthSndFactor`
- `golden_mul_conj`
- `goldenZeroSectorLift_norm`
- the `rw` tactic

Unlike 0374, this theorem itself does not invoke `ring`. Therefore, if the dependency theorems are already imported from their defining modules, the tactic requirement here is quite small.

The whole `SignedGoldenZeroSectorDescent.lean` module is broader because later declarations use fifth-power factorization, coprimality, divisibility, `omega`, `norm_num`, and related machinery. Since no Lean build is performed in this task, the exact minimal import set is not confirmed.

## Comparator challenge suitability

**Suitable**, though easier than 0374 and best viewed as an API-composition micro challenge.

For example, expose `golden_mul_conj` and `goldenZeroSectorLift_norm` and ask for

```lean
example (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x)
      (goldenConj (goldenZeroSectorLift x)) =
        goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  ?_
```

The evaluation points are whether the solver can

1. turn the left-hand side into a norm using the general theorem `golden_mul_conj`,
2. rewrite that norm with 0374,
3. reuse the existing API instead of unnecessarily unfolding coordinate definitions.

Paired with 0374, this gives two distinct Comparator tasks: first proving a nontrivial polynomial identity, then composing its result through an abstract ring API.

## Technical significance

This theorem is the **ring re-embedding bridge** that makes the recursive zero-sector descent possible.

By 0374 one has

$$
H(r,s)=N(T(r,s)).
$$

The present theorem upgrades this to

$$
T(r,s)\overline{T(r,s)}=\iota(H(r,s)),
$$

where `\iota` is `goldenOfInt`. Substituting `H(r,s)=D^5` then produces

$$
T(r,s)\overline{T(r,s)}=\iota(D^5),
$$

a fifth-power product equation inside the golden order.

At that point the already established machinery such as `goldenCoprimeFactorOfFifthPower` can be reused. The zero-sector quartic equation is therefore not solved as an unrelated new Diophantine problem; it is routed back into the earlier theorem that a relatively prime product which is a fifth power splits into unit-times-fifth-power factors. This one-line theorem fixes precisely that connection.

## Next declaration to read

The next declaration is **`GoldenZeroSectorDescentPacket`**.

Its declaration kind is `structure`.

The repository places it immediately after the present theorem with the explanatory docstring that the invariant preserved by fifth-power re-entry stores both the visible coordinate as five times a fifth power and the quartic factor itself as a fifth power:

```lean
structure GoldenZeroSectorDescentPacket where
  base : GoldenInt
  t : ℕ
  D : ℕ
  t_pos : 0 < t
  D_pos : 0 < D
  ...
```

Declarations 0372–0375 establish the quadratic-lift re-entry API. The next stage is therefore to study the packet type that makes this re-entry iterable as a genuine descent invariant.

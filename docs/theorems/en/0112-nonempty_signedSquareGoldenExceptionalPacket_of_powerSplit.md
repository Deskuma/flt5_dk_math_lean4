# 0112 — `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`

## Lean type

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

This theorem is `private`, so it is not part of the public module API. Its role is to prove that an exact five-adic power split `s` yields a concrete witness of the 0111 structure `SignedSquareGoldenExceptionalPacket`, which is then consumed by `Classical.choice` immediately afterward.

## Mathematical statement

Given `SignedFiveAdicPowerSplit u v w`, in either the difference or sum orientation one can choose integral coordinates $M,N,\delta$ satisfying simultaneously

$$
\operatorname{GoldenNorm}(M,N)=5b^5,
$$

$$
M-2N=5^8a^{10},
$$

$$
M^2-4N^2=\delta^2,
$$

$$
(2M+N)^2-5N^2=20b^5,
$$

where $a,b$ are `s.a` and `s.b`. Thus a `SignedSquareGoldenExceptionalPacket u v w` exists.

The key point is that the two signed orientations use different coordinates, but both normalize to the same four invariant shapes.

## Role in the full proof

0111 only declared the packet type. This theorem is the first actual constructor theorem showing that the packet can always be built from the signed five-adic power split. It is therefore the effective transformer from the signed five-adic layer to the square-golden layer.

Immediately afterward the source defines

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

so this theorem sits exactly at the boundary between proof-only existence and the downstream data API.

## Direct dependencies

The main declarations used directly or materially are:

1. `SignedFiveAdicPowerSplit`
   - Input `s`; the proof uses `s.fiveAdic`, `s.a`, `s.b`, `s.carrier_eq`, and `s.residual_eq`.
2. `SignedSquareGoldenExceptionalPacket`
   - The output packet type from 0111.
3. `SignedSquareGoldenSource`
   - Constructors `.difference` and `.sum` populate the provenance field.
4. `right_lt_of_fermat5Equation`
   - Supplies $v\le w$ in the difference branch.
5. `GN5_eq_goldenNorm_squareLink`
   - Converts the difference-side `GN5` residual to `GoldenNorm`.
6. `sumGN5_eq_goldenNorm_signed`
   - 0108; converts the sum-side `SumGN5` residual to the signed `GoldenNorm` form.
7. `endpoint_square_discriminant`
   - Supplies the difference-side square discriminant.
8. `signed_endpoint_square_discriminant`
   - 0109; supplies the sum-side square discriminant.
9. `four_mul_goldenNorm_eq_discriminant_five`
   - Converts the golden-norm identity into the discriminant-five identity.

## Proof flow

The proof begins with

```lean
let p := s.fiveAdic
cases p.source with
```

and splits on the five-adic provenance.

### Difference orientation

For the difference source it sets

```lean
let M : ℤ := (w : ℤ) ^ 2 + (v : ℤ) ^ 2
let N : ℤ := (w : ℤ) * (v : ℤ)
let delta : ℤ := (w : ℤ) ^ 2 - (v : ℤ) ^ 2
```

`right_lt_of_fermat5Equation` yields $v\le w$. Then `Nat.sub_add_cancel` converts the gap coordinate $w-v$ back to the endpoint coordinate $w$, allowing

```lean
GN5_eq_goldenNorm_squareLink (w - v) v
```

to be reshaped into

$$
\operatorname{GoldenNorm}(M,N)=GN5(w-v,v).
$$

The residual identity from the source and `s.residual_eq` then give

$$
\operatorname{GoldenNorm}(M,N)=5b^5.
$$

For the boundary, the source carrier equality is cast to integers to prove

$$
M-2N=(p.carrier)^2,
$$

then `s.carrier_eq` and polynomial normalization give

$$
(5^4a^5)^2=5^8a^{10}.
$$

The square discriminant is reused directly from `endpoint_square_discriminant`.

Finally,

$$
(2M+N)^2-5N^2=4\operatorname{GoldenNorm}(M,N)
$$

comes from `four_mul_goldenNorm_eq_discriminant_five`; substituting `hGolden` reduces this to $20b^5$.

The branch ends with the record constructor

```lean
exact ⟨{
  powerSplit := s
  M := M
  N := N
  delta := delta
  source := .difference rfl rfl rfl
  golden_eq := hGolden
  tenth_boundary := hBoundary
  square_discriminant := hSquare
  discriminant_five_eq := hDiscFive }⟩
```

### Sum orientation

The sum branch chooses

```lean
let M : ℤ := (u : ℤ) ^ 2 + (v : ℤ) ^ 2
let N : ℤ := -((u : ℤ) * (v : ℤ))
let delta : ℤ := (u : ℤ) ^ 2 - (v : ℤ) ^ 2
```

The golden norm comes from 0108 `sumGN5_eq_goldenNorm_signed` via `simpa [M, N]`. The carrier boundary is rewritten from the source equality, then normalized with `push_cast`, `dsimp`, and `ring`. The square discriminant is supplied directly by 0109 `signed_endpoint_square_discriminant`.

The discriminant-five calculation and final packet constructor are structurally identical to the difference branch, except that the provenance field is

```lean
source := .sum rfl rfl rfl
```

## Lean-specific processing

### `Nonempty` and `Classical.choice`

The conclusion is `Nonempty (...)`, not the packet itself. The construction is explicit, but the public downstream API separates the existence proof from the chosen witness and uses `Classical.choice` in a following `noncomputable def`.

### `private theorem`

This theorem is intentionally an implementation detail. Downstream code is expected to use `signedSquareGoldenExceptionalPacket_of_powerSplit`, insulating later proofs from constructor details.

### Natural subtraction and casts

In the difference branch, `w - v` is natural subtraction, so the proof must explicitly establish $v\le w$ for `Nat.cast_sub` and `Nat.sub_add_cancel`. The sum branch instead uses the integral negative cross term $N=-uv$ from the start and therefore avoids truncation issues.

### `simpa`, `push_cast`, and `ring`

The proof has three clear normalization layers: `simpa` reshapes upstream theorems to local definitions, `push_cast` normalizes embeddings from naturals to integers, and `ring` closes the final polynomial identities.

## Redundancy and duplication

The difference and sum branches duplicate most of the proof after coordinate selection. In particular, the following parts are nearly identical:

- converting the residual to $5b^5$,
- converting the carrier square to $5^8a^{10}$,
- deriving `hDiscFive`,
- constructing the final packet record.

The duplication improves auditability of each provenance branch, but maintenance requires synchronized changes.

As noted in 0111, `discriminant_five_eq` is also logically derivable from `golden_eq`, so storing it as a field is an API convenience rather than a minimal logical requirement.

## Optimization candidates

1. Factor each orientation into a helper returning `(M,N,delta,hGoldenBase,hSquare)`, then share the remainder of the construction.
2. Extract the derivation of `hDiscFive` from `golden_eq` into a common theorem.
3. Name the carrier-power normalization lemma
   `((5^4*a^5 : ℕ : ℤ)^2) = 5^8*(a:ℤ)^10`.
4. Compare the current `Nonempty` + `Classical.choice` split with a direct `noncomputable def` that constructs the packet internally.
5. Introduce an orientation abstraction to reduce branch duplication, but only if it preserves the current branch-local auditability.

## Required Mathlib imports and import optimization

The generated standalone artifact begins with

```lean
import Mathlib
```

so that import is sufficient for the current artifact.

The theorem uses tactics and base lemmas including `ring`, `push_cast`, `norm_num`, `Nat.cast_sub`, and `Nat.sub_add_cancel`, in addition to the DkMath five-adic packet, GN5 / SumGN5 bridges, square discriminant identities, and golden-norm discriminant bridge.

The standalone artifact does not preserve the exact minimal import list of the original source module. Therefore a smaller import set is likely possible, but it is not established here because this run intentionally does not perform a Lean build.

## Comparator challenge suitability

**Very suitable.** This theorem supports several alternative proof architectures while preserving the same output packet.

Useful competitors are:

1. the current fully explicit two-branch proof,
2. orientation-specific coordinate helpers plus one common constructor,
3. a generic normalization proof using `SignedSquareGoldenSource` as an eliminator,
4. a minimal packet design where `discriminant_five_eq` is derived rather than stored.

Evaluation should include not only line count but also elaboration stability, cast burden, error locality, readability of branch provenance, and resistance to upstream definition changes.

## Position in the source material

The target branch contains both `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The connector did not inspect the corresponding PDF pages in this run, so no page or section number is guessed.

The formal source of truth is the generated `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` section inside `Flt5DkMath/FLT5StandAlone.lean`.

## Next declaration to read

The next declaration is

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

0112 proves existence via `Nonempty`; this next declaration chooses that witness and exposes it as reusable data. It is therefore the dependency-ordered transition from a proof proposition to a reusable packet object and should not be skipped.
# 0111 — `SignedSquareGoldenExceptionalPacket`

## Lean type

```lean
/--
The exceptional square-golden packet common to both signed five-adic sources.
The single residual five-layer becomes a golden norm `5*b^5`, while the
carrier becomes the tenth-power square boundary `5^8*a^10`.
-/
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  source : SignedSquareGoldenSource u v w M N delta
  golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
  tenth_boundary : M - 2 * N = (5 : ℤ) ^ 8 * (powerSplit.a : ℤ) ^ 10
  square_discriminant : M ^ 2 - 4 * N ^ 2 = delta ^ 2
  discriminant_five_eq :
    (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (powerSplit.b : ℤ) ^ 5
```

`SignedSquareGoldenExceptionalPacket u v w` is not a proposition in `Prop`; it is a `Type` that retains concrete witnesses together with proofs about them.

## Mathematical statement

This structure packages the square-golden coordinates obtained from a signed five-adic power split into one common form.

Let the integer coordinates be

$$
M,N,\delta\in\mathbb Z,
$$

and write the natural-number witnesses carried by `powerSplit` as $a,b$. The packet stores the following four invariants simultaneously:

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
(2M+N)^2-5N^2=20b^5.
$$

In addition, the `source` field uses 0110 `SignedSquareGoldenSource` to record whether $(M,N,\delta)$ came from the difference orientation or the sum orientation.

Thus the packet does not erase the two signed branches. Rather, it **bundles common invariants and branch provenance into the same object** so that downstream arguments can use a uniform interface.

## Role in the overall proof

This declaration is the central data boundary of `SignedSquareGoldenExceptional.lean`.

Upstream, `SignedFiveAdicPowerSplit` stores the exact power split of the carrier and residual in the exceptional five-adic case. In that form, however, the arithmetic is still expressed as two natural-number orientations, difference and sum.

0110 `SignedSquareGoldenSource` unifies the provenance, and 0111 combines it with four facts: the `GoldenNorm` equation, the square boundary, the square discriminant, and the discriminant-five identity. Downstream golden-integer arguments can therefore consume this packet without reopening the original Fermat equation or repeating the branch split.

In particular, the later `SignedGoldenRamifierStrippedPacket` stores the present packet in its `exceptional` field and proceeds to golden-integer coordinates corresponding to

$$
\alpha=M+N\varphi.
$$

Accordingly, 0111 is best viewed as the **hand-off object from the natural-number/five-adic layer to the golden-integer layer**.

## Direct dependencies

The declaration has three direct type-level dependencies.

1. `SignedFiveAdicPowerSplit u v w`
   - Stores the exceptional five-adic normal form and the exact power witnesses `a` and `b`.
   - The right-hand sides of `golden_eq` and `tenth_boundary` refer to `powerSplit.a` and `powerSplit.b`.

2. `SignedSquareGoldenSource u v w M N delta`
   - The provenance type introduced in 0110.
   - Records whether $(M,N,\delta)$ comes from the difference or sum signed coordinate system.

3. `GoldenNorm M N`
   - The two-variable golden norm introduced by the square-golden bridge.
   - In this exceptional packet it is identified with $5b^5$, exposing one residual factor of $5$.

The structure declaration itself has no proof script, so 0108 `sumGN5_eq_goldenNorm_signed` and 0109 `signed_endpoint_square_discriminant` do not appear literally in its field types. They are nevertheless important construction dependencies because the immediately following packet-construction theorem uses them to fill these fields.

## Construction flow

The `structure` declaration itself performs no proof. The following theorem carries the actual constructor proof:

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

That theorem splits on `s.fiveAdic.source`, handles the difference and sum cases separately, defines $M,N,\delta$, proves the four required invariants, and finally returns a `Nonempty` witness of essentially the following form:

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

with `source := .sum ...` in the sum branch.

Thus 0111 defines the storage format, while the next theorem normalizes branch-specific arithmetic into this common packet.

## Lean-specific processing

### Why the declaration lives in `Type`

Unlike proposition-only packets such as `BranchBSquareGoldenNormalForm`, this declaration lives in `Type`. Downstream code needs to project and reuse computationally and structurally meaningful witnesses such as `M`, `N`, `delta`, and `powerSplit`.

For example, later proofs directly read fields such as

```lean
p.M
p.N
p.powerSplit.b
```

so a data-carrying `Type` is more natural than a purely proof-irrelevant proposition.

### Dependent fields

`golden_eq` and `tenth_boundary` depend on the previously declared `powerSplit` field:

```lean
golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
```

This is a dependent record: later fields refer to data stored in earlier fields.

### The `ℕ` to `ℤ` boundary

The external parameters `u v w` and the power witnesses remain natural numbers, while $M,N,\delta$ and all four invariants are expressed over integers. This allows the sum orientation with $N=-uv$ to be represented directly and avoids truncated natural-number subtraction.

## Redundancy and duplication

`discriminant_five_eq` is likely algebraically derivable from `golden_eq` together with the definition of `GoldenNorm`. Earlier in the square-golden development, a wrapper theorem already converts a golden-norm equality into the corresponding discriminant-five identity.

Therefore one possible logical design would store only

```lean
golden_eq
```

and expose `discriminant_five_eq` as a derived theorem.

The current design nevertheless has a clear API advantage: later golden arithmetic repeatedly wants the discriminant-five equation in exactly this shape. Materializing it as a field avoids unfolding `GoldenNorm` and invoking ring normalization each time. This is an intentional tradeoff between logical minimality and downstream usability.

Likewise, the tuple `M`, `N`, `delta`, and `source` is conceptually cohesive and could be factored into a dedicated coordinate structure.

## Optimization candidates

1. Introduce a small `SignedSquareGoldenCoordinates` structure containing `M`, `N`, `delta`, and `source`.
2. Compare the current stored `discriminant_five_eq` field with a design where it is a derived theorem from `golden_eq`.
3. Push common difference/sum construction of `hSquare` and `hDiscFive` into orientation-independent lemmas.
4. If `powerSplit.a` and `powerSplit.b` are used repeatedly downstream, add projection aliases to shorten long field chains.
5. Split the packet into a minimal core plus a derived API layer, separating logical assumptions from ergonomic convenience.

The current flat packet still has a significant auditing advantage: all facts required by downstream proofs are visible in one record.

## Required Mathlib imports and import optimization

The generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch begins with

```lean
import Mathlib
```

so `Mathlib` is sufficient for the artifact as checked in.

The generated artifact does not preserve the original per-module import lines, however, so the exact minimal Mathlib import set of `SignedSquareGoldenExceptional.lean` cannot be established from this artifact alone.

The structure declaration itself uses no tactics. It requires only `ℕ`, `ℤ`, exponentiation, and previously defined DkMath types and definitions. A future import-minimization pass should therefore explicitly import the DkMath modules providing

- `SignedFiveAdicPowerSplit`,
- the square-golden bridge / `GoldenNorm`, and
- the signed square-golden source layer,

then reduce transitive Mathlib dependencies by actual builds.

**Inference:** the declaration itself probably does not require a direct `import Mathlib` umbrella import. Because this run intentionally performs no Lean build, that minimal import set is not claimed as verified.

## Comparator challenge suitability

**Suitable.** This is more interesting as a data-model/API-design challenge than as a tactic-length challenge.

A comparator can implement the same downstream theorem using three designs:

1. the current flat structure;
2. a two-layer `Coordinates` + `Invariants` structure;
3. a minimal-field structure where `discriminant_five_eq` is derived rather than stored.

Useful metrics include constructor-proof length, projection readability, rewrite stability, downstream theorem length, import dependencies, and resilience to later representation changes.

## Position in the available sources

The target branch contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The GitHub connector used in this run did not provide a direct page-level comparison inside those PDFs, so no page or section number is guessed here.

The final formal authority is the `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next theorem to read

The next declaration should be the immediately following private theorem

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

Where 0111 declares **what must be stored**, this theorem actually constructs the packet from the two difference/sum orientations. It is where 0108 `sumGN5_eq_goldenNorm_signed`, 0109 `signed_endpoint_square_discriminant`, and the existing difference-side square-golden bridge converge, making it the natural next dependency step.

# 0252 — `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`

## Lean type

```lean
/-- The stripped element times its conjugate is an embedded fifth power. -/
theorem SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenMul p.beta (goldenConj p.beta) =
      goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5 := by
  rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

This is a `theorem` stating that the product of the ramifier-stripped element `beta` with its conjugate is a genuine fifth power inside the golden order.

## Mathematical statement

A `SignedGoldenRamifierStrippedPacket` already carries the field

$$
N(\beta)=b^5.
$$

On the other hand, the general identity 0176 `golden_mul_conj` gives

$$
\beta\overline{\beta}=N(\beta).
$$

Finally, 0251 `goldenOfInt_pow_five` transports the integer fifth power into the golden order.

Thus the theorem expresses the chain

$$
\beta\overline{\beta}
=N(\beta)
=b^5
=(\operatorname{goldenOfInt} b)^5
$$

through the raw golden-order API.

If

$$
z:=\operatorname{goldenOfInt}(b),
$$

then the theorem has the standard factorization form

$$
\beta\overline{\beta}=z^5.
$$

This is exactly the form needed for the subsequent coprime-factor extraction step.

## Role in the full proof

Declarations 0241–0247 establish and package the relative primality of `beta` and `goldenConj beta`. In particular, the certified state supplies

$$
GoldenRelPrime(\beta,\overline{\beta}).
$$

Separately, the stripped packet from 0231 stores the norm certificate

$$
N(\beta)=b^5.
$$

The present theorem converts that integer-valued norm information into an equality of factors inside the golden ring.

After 0252, the two inputs required by the generic contract `GoldenCoprimeFactorOfFifthPower` are available:

1. `GoldenRelPrime beta (goldenConj beta)`;
2. `goldenMul beta (goldenConj beta) = goldenPow z 5`.

Therefore 0252 is the bridge from **the norm is a fifth power** to **the product of the relatively prime factors is itself a fifth power**.

Once this conversion is available, the Euclidean-domain / gcd machinery can be used by the generic coprime-factor theorem to conclude a representation of the form

$$
\beta=\varepsilon\gamma^5.
$$

## Direct dependencies

The proof directly uses exactly three named facts:

- 0176 `golden_mul_conj`;
- the packet field `p.beta_norm`;
- 0251 `goldenOfInt_pow_five`.

The statement also depends on:

- `SignedGoldenRamifierStrippedPacket`;
- `GoldenInt`;
- `goldenConj`;
- `goldenMul`;
- `goldenOfInt`;
- `goldenPow`.

Conceptually the dependency is simply the composition of

$$
\beta\overline{\beta}=N(\beta),
\qquad
N(\beta)=b^5,
\qquad
\operatorname{goldenOfInt}(b^5)=\operatorname{goldenOfInt}(b)^5.
$$

## Proof flow

The entire proof is one rewrite chain:

```lean
rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

### 1. Replace the conjugate product by the norm

`golden_mul_conj` rewrites

```lean
goldenMul p.beta (goldenConj p.beta)
```

to

```lean
goldenOfInt (goldenNorm p.beta).
```

### 2. Use the packet's norm certificate

The field `p.beta_norm` rewrites

```lean
goldenNorm p.beta
```

to

```lean
(p.exceptional.powerSplit.b : ℤ) ^ 5.
```

### 3. Convert the embedded integer fifth power into a golden fifth power

0251 `goldenOfInt_pow_five` rewrites

```lean
goldenOfInt ((p.exceptional.powerSplit.b : ℤ) ^ 5)
```

to

```lean
goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5.
```

At that point the goal is closed.

## Lean-specific processing

The proof uses only `rw`, applying the three equality theorems from left to right.

A notable feature is that no coordinate definition is unfolded. The proof never expands the concrete coordinates of `beta`, the formula for `goldenConj`, the polynomial defining `goldenMul`, or the recursion behind `goldenPow`.

This makes 0252 a good example of the theorem API successfully hiding the explicit-coordinate implementation.

The field `p.beta_norm` is a dependent structure projection. Its type already refers to the same nested value `p.exceptional.powerSplit.b`, so Lean does not need any manual transport of the integer parameter.

## Redundancy and duplication

Logically, the theorem contains little information beyond the composition of three already established equalities. Downstream code could repeat

```lean
rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

wherever the result is needed.

Nevertheless, a dedicated theorem is useful API redundancy:

- it exposes the exact form consumed by the generic coprime-factor theorem;
- downstream proofs do not need to know the provenance of `beta_norm`;
- it hides the route through the conjugate/norm identity and integer-embedding bridge;
- it records the mathematical milestone “the stripped element times its conjugate is a fifth power” in a theorem name.

Thus it is a wrapper in logical terms, but an important interface theorem in the proof graph.

## Optimization candidates

1. **Keep the current proof**
   - three rewrites only, with very clear provenance.

2. **Compress with `simpa`**
   - one could potentially start from `golden_mul_conj p.beta` and simplify using `p.beta_norm` and 0251.
   - Exact simp behavior is unverified because this museum pass does not run a Lean build.

3. **Publish a standard `*` / `^` notation version**
   - using 0159 `golden_mul_eq` and 0160 `golden_pow_eq`, one could expose a Mathlib-style statement such as

```lean
p.beta * goldenConj p.beta =
  (goldenOfInt (...) : GoldenInt) ^ 5
```

4. **Bundle the integer embedding and norm as morphisms**
   - making `goldenOfInt` a `RingHom` and the norm a multiplicative map could let generic `map_pow`-style lemmas replace some bridge theorems.

The current theorem already matches the exact downstream consumer shape, so local optimization is not urgent.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself uses only `rw`; its direct Mathlib surface is therefore very small.

Its real dependencies are the local golden-order APIs for:

- algebra on `GoldenInt`;
- conjugation and norm;
- the stripped packet;
- integer embedding and powers.

The surrounding `SignedGoldenFifthPower.lean` module continues into a generic factorization contract and later connects to Euclidean-domain machinery, so import minimization should be evaluated at module scope rather than from 0252 alone.

No Lean build is performed in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem is small enough that API-design differences are easy to isolate.

Possible competitors are:

- A: current three-step `rw` proof;
- B: `simpa` from `golden_mul_conj p.beta`;
- C: normalize to standard `*` / `^` notation first;
- D: derive the result from bundled `RingHom` / multiplicative-norm APIs;
- E: reprove the equality by direct coordinate expansion.

Useful comparison axes are proof length, dependency depth, visibility of mathematical provenance, the raw/standard API boundary, robustness under upstream refactoring, and standalone auditability.

The contrast between A and E is especially useful: A composes established theorem-level abstractions, whereas E recomputes the explicit coordinates.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenFifthPower.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The repository source confirms that this theorem immediately follows 0251 `goldenOfInt_pow_five`, and that the generic contract `GoldenCoprimeFactorOfFifthPower` follows immediately afterward.

The target branch also contains `docs/pdf/FLT5-main-ja-v0-r1.pdf` and `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0253 `GoldenCoprimeFactorOfFifthPower`**:

```lean
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

This is not a theorem but an `abbrev : Prop`. It defines the generic coprime-factor extraction contract:

$$
xy=z^5,
\qquad
\operatorname{RelPrime}(x,y)
$$

should imply

$$
x=\varepsilon\gamma^5.
$$

By 0252, the stripped packet has been converted exactly into the input shape required by this contract. Declaration 0253 therefore moves away from packet-specific arithmetic and exposes the general fifth-power factor-extraction interface over the golden Euclidean domain.
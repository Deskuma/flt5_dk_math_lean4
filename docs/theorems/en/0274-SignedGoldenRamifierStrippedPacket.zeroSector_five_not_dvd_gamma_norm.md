# 0274 — `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm`

## Declaration kind

This declaration is a **`theorem`**.

It is a zero-sector specialization lemma in `SignedGoldenZeroSector.lean`. It transports the already established general result `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm`, for a unit-times-fifth-power representation, to the pure fifth-power case where the unit factor is `1`.

## Lean type

```lean
/-- In the zero sector the base norm is not divisible by five. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  apply p.five_not_dvd_gamma_norm goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

Mathematically, if the packet coordinate `beta` is a pure fifth power

$$
\beta=\gamma^5,
$$

then the golden norm of `gamma` is not divisible by five:

$$
5\nmid N(\gamma).
$$

Because `goldenNorm gamma` is integer-valued, Lean states the conclusion using divisibility in `ℤ`:

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

## Mathematical meaning

At the general unit-times-fifth-power layer one has a representation

$$
\beta=\epsilon\gamma^5,
\qquad \epsilon\in\mathcal O^\times.
$$

Earlier results show that the norm of `gamma` agrees, up to sign, with the packet power-split base `b`. The packet also carries

$$
5\nmid b.
$$

Consequently, the general theorem

```lean
SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
```

concludes

$$
5\nmid N(\gamma).
$$

In the zero sector the unit representative is

$$
\varphi^0=1,
$$

so the hypothesis reduces to

$$
\beta=\gamma^5.
$$

The present theorem simply reinterprets this as

$$
\beta=1\cdot\gamma^5
$$

and supplies `goldenOne` as the unit to the general theorem.

Thus this theorem proves no new five-adic arithmetic by itself. It is a **specialization bridge** carrying the general statement that the fifth-power base norm is a 5-adic unit into the zero-sector API.

## Role in the full proof

0273 `zeroSector_gamma_norm_eq_or_eq_neg` connected the norm itself to packet data in the zero sector:

$$
N(\gamma)=b
\qquad\text{or}\qquad
N(\gamma)=-b.
$$

0274 supplies the complementary statement that this same zero-sector base norm contains no factor of five:

$$
5\nmid N(\gamma).
$$

This non-divisibility is used directly later by `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`. There one assumes for contradiction that

$$
5\mid H(\gamma),
$$

combines that assumption with the congruence information supplied by `five_dvd_goldenFifthSndFactor_sub_norm_sq`, and obtains

$$
5\mid N(\gamma)^2.
$$

Since 5 is prime, this yields

$$
5\mid N(\gamma),
$$

which contradicts the present theorem.

Accordingly, 0274 provides a **5-adic exclusion boundary** for the subsequent zero-sector coordinate arithmetic.

## Direct dependencies

### `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm`

This is the general theorem carrying essentially all of the mathematical content used here.

```lean
theorem SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

In the canonical source, the general theorem assumes `5 ∣ goldenNorm gamma`, splits using `p.gamma_norm_eq_or_eq_neg hepsilon hbeta` into

$$
N(\gamma)=b
\quad\text{or}\quad
N(\gamma)=-b,
$$

and in either branch contradicts the packet field

```lean
p.five_not_dvd_b : ¬ 5 ∣ p.exceptional.powerSplit.b
```

The present theorem does not re-prove that argument.

### `goldenUnit_one`

This theorem supplies the fact that `goldenOne` is a `GoldenUnit`.

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

therefore fixes the general theorem's unit parameter `epsilon` to `goldenOne`.

### `goldenOne`

This is the project-side multiplicative identity of the golden integer ring. It is used to embed the zero-sector hypothesis into the `unit × fifth power` form required by the general theorem.

### `goldenMul`, `goldenPow`

The general theorem requires

```lean
p.beta = goldenMul epsilon (goldenPow gamma 5)
```

whereas the zero-sector hypothesis is

```lean
p.beta = goldenPow gamma 5
```

The final part of the proof bridges the difference between `goldenMul goldenOne (...)` and the pure fifth power.

### `goldenNorm`

This is the norm on `GoldenInt` and the subject of the conclusion. The present theorem neither unfolds nor computes it; all norm arithmetic is delegated to the general theorem.

## Proof flow

### 1. Specialize the general theorem to the unit `1`

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

At this point the proof of

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

is delegated to the general theorem. The remaining goal is only to align the factorization hypothesis.

Conceptually, it remains to show

$$
\beta=\gamma^5
\Longrightarrow
\beta=1\cdot\gamma^5.
$$

### 2. Rewrite `p.beta` using `hbeta`

```lean
rw [hbeta]
```

This replaces the left-hand side `p.beta` by `goldenPow gamma 5`, reducing the remaining goal to the multiplicative identity law.

### 3. Close the equality coordinatewise

```lean
ext <;> simp [goldenOne, goldenMul]
```

`ext` decomposes equality of `GoldenInt` values into equality of their coordinates. The concrete project-side definitions of `goldenOne` and `goldenMul` are then supplied to `simp`, which closes every generated goal.

No norm computation or divisibility calculation occurs in these three proof lines; all such arithmetic has already been encapsulated by the general theorem.

## Lean-specific processing

### Dot notation for a namespace theorem

```lean
p.five_not_dvd_gamma_norm
```

uses dot notation to provide the packet argument `p` to `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm`.

### Inference of the implicit unit parameter

In

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

Lean infers the implicit `epsilon` to be `goldenOne` from the type of `goldenUnit_one`.

### Direction of `rw [hbeta]`

The proof rewrites `p.beta` to `goldenPow gamma 5`, not in the reverse direction. This makes the remaining representation goal the simple comparison between a pure fifth power and `1 ×` that fifth power.

### `ext <;> simp`

Rather than proving the identity law through an abstract ring lemma, the proof descends to the coordinates of `GoldenInt` and simplifies the concrete project definitions.

The `<;>` combinator applies the same `simp` invocation to every subgoal generated by `ext`.

## Redundancy and duplication

The proof is only three lines long, so there is almost no local redundancy.

There is, however, an exact repetition with the adaptation tail of the preceding theorem 0273 `zeroSector_gamma_norm_eq_or_eq_neg`:

```lean
rw [hbeta]
ext <;> simp [goldenOne, goldenMul]
```

Both theorems independently reconstruct the representation alignment

$$
\beta=\gamma^5
\Rightarrow
\beta=1\cdot\gamma^5.
$$

If more zero-sector specializations of the same form accumulate, this could be extracted into a helper lemma. At present the duplication is only two proof lines, so abstraction may cost more navigation than it saves; the optimization priority is low.

## Optimization candidates

### 1. A zero-sector factorization helper

Conceptually, one could introduce a helper such as

```lean
lemma zeroSector_eq_one_mul_fifth
    {beta gamma : GoldenInt}
    (h : beta = goldenPow gamma 5) :
    beta = goldenMul goldenOne (goldenPow gamma 5) := by
  ...
```

Then 0273, 0274, and similar specialization theorems could focus only on applying their general counterparts.

Whether this is worthwhile should be decided after counting how often the same proof pattern occurs in the source.

### 2. Close the identity law abstractly

If the bridge between `goldenMul` and the ring multiplication on `GoldenInt` is stable enough, the coordinate `ext` may be replaceable by a semantic `one_mul`-style proof, possibly of the form

```lean
simpa [...] using hbeta
```

The exact rewrite lemma available under the current import graph is **not verified**, because this run does not perform a Lean build.

### 3. Preserve the paired API of 0273 and 0274

One could alternatively derive 0274 from the 0273 statement

$$
N(\gamma)=\pm b
$$

and the packet field `5 ∤ b`. However, the current implementation directly reuses the already packaged general theorem `five_not_dvd_gamma_norm`, avoiding duplication of its sign and coercion argument. From the viewpoint of dependency reuse, the existing proof is preferable.

## Required Mathlib imports and import optimization

The canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` on the target branch uses

```lean
import Mathlib
```

The present theorem itself directly relies only on ordinary proof mechanisms such as `apply`, `rw`, structure extensionality, `simp`, and pre-existing project theorems. It invokes no advanced Mathlib number-theory theorem directly.

The general theorem `five_not_dvd_gamma_norm`, however, internally uses integer divisibility, signs, coercions, and earlier golden-arithmetic and packet APIs.

Because the standalone artifact concatenates generated source modules, the exact minimal import set of the original `SignedGoldenZeroSector.lean` cannot be determined from this single artifact alone. This run also performs no Lean build, so the reduction of `import Mathlib` to individual Mathlib modules remains **unverified**.

For an import audit, one should first inspect the project import graph supplying at least

- `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm`,
- the golden unit API (`goldenUnit_one`, `goldenOne`), and
- `GoldenInt` arithmetic (`goldenMul`, `goldenPow`, `goldenNorm`),

and then verify any reduced imports with Lean.

## Comparator challenge suitability

**Suitable, but low difficulty.**

A useful challenge would expose the general theorem

```lean
p.five_not_dvd_gamma_norm
```

and the unit proof

```lean
goldenUnit_one
```

and ask the solver to prove the zero-sector theorem from

```lean
hbeta : p.beta = goldenPow gamma 5
```

The evaluation points would be:

1. Reuse the general five-adic theorem instead of re-proving it.
2. Select `goldenOne` / `goldenUnit_one` as the zero-sector unit.
3. Resolve the representation mismatch between `p.beta = gamma^5` and `p.beta = 1 * gamma^5` with `rw`, `ext`, and `simp`.

This is better viewed as an **API specialization / representation alignment challenge** than as a challenge on the core number theory itself.

## Relation to the PDFs

The target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`, and
- `docs/pdf/FLT5-main-en-v0-r1.pdf`.

However, the GitHub connector does not return the PDF binary contents, and fetching the public raw PDFs also failed in this run. The TeX source is stored on the branch only as a zip archive, so it could not be inspected through this path either.

Therefore the exact PDF page, section, or wording corresponding to this theorem is **unverified**, and no such mapping is guessed here. The technical account in this document is grounded directly in the generated Lean source contained in `Flt5DkMath/FLT5StandAlone.lean` and in the existing theorem APIs on the target branch.

## Next declaration to read

The declaration immediately following 0274 in the canonical Lean source is 0275:

```lean
/-- Exact signed second-coordinate equation in the zero sector. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
      -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  ...
```

Where 0274 imposes the norm-side exclusion

$$
5\nmid N(\gamma),
$$

0275 extracts an exact signed product equation from the second coordinate of `gamma^5`, making the zero-sector coordinate arithmetic concrete.

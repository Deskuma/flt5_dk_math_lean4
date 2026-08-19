# 0149 — `goldenFiveNonsquare`

## Lean type

```lean
instance goldenFiveNonsquare : Zsqrtd.Nonsquare 5 := by
  refine ⟨fun n h => ?_⟩
  have hn : n < 3 := by
    by_contra hn
    have h3 : 3 ≤ n := Nat.le_of_not_gt hn
    have h9 : 9 ≤ n * n := by nlinarith
    omega
  interval_cases n <;> norm_num at h
```

This is not a theorem but a typeclass instance of `Zsqrtd.Nonsquare 5`. It supplies Lean's typeclass machinery with the fact that the natural number `5` is not a square, which is required by the downstream `Zsqrtd 5` infrastructure.

## Mathematical statement and meaning of the declaration

The mathematical content is

$$
\nexists n\in\mathbb N,\quad n^2=5.
$$

Thus `5` is not a square in the natural numbers. Concretely,

$$
2^2=4<5<9=3^2,
$$

so no natural number can have square equal to `5`.

Although elementary, this fact is structurally important on the `Zsqrtd 5` side. Registering `Zsqrtd.Nonsquare 5` enables downstream zero-product properties of `Zsqrtd`, which are then transported back to `GoldenInt` through `goldenDoubleEmbedding`.

## Role in the overall proof

The preceding declaration 0148 defines

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

and moves golden integers into the `Zsqrtd 5` representation. The present instance supplies the target type with the nonsquare condition on `5`.

The source then follows the chain

```text
goldenDoubleEmbedding
→ goldenFiveNonsquare
→ goldenDoubleEmbedding_injective
→ goldenDoubleEmbedding_mul
→ GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
→ NoZeroDivisors GoldenInt
→ IsDomain GoldenInt
```

In particular, `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` maps a zero product into `Zsqrtd 5` and invokes `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`. The present instance is therefore an external structural condition needed to promote the explicit golden ring from a `CommRing` to a domain-like object with no zero divisors.

## Direct dependencies

The declaration directly depends on:

- Mathlib's `Zsqrtd.Nonsquare`
- natural-number order and multiplication
- `Nat.le_of_not_gt`
- `nlinarith`
- `omega`
- `interval_cases`
- `norm_num`

`goldenDoubleEmbedding` does not occur in the proof term itself, but it is the immediate structural reason why this instance is introduced at this point in the development.

## Proof / construction flow

The proof has two stages.

First, it shows that any natural number whose square is assumed to be `5` must satisfy `n < 3`:

```lean
have hn : n < 3 := by
  by_contra hn
  have h3 : 3 ≤ n := Nat.le_of_not_gt hn
  have h9 : 9 ≤ n * n := by nlinarith
  omega
```

If `n ≥ 3`, then `n^2 ≥ 9`, contradicting the hypothesis `h` that its square is `5`.

Second, the bound `n < 3` reduces the problem to the finite cases `n = 0, 1, 2`:

```lean
interval_cases n <;> norm_num at h
```

Their squares are `0`, `1`, and `4`, so each case contradicts `h`.

## Lean-specific processing

`refine ⟨fun n h => ?_⟩` directly constructs the field required by `Zsqrtd.Nonsquare 5`. Because this is registered as an instance, later declarations needing `Zsqrtd.Nonsquare 5` can obtain it automatically through typeclass resolution rather than passing it explicitly.

`nlinarith` derives the nonlinear lower bound on `n * n` from `3 ≤ n`, while `omega` closes the resulting natural-number arithmetic contradiction. `interval_cases` turns the small numerical interval into explicit cases, and `norm_num` evaluates each concrete square.

## Redundancy and duplication

Mathematically, the argument could be summarized by the single observation $2^2<5<3^2$, so the present proof is somewhat tactic-driven. It first derives `n < 3` and then enumerates the remaining values, using several arithmetic tactics for a very small constant.

The design choice to register `Zsqrtd.Nonsquare 5` once as an instance is not redundant, however: it prevents the same nonsquare fact from being reproved throughout the later `Zsqrtd`-based argument.

## Optimization candidates

Several alternatives are worth considering.

1. Reuse an existing Mathlib theorem or instance for the nonsquareness of `5`, if an appropriate one is available.
2. Derive the contradiction from a general modular-arithmetic statement about quadratic residues.
3. Keep the finite-case strategy but reduce the number of arithmetic tactics used.
4. If many `Zsqrtd.Nonsquare p` instances are required, derive them from a reusable theorem for suitable primes rather than proving each small constant separately.

The current proof is short and local, however, so replacing it with a more general abstraction may increase dependencies without improving auditability.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This declaration requires the module defining `Zsqrtd` and `Zsqrtd.Nonsquare`, together with the tactics `nlinarith`, `omega`, `interval_cases`, and `norm_num`.

The exact minimal import set is not verified in this museum pass because no Lean build is performed. A narrower combination of the `Zsqrtd` definition module and the necessary tactic imports should be possible, but that remains an explicit optimization hypothesis.

## Suitability as a Comparator challenge

Yes. The same `Zsqrtd.Nonsquare 5` instance can be constructed in several styles:

- the current inequality bound plus `interval_cases`;
- a modular-arithmetic proof using quadratic residues;
- reuse of a general theorem about squares or primes;
- an explicit arithmetic proof avoiding `decide` / `native_decide`.

Useful comparison metrics are proof length, number of tactic dependencies, degree of generality, dependence on Mathlib API, and readability. It is a compact challenge for comparing a local concrete proof against a reusable general theorem.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch. There, this instance appears immediately after `goldenDoubleEmbedding` and immediately before `goldenDoubleEmbedding_injective`.

Japanese and English PDFs also exist on the target branch, but the concrete page corresponding to this supporting instance was not identified directly in this pass. Therefore no PDF page or section number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem goldenDoubleEmbedding_injective :
    Function.Injective goldenDoubleEmbedding := by
  intro x y h
  have hsnd : x.snd = y.snd := congrArg Zsqrtd.im h
  have hfst : 2 * x.fst + x.snd = 2 * y.fst + y.snd :=
    congrArg Zsqrtd.re h
  apply GoldenInt.ext
  · omega
  · exact hsnd
```

By 0149 the target `Zsqrtd 5` has the required nonsquare condition. Declaration 0150 then proves that the doubled embedding loses no information, i.e. that it is injective.
## 0185 — `golden_tau_mul_conj`

## Lean type

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

This is a `theorem` stating that the product of the distinguished ramifier `goldenTau` with its conjugate is the embedded integer `5` inside the golden order.

## Mathematical statement

`goldenTau` is defined by

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

and mathematically represents

$$
\tau=2+\varphi.
$$

The conjugation introduced in 0163 acts by

$$
\overline{a+b\varphi}=(a+b)-b\varphi,
$$

so

$$
\overline{\tau}=\overline{2+\varphi}=3-\varphi.
$$

The present theorem therefore states

$$
\tau\overline{\tau}=5
$$

as an equality internal to `GoldenInt`.

Declaration 0176 `golden_mul_conj` already proves for every golden integer that

$$
x\overline{x}=N(x),
$$

and 0184 `goldenNorm_tau` establishes

$$
N(\tau)=5.
$$

Thus 0185 is the specialization and composition of those two facts at `x=τ`.

A direct coordinate check gives the same result: `goldenTau = ⟨2,1⟩`, `goldenConj goldenTau = ⟨3,-1⟩`, and their golden product is `⟨5,0⟩ = goldenOfInt 5`.

## Role in the full proof

Declarations 0177–0185 organize the concrete ramified element above five inside the golden order.

- `goldenSqrtFive = 2φ-1` has square `5` and norm `-5`.
- `goldenTau = 2+φ` is equal to `φ * goldenSqrtFive`.
- `goldenNorm_tau` establishes `N(τ)=5`.
- The present theorem turns that norm value into the internal factorization `τ * conj τ = 5`.

This is therefore the bridge from a numerical norm certificate to an **explicit ramified factorization inside the ring**.

The next theorem, `exists_goldenTau_factor_of_five_dvd`, extracts an actual `goldenTau` factor from an ordinary integer divisibility condition involving `5 ∣ 2*M+N`. For understanding the exceptional five-adic branch, 0185 records that the rational prime `5` is not merely associated with the norm of `τ`; it actually decomposes as `τ` times its conjugate in the golden order.

## Direct dependencies

The Lean proof directly uses only two named theorems:

- 0176 `golden_mul_conj`
- 0184 `goldenNorm_tau`

The statement itself also uses the definitions:

- `GoldenInt`
- 0178 `goldenTau`
- 0163 `goldenConj`
- 0124 `goldenMul`
- 0162 `goldenOfInt`

The direct proof dependency is therefore essentially

$$
\texttt{golden\_mul\_conj}
+\texttt{goldenNorm\_tau}
\longrightarrow
\texttt{golden\_tau\_mul\_conj}.
$$

As mathematical background, 0183 `goldenTau_eq_phi_mul_sqrtFive`, 0181 `goldenSqrtFive_sq`, 0182 `goldenNorm_sqrtFive`, and 0167 `goldenNorm_phi` explain how `τ` is related to the ramified square root of five.

## Proof flow

The proof consists of two rewrites:

```lean
by
  rw [golden_mul_conj, goldenNorm_tau]
```

1. `golden_mul_conj` specializes to `goldenTau` and rewrites the left-hand side to

$$
goldenOfInt(goldenNorm\ goldenTau).
$$

1. `goldenNorm_tau` rewrites the norm value to `5`.
2. Both sides become `goldenOfInt 5`, so the rewrite sequence closes the goal.

No coordinate expansion, `ring`, or `norm_num` appears in this proof. Unlike the direct coordinate certificate used in 0184, this theorem is deliberately proved by reusing the abstract API already established upstream.

## Lean-specific processing

`rw [golden_mul_conj, goldenNorm_tau]` applies the listed equalities from left to right.

The first rewrite implicitly specializes

```lean
golden_mul_conj goldenTau
```

so that

```lean
goldenMul goldenTau (goldenConj goldenTau)
```

becomes

```lean
goldenOfInt (goldenNorm goldenTau).
```

The second rewrite then replaces the inner norm by `5`, leaving a reflexive equality.

An important design point is that this proof is not merely definitional reduction. It treats 0176 and 0184 as reusable API facts. In this sense, 0185 is a particularly clean example of theorem-level abstraction paying off after a long explicit-coordinate development.

## Redundancy and duplication

Mathematically, this theorem contains very little information beyond the combination of 0176 and 0184. Downstream code could simply repeat

```lean
rw [golden_mul_conj, goldenNorm_tau]
```

whenever the factorization is needed.

However, naming the result is useful API redundancy because `τ * conj τ = 5` is the central ring-theoretic reading of the ramification block. A dedicated theorem provides several benefits:

- the factorization of `5` can be referenced directly;
- downstream code need not know that the proof passes through the norm API;
- the mathematical status of `goldenTau` as the distinguished ramifier becomes visible in theorem names;
- the public factorization interface can remain stable even if the internal norm implementation changes.

Thus the theorem is redundant from a logical-minimality perspective but useful from an API and proof-readability perspective.

## Optimization candidates

Four approaches are worth comparing.

1. **Keep the current proof**
   - two theorem rewrites;
   - short, structural, and mathematically transparent.

2. **Compress to a `simpa` proof**
   - conceptually something like

```lean
simpa [goldenNorm_tau] using golden_mul_conj goldenTau
```

   may work, although the exact simp behavior is unverified here because no Lean build is run.

1. **Use a direct coordinate proof**
   - unfold `goldenTau`, `goldenConj`, and `goldenMul`, then close by `decide`, `norm_num`, or `ring`;
   - this gives shallower theorem dependencies but loses the structural reuse of 0176 and 0184.

2. **Bundle a ramification API**
   - package `τ`, `N(τ)=5`, `τ*conj τ=5`, and factor-extraction properties together;
   - this becomes more attractive if the exceptional five-adic branch grows substantially.

At present, the current proof already offers a strong balance between brevity and mathematical provenance, so there is little pressure to optimize it further.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The present theorem itself uses only a small surface:

- equality rewriting via `rw`
- `GoldenInt` and its raw operations
- `golden_mul_conj`
- `goldenNorm_tau`

It does not directly use `ring`, `norm_num`, analysis, or advanced number-theory APIs.

The upstream proofs of its dependencies do use arithmetic tactics, so the true minimal import set for the full `GoldenOrder` module is governed by the surrounding declarations rather than by 0185 alone. Because this museum pass does not run a Lean build, the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Despite its small size, the theorem gives a clean comparison of proof architecture.

Possible contestants are:

- A: current `rw [golden_mul_conj, goldenNorm_tau]`
- B: a `simpa ... using golden_mul_conj goldenTau` proof
- C: closed coordinate proof via `decide`
- D: explicit `ext` + `simp` + `ring`
- E: a route through `τ=φ√5` and the previously established ramification identities

Useful comparison axes include proof-term size, direct dependency depth, visibility of mathematical provenance, robustness under upstream refactoring, tactic dependence, and readability as a downstream API theorem.

The contrast between A and C is especially instructive: A reuses the structural theorem layer, whereas C recomputes the concrete coordinates.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The current repository state and the preceding 0184 document confirm the sequence

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]

theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

The branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0186 `exists_goldenTau_factor_of_five_dvd`**.

The next stage turns an ordinary integer divisibility condition involving `5` into the constructive appearance of a `goldenTau` factor inside the golden order.

Now that 0184 gives

$$
N(\tau)=5
$$

and 0185 upgrades this to the internal factorization

$$
\tau\overline{\tau}=5,
$$

0186 moves from “five is visible” to “the ramified factor `τ` actually divides the relevant golden integer.”

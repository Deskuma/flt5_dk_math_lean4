# 0250 — `branchB_false_of_goldenConjugateCoprimeCore`

## Lean type

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

This is a `theorem`. It connects the contradiction receiver supplied as 0248 `SignedGoldenConjugateCoprimeCore` to the existing Branch-B routing theorem and derives `False` from a `CounterexamplePack` together with the Branch-B condition.

## Mathematical statement

The logical structure of the theorem is schematically

$$
\mathrm{SignedGoldenConjugateCoprimeCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
\Longrightarrow
\mathrm{BranchB\ counterexample}\to\bot.
$$

The hypothesis `hCore` is a contract saying that any `SignedGoldenConjugateCoprimePacket` yields a contradiction. Declaration 0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore` lifts this local golden-integer contradiction core to a `SignedBranchARefuter`, which rules out every signed Branch-A normal form.

Passing that refuter to the already established `branchB_false_of_signedBranchARefuter` gives `False` from the FLT5 counterexample data `hPack : CounterexamplePack x y z` and the Branch-B condition

$$
5\nmid(z-y).
$$

Thus 0250 itself contains no new divisibility, norm, or conjugation calculation. It is a routing theorem that transports the conjugate-coprime contradiction back to the original Branch-B problem.

## Role in the full proof

Declarations 0241–0244 prove for the ramifier-stripped element `beta` that

$$
\operatorname{GoldenRelPrime}(\beta,\overline\beta).
$$

Declarations 0245–0247 bundle that certificate into a packet and make the certified packet constructible directly from a signed normal form. Declaration 0248 defines the receiver contract that turns such a packet into `False`, and 0249 lifts that receiver to the project-level `SignedBranchARefuter` interface.

Declaration 0250 is the final facade that feeds the output of 0249 into the existing Branch-B routing theorem. The dependency chain of this block is therefore

$$
\text{conjugate coprimality}
\to
\text{certified packet}
\to
\text{local contradiction core}
\to
\text{signed Branch-A refuter}
\to
\text{Branch-B contradiction}.
$$

With this theorem in place, downstream consumers do not need to know how the normal-form packet was constructed or how `beta_relPrime_conj` was proved. Supplying a `SignedGoldenConjugateCoprimeCore` is enough to close Branch B.

## Direct dependencies

The proof directly uses two named theorems:

- 0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore`
- `branchB_false_of_signedBranchARefuter`

The statement also depends on:

- 0248 `SignedGoldenConjugateCoprimeCore`
- `CounterexamplePack`
- `SignedBranchARefuter`
- natural-number divisibility `5 ∣ z - y`
- `False`

The direct proof dependency is extremely shallow:

$$
\texttt{hCore}
\xrightarrow{\texttt{signedBranchARefuter\_of\_goldenConjugateCoprimeCore}}
\texttt{SignedBranchARefuter}
\xrightarrow{\texttt{branchB\_false\_of\_signedBranchARefuter}}
\bot.
$$

## Proof flow

The proof closes with a single `exact`:

```lean
by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

1. Pass `hCore` to 0249 to obtain a `SignedBranchARefuter`.
2. Pass that refuter together with `hPack` and `hBranch` to `branchB_false_of_signedBranchARefuter`.
3. The returned value has type `False`, exactly matching the goal.

No witness expansion, rewriting, simplification, or arithmetic tactic is needed.

## Lean-specific processing

The parameters `{x y z : ℕ}` are implicit. Lean infers them from `hPack : CounterexamplePack x y z` and `hBranch`.

The expression

```lean
signedBranchARefuter_of_goldenConjugateCoprimeCore hCore
```

treats the theorem as a function and produces a value of type `SignedBranchARefuter`. That value is immediately supplied as the first argument of the next theorem, so the proof term is naturally read as nested function application.

`exact` only checks that the constructed term has the target type `False`; no tactic automation beyond ordinary elaboration and definitional reduction is required.

## Redundancy and duplication

Logically, 0250 is just the composition of 0249 with `branchB_false_of_signedBranchARefuter`, so it adds no new mathematical information. A downstream proof could repeat

```lean
exact branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

and omit this named theorem entirely.

There is nevertheless substantial value in keeping the facade theorem:

- the path from the contradiction core to Branch-B closure has a direct searchable name;
- downstream code does not need to expose the intermediate `SignedBranchARefuter` layer;
- the public Branch-B API can remain stable if the packet/refuter construction changes upstream;
- the proof-dependency graph explicitly records that this core closes Branch B.

It is therefore logically redundant but useful architectural redundancy.

## Optimization candidates

1. **Keep the current theorem**
   - the proof is already near-minimal and the routing meaning is clear from the theorem name.

2. **Use term style**

```lean
:= branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

   This may remove the `by exact` wrapper without changing the meaning.

3. **Abstract a common routing helper**
   - if the pattern `Core → SignedBranchARefuter → BranchB false` is repeated across several modules, a generic lifting helper could reduce boilerplate.

4. **Remove the facade and use direct composition everywhere**
   - this reduces code volume but makes the domain-specific proof graph less visible.

Because the current proof is already extremely small, API clarity is more important than local proof compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface needed by this theorem is tiny and consists essentially of:

- function application
- implicit arguments
- `False`
- natural numbers and divisibility notation

No specialized tactic is used.

However, the surrounding `SignedGoldenConjugateCoprime.lean` module uses golden divisibility, norms, conjugation, `Nat.Coprime`, and integer/natural-number casts, so the module-level minimal import set is much broader than the requirements of 0250 alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes, although the interesting comparison is architectural rather than mathematical.

Possible variants are:

- A: the current named facade theorem
- B: direct composition of 0249 and the Branch-B routing theorem at every call site
- C: a generic `Core → Refuter → BranchB false` helper
- D: a higher-level structure/API that hides the intermediate `SignedBranchARefuter` layer

Useful metrics are dependency visibility, simplicity for consumers, robustness under refactoring, theorem-search ergonomics, and clarity of module boundaries rather than raw proof-term length.

In that sense, 0250 is a good Comparator challenge for deciding when a very small theorem deserves to remain as a named API boundary.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In the source, this theorem appears immediately after 0249. The `SignedGoldenConjugateCoprime.lean` generated section ends immediately after 0250, and the next generated module is `SignedGoldenFifthPower.lean`.

The target branch also contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this internal routing theorem was not directly identified in this run, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0251 `goldenOfInt_pow_five`**, the first theorem in the next module `SignedGoldenFifthPower.lean`:

```lean
@[simp] theorem goldenOfInt_pow_five (b : ℤ) :
    goldenOfInt (b ^ 5) = goldenPow (goldenOfInt b) 5 := by
  apply GoldenInt.ext
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
    ring
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

The routing block closes at 0250. Declaration 0251 returns to algebraic content by proving that integer embedding preserves fifth powers in the explicit golden API, preparing the representation of `beta * conj(beta)` as an embedded fifth power.
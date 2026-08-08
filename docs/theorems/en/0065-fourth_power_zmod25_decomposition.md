# 0065 — `fourth_power_zmod25_decomposition`

## Lean type

```lean
private theorem fourth_power_zmod25_decomposition
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    ∃ q : ℕ, (n : ZMod 25) ^ 4 = 1 + 5 * (q : ZMod 25) := by
  let q : ℕ := n ^ 4 / 5
  have hmod : n ^ 4 % 5 = 1 := fourth_power_mod_five_eq_one h5n
  have hsplit := Nat.mod_add_div (n ^ 4) 5
  have hdecomp : n ^ 4 = 1 + 5 * q := by
    dsimp [q]
    omega
  refine ⟨q, ?_⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod 25)) hdecomp
  simpa using hcast
```

This declaration is `private` and is a local lemma used inside `SignedFiveAdic.lean`.

## Mathematical statement

If the natural number `n` is not divisible by 5, then by article 0064,

$$
n^4 \equiv 1 \pmod 5.
$$

Hence there exists a natural number $q$ such that

$$
n^4 = 1 + 5q.
$$

This lemma maps that integer decomposition into `ZMod 25` and provides it in the form

$$
(n : \mathrm{ZMod}\ 25)^4 = 1 + 5(q : \mathrm{ZMod}\ 25).
$$

The important point is that $q$ does not need to be uniquely determined modulo 5. The downstream mod-25 calculations only require the first-order 5-adic information that the fourth power has the form $1+5q$.

## Role in the overall proof

This lemma is the bridge that lifts nonzero fourth-power information modulo 5 into a form usable in calculations modulo 25.

Immediately afterward, `GN5_cast_mod25_eq_five` applies this lemma to `y` under `5 ∣ g` and `5 ∤ y`, expands `GN5 g y` in `ZMod 25`, and reduces it to 5. `SumGN5_cast_mod25_eq_five` likewise applies the lemma to either `u` or `v`.

The dependency flow is approximately

```text
5 ∤ n
  ↓ 0064
n^4 % 5 = 1
  ↓ 0065
n^4 = 1 + 5q
  ↓ cast
(n : ZMod 25)^4 = 1 + 5q
  ↓
mod-25 calculations for GN5 / SumGN5
```

## Direct dependencies

- `fourth_power_mod_five_eq_one` — article 0064
- `Nat.mod_add_div`
- natural-number division `/`
- `omega`
- `congrArg`
- natural-number casts into `ZMod 25`
- `simpa`

The essential direct dependency is 0064. `Nat.mod_add_div` supplies the division algorithm, and `omega` combines that identity with the known remainder value to reconstruct the natural-number decomposition.

## Proof flow

1. Define `q := n ^ 4 / 5`.
2. Obtain `hmod : n ^ 4 % 5 = 1` from article 0064.
3. Use `Nat.mod_add_div (n ^ 4) 5` to obtain the standard quotient-remainder decomposition.
4. Combine `hmod` and the division decomposition with `omega` to derive `n ^ 4 = 1 + 5 * q`.
5. Choose this `q` as the existential witness.
6. Use `congrArg` to cast the natural-number equality into `ZMod 25`.
7. Use `simpa` to normalize the cast equality into the target form.

## Lean-specific processing

Mathematically, one might simply say: “since $n^4 \equiv 1 \pmod 5$, the number $n^4-1$ is divisible by 5.” Over the naturals, however, using the quotient `n^4 / 5` together with `Nat.mod_add_div` avoids explicit management of truncated subtraction.

`hmod` may look unused inside the text of the `hdecomp` proof, but `omega` sees the entire local context and uses both `hmod` and `hsplit`. This makes the proof dataflow slightly less explicit to a human reader.

`congrArg (fun t : ℕ => (t : ZMod 25)) hdecomp` is the standard mechanism used here to transport an equality proved in the naturals into the ring `ZMod 25`.

## Redundancy and duplication

`hmod` and `hsplit` do not appear syntactically in the final equality; they are consumed indirectly by `omega`. Thus the proof intent is partly hidden inside tactic search.

The proof also first establishes a natural-number equality `hdecomp` and then transports it by `congrArg`. If only the mod-25 conclusion were needed, a more direct modular/divisibility API might be possible. On the other hand, the current “integer decomposition → cast” structure is mathematically transparent.

## Optimization candidates

The first candidate is to build `hdecomp` more explicitly from `Nat.mod_add_div` using a `calc` block, rewriting the remainder to 1 before normalization. That could reduce the implicit dependence on `omega` and make the dataflow clearer.

A second candidate is to derive a divisibility statement corresponding to `5 ∣ n ^ 4 - 1` and extract a witness directly, but this introduces management of `Nat.sub` and is not obviously an improvement.

A third candidate is a general lifting lemma from `ZMod 5` to a representation modulo `25` of the form `a + 5q`. This would generalize the recurring pattern “lift information modulo $p$ to a first-order representation modulo $p^2$.” Since this proof fixes 5 and 25, the current short specialized proof also has value.

## Required Mathlib imports and import optimization

The generated standalone artifact assumes `import Mathlib`, and its manifest confirms that the source module `DkMath/FLT/Five/SignedFiveAdic.lean` is among the ordered source modules.

At minimum, this lemma needs functionality for `ZMod`, natural-number division and remainder, the `omega` tactic, and basic cast/simplification support. The exact import lines of the split source file `SignedFiveAdic.lean` were not directly confirmed in this run, so concrete minimal module names are treated as conjectural.

Import minimization should therefore be established only after fetching the split source and build-checking a reduced set covering `ZMod`, Nat mod/div, and Omega.

## Comparator challenge suitability

This is a good candidate. The statement is short, but proof strategies can differ meaningfully.

- Current: `Nat.mod_add_div` + `omega` + `congrArg`
- Candidate A: explicitly extract a divisibility witness
- Candidate B: use `calc` and rewriting to reduce reliance on `omega`
- Candidate C: use a general `ZMod 5` / `ZMod 25` lifting lemma

Useful comparison axes are transparency, tactic dependence, generalizability, import weight, and convenience for downstream rewriting.

## Evidence and conjecture

The declaration name, type, proof body, and the fact that `GN5_cast_mod25_eq_five` immediately consumes this lemma were confirmed in `Flt5DkMath/FLT5StandAlone.lean`. The standalone manifest also confirms that `SignedFiveAdic.lean` is included in the ordered source modules.

The exact page corresponding to this lemma in the existing Japanese and English PDFs was not confirmed in this run, so no PDF-specific claims or page numbers are inferred. Minimal Mathlib imports are likewise conjectural because the split source file's import lines were not directly retrieved.

## Next theorem to read

```lean
private theorem GN5_cast_mod25_eq_five
    {g y : ℕ} (h5g : 5 ∣ g) (h5y : ¬ 5 ∣ y) :
    (GN5 g y : ZMod 25) = 5
```

This is the first lemma that directly consumes `fourth_power_zmod25_decomposition`. It proves that the difference-orientation `GN5` residual is exactly 5 modulo 25, and in dependency order it should be read before `SumGN5_cast_mod25_eq_five`.

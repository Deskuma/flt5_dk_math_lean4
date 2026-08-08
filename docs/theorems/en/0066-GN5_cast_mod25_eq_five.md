# 0066 — `GN5_cast_mod25_eq_five`

## Lean type

```lean
private theorem GN5_cast_mod25_eq_five
    {g y : ℕ} (h5g : 5 ∣ g) (h5y : ¬ 5 ∣ y) :
    (GN5 g y : ZMod 25) = 5 := by
  rcases h5g with ⟨k, rfl⟩
  rcases fourth_power_zmod25_decomposition h5y with ⟨q, hq⟩
  unfold GN5
  push_cast
  rw [hq]
  ring_nf
  simp only [show (25 : ZMod 25) = 0 by decide,
    show (50 : ZMod 25) = 0 by decide,
    show (250 : ZMod 25) = 0 by decide,
    show (625 : ZMod 25) = 0 by decide,
    mul_zero, add_zero]
```

This declaration is `private`; it is a local lemma inside `SignedFiveAdic.lean` that fixes the difference-orientation residual `GN5` modulo 25.

## Mathematical statement

For natural numbers `g,y`, if

$$
5\mid g,\qquad 5\nmid y,
$$

then the image of `GN5` modulo 25 is

$$
\operatorname{GN5}(g,y)\equiv 5\pmod{25}.
$$

Writing `g=5k`,

$$
\operatorname{GN5}(5k,y)
=(5k)^4+5(5k)^3y+10(5k)^2y^2+10(5k)y^3+5y^4.
$$

The first four terms contain factors 625, 625, 250, and 50 respectively, so they vanish modulo 25. Hence

$$
\operatorname{GN5}(5k,y)\equiv 5y^4\pmod{25}.
$$

By article 0065, if $5\nmid y$, there exists $q\in\mathbb N$ such that

$$
y^4=1+5q\quad\text{in }\mathrm{ZMod}\ 25.
$$

Therefore

$$
5y^4=5+25q=5\quad\text{in }\mathrm{ZMod}\ 25.
$$

## Role in the whole proof

This lemma is the entry point for extracting the fact that the cyclotomic residual in the difference orientation has **5-adic valuation exactly one**.

Later, in the difference branch of `nonempty_signedFiveAdicPacket_of_normalForm`, the theorem is applied with `g=w-v` to obtain

$$
(\operatorname{GN5}(w-v,v):\mathrm{ZMod}\ 25)=5.
$$

This is converted back to the natural-number congruence

$$
\operatorname{GN5}(w-v,v)\bmod 25=5,
$$

from which one gets that 5 divides the residual but 25 does not; consequently `padicValNat 5 (...) = 1`.

The dependency flow is

```text
5 ∣ g        5 ∤ y
  ↓            ↓ 0065
 g = 5k     y^4 = 1 + 5q  in ZMod 25
    \          /
     \        /
      expand GN5
         ↓
  GN5(g,y) = 5  in ZMod 25
         ↓
  mod 25 = 5
         ↓
  5 ∣ GN5, 25 ∤ GN5
         ↓
  v₅(GN5) = 1
```

## Direct dependencies

- `GN5` — 0006
- `fourth_power_zmod25_decomposition` — 0065
- `ZMod 25`
- `rcases` for extracting divisibility witnesses
- `push_cast`
- `rw`
- `ring_nf`
- `simp only`
- `decide` for facts such as `25 = 0` in `ZMod 25`

The essential mathematical dependencies are the polynomial definition of `GN5` and the fourth-power decomposition from 0065.

## Proof flow

1. Destructure `h5g : 5 ∣ g` to write `g = 5 * k`.
2. Apply 0065 to `y` and obtain `hq : (y : ZMod 25)^4 = 1 + 5 * q`.
3. Unfold `GN5`.
4. Use `push_cast` to move natural-number coefficients, products, and powers into the `ZMod 25` polynomial expression.
5. Rewrite $y^4$ using `hq`.
6. Normalize the polynomial with `ring_nf`.
7. Explicitly discharge the facts that `25,50,250,625` are zero in `ZMod 25` using `decide`, then simplify to the final value 5.

## Lean-specific processing

Mathematically one simply says that because `g` is divisible by 5, every high-order term containing `g` vanishes modulo 25. The current Lean proof makes this concrete by substituting `g=5*k` and reducing the relevant coefficients all the way to `25,50,250,625`.

`push_cast` turns the natural-number polynomial defining `GN5` into an expression in `ZMod 25`. `ring_nf` then performs polynomial normalization, while the final `simp only` removes the concrete coefficients that are zero modulo 25.

Facts such as `show (25 : ZMod 25) = 0 by decide` hard-code the modulus 25 directly into the proof script.

## Redundancy and duplication

The four explicit facts for `25,50,250,625` are mechanical instances of the same principle: every multiple of 25 is zero in `ZMod 25`.

The proof also fully unfolds `GN5` before normalization. It may be possible to use an existing decomposition theorem such as `GN5_eq_g_pow_four_add_five_mul` instead, making the separation between the `g`-part and the remaining `5y^4` term more mathematically visible.

On the other hand, the current proof is easy to audit because it works directly with the fixed polynomial and has few abstract dependencies.

## Optimization candidates

The first candidate is to replace the four concrete `show ... = 0 by decide` facts with a generic `ZMod` fact stating that multiples of 25 vanish modulo 25.

The second candidate is to rewrite with `GN5_eq_g_pow_four_add_five_mul`, substitute `g=5k`, and show structurally that only $5y^4$ survives modulo 25. This could reduce dependence on a full unfold of `GN5`.

A third possibility is to generalize the pattern to a prime $p$: if $p\mid g$, $p\nmid y$, and a fourth-power-like residual has a decomposition $y^{p-1}=1+pq$ modulo $p^2$, then the corresponding residual is $p$ modulo $p^2$. Because the coefficients of `GN5` are specific to exponent 5, however, such a generalization may be excessive here.

## Required Mathlib imports and import optimization candidates

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`, and its manifest lists `DkMath/FLT/Five/SignedFiveAdic.lean` among the ordered source modules.

For this lemma alone, at least `ZMod`, cast simplification (`push_cast`), ring normalization (`ring_nf`), and basic tactics (`simp`, `decide`) are needed. The split source file `DkMath/FLT/Five/SignedFiveAdic.lean` could not be fetched directly from the museum branch, so the exact minimal import list remains unverified and is therefore speculative.

Import optimization would require obtaining the split source imports and then checking, with a Lean build, whether `import Mathlib` can be reduced to the relevant `ZMod`, ring-tactic, and cast-tactic modules. No Lean build was run in this article.

## Comparator challenge suitability

This is a good candidate. The target is short, but there are several clearly distinct proof styles.

- Current: `rcases` + `unfold GN5` + `push_cast` + `ring_nf` + concrete `simp`
- Candidate A: structural proof via an existing `GN5` decomposition theorem
- Candidate B: proof emphasizing `ZMod` divisibility/characteristic APIs
- Candidate C: proof through a general modulo-$p^2$ helper lemma

Useful comparison criteria include not only line count, but also the amount of hard-coding of modulus 25, visibility of the mathematical structure, tactic dependence, generalizability, and import weight.

## Evidence and speculation

The theorem name, type, and complete proof body were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The same source also confirms that the later difference branch applies this theorem to `GN5 (w - v) v` and then converts the result through mod 25, divisibility by 5, nondivisibility by 25, and finally 5-adic valuation 1.

GitHub code search returned a transient upstream 502 during this run, and the split source `DkMath/FLT/Five/SignedFiveAdic.lean` returned 404 on the museum branch. Therefore the exact imports of the split source remain unverified.

The exact matching locations in the existing Japanese and English PDFs could not be verified during this run because of the GitHub search failure. No PDF page numbers or PDF-specific explanations have been guessed.

## Next theorem to read

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5
```

This article handles the residual in the difference orientation. The next article fixes the sum-orientation residual `SumGN5` to the same value 5 modulo 25, where the coprimality lemmas 0062–0063 and the fourth-power decomposition 0065 come together.

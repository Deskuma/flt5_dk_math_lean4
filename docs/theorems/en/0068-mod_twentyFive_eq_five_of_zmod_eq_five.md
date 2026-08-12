# 0068 — `mod_twentyFive_eq_five_of_zmod_eq_five`

## Lean type

```lean
private theorem mod_twentyFive_eq_five_of_zmod_eq_five
    {n : ℕ} (h : (n : ZMod 25) = 5) :
    n % 25 = 5 := by
  have hmod : n ≡ 5 [MOD 25] :=
    (ZMod.natCast_eq_natCast_iff n 5 25).mp (by simpa using h)
  simpa [Nat.ModEq] using hmod
```

This is a `private` declaration used inside the `SignedFiveAdic.lean` layer to convert an equality in `ZMod 25` back into a natural-number `% 25` equality.

## Mathematical statement

For a natural number `n`, if its image in `ZMod 25` is 5,

$$
(n:\mathrm{ZMod}\ 25)=5,
$$

then

$$
n\bmod25=5.
$$

Mathematically this merely rewrites the same congruence information in two representations. Equality in `ZMod 25` means

$$
n\equiv5\pmod{25},
$$

and since `5<25`, the standard residue on the right is exactly 5.

## Role in the full proof

Articles 0066 and 0067 establish, for the difference and sum residuals respectively,

$$
(residual:\mathrm{ZMod}\ 25)=5.
$$

The downstream proof, however, needs the natural-number form

$$
residual\bmod25=5,
$$

because it is convenient for extracting divisibility and non-divisibility facts. This lemma isolates that representation boundary in one place.

Inside `nonempty_signedFiveAdicPacket_of_normalForm`, the difference branch uses

```lean
have hmod : GN5 (w - v) v % 25 = 5 :=
  mod_twentyFive_eq_five_of_zmod_eq_five hcast
```

while the sum branch uses

```lean
have hmod : SumGN5 u v % 25 = 5 :=
  mod_twentyFive_eq_five_of_zmod_eq_five hcast
```

The resulting `hmod` is then converted into `n=5+25M`, from which `5∣n` and `25∤n` are obtained, leading to 5-adic valuation one.

The dependency flow is

```text
(residual : ZMod 25) = 5
             ↓
ZMod.natCast_eq_natCast_iff
             ↓
      residual ≡ 5 [MOD 25]
             ↓
          Nat.ModEq
             ↓
      residual % 25 = 5
             ↓
       n = 5 + 25M
             ↓
        5 ∣ n, 25 ∤ n
```

## Direct dependencies

- `ZMod.natCast_eq_natCast_iff`
- `Nat.ModEq`
- `simpa`

The lemma does not mathematically depend on the specific contents of 0066 or 0067; it is a general bridge for any natural number `n`. Articles 0066 and 0067 are the main producers of inputs for this bridge.

## Proof flow

1. Start from `h : (n : ZMod 25) = 5`.
2. Apply the forward direction of `ZMod.natCast_eq_natCast_iff n 5 25` to obtain `Nat.ModEq 25 n 5`, written as `n ≡ 5 [MOD 25]`.
3. Unfold `Nat.ModEq`, which turns the congruence into an equality of remainders.
4. `simpa [Nat.ModEq]` closes the goal `n % 25 = 5`.

## Lean-specific processing

No new arithmetic is proved here; the theorem converts between two Lean encodings of modular arithmetic.

`ZMod 25` is convenient for ring calculations. In contrast, `Nat.ModEq` and `%` are convenient for the later natural-number divisibility constructions. By making the conversion explicit, later code does not need to mix the `ZMod` and `Nat` APIs at every use site.

The small `by simpa using h` step normalizes the right-hand `5` as the relevant natural-number cast into `ZMod 25`.

## Redundancy and duplication

The proof is only two substantive lines and contains no significant duplication.

The intermediate proposition `hmod` is logically optional: the theorem could potentially be compressed into a single `simpa [Nat.ModEq]` around the relevant equivalence. The current form is nevertheless explanatory because it visibly separates

```text
ZMod equality → modular congruence → remainder equality.
```

## Optimization candidates

The first candidate is to see whether the proof can be compressed to a single `simpa [Nat.ModEq]` without making the cast direction obscure.

The second candidate is to use or define a general bridge of the form

```lean
(n : ZMod m) = r → n % m = r % m
```

and obtain this theorem as the specialization `m=25`, `r=5`. If Mathlib already exposes an equivalent theorem, this private lemma may be reducible to a short wrapper.

A third design option is to keep the downstream development in `Nat.ModEq` form instead of expanding to `%`. That would remove this particular representation step, but the current downstream lemmas directly consume remainder equalities, so it would require a broader refactor.

## Required Mathlib imports and import optimization candidates

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. This lemma itself mainly needs `ZMod`, natural-number modular congruence (`Nat.ModEq`), and ordinary simplification.

There is therefore substantial room to reduce imports toward the modules that provide `ZMod` and natural-number modular arithmetic. However, the exact imports of the split source file `SignedFiveAdic.lean` were not directly available from the museum branch in this run, so concrete minimal module names remain unverified and are stated only as a candidate.

No Lean build was performed in this run, so import minimization was not tested.

## Comparator challenge suitability

Suitable, though small. The interesting comparison is API design rather than mathematical difficulty.

- Current: `ZMod.natCast_eq_natCast_iff` followed by unfolding `Nat.ModEq`
- Candidate A: a more direct `ZMod` / remainder bridge from Mathlib
- Candidate B: a generalized modulus/residue helper
- Candidate C: keep downstream proofs in `Nat.ModEq` form and avoid `%` expansion

Useful comparison criteria are API clarity, cast stability, resistance to Mathlib changes, and generality rather than raw line count.

## Evidence and explicit uncertainty

The theorem name, type, and complete proof body were confirmed in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The same source also confirms that both the difference and sum branches call this lemma directly.

GitHub code search returned a transient upstream error during this run, so the already known standalone source was fetched directly instead. The exact corresponding pages in the existing Japanese and English PDFs were not confirmed, and no PDF-specific page numbers or claims are guessed here.

## Next theorem to read

```lean
private theorem eq_five_add_twentyFive_mul_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ∃ M : ℕ, n = 5 + 25 * M
```

Article 0068 provides the remainder equality; the next bridge turns it into the explicit arithmetic shape `n=5+25M`, which can be consumed directly by divisibility arguments.

# 0069 — `eq_five_add_twentyFive_mul_of_mod_eq_five`

## Lean type

```lean
private theorem eq_five_add_twentyFive_mul_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ∃ M : ℕ, n = 5 + 25 * M := by
  refine ⟨n / 25, ?_⟩
  have hsplit := Nat.mod_add_div n 25
  omega
```

This declaration is `private`. Inside `SignedFiveAdic.lean`, it converts the remainder statement `n % 25 = 5` into an explicit quotient-remainder decomposition that later divisibility arguments can consume directly.

## Mathematical statement

If a natural number `n` has remainder 5 modulo 25, then there exists a natural number `M` such that

$$
n=5+25M.
$$

This is simply the division algorithm

$$
n=(n\bmod25)+25\left\lfloor\frac{n}{25}\right\rfloor
$$

with `n % 25 = 5` substituted. The proof chooses

$$
M=n/25
$$

as the witness.

## Role in the whole proof

Article 0068 converts a residual equality in `ZMod 25` into

$$
residual\bmod25=5.
$$

Article 0069 turns that remainder equation into

$$
residual=5+25M.
$$

This explicit shape allows the following lemma `five_dvd_of_eq_five_add_twentyFive_mul` to construct a witness for `5 ∣ residual` directly. Both the difference and sum branches call this theorem immediately after obtaining `hmod`.

The dependency flow is

```text
(residual : ZMod 25) = 5
             ↓ 0068
      residual % 25 = 5
             ↓ 0069
      residual = 5 + 25*M
             ↓
          5 ∣ residual
```

At the same time the original `hmod` is retained for a separate proof that `25 ∤ residual`, after which the residual is shown to have 5-adic valuation exactly one.

## Direct dependencies

- `Nat.mod_add_div`
- natural-number division `/` and remainder `%`
- `omega`

The theorem does not call 0068 itself. It is a general arithmetic bridge whose input type is `n % 25 = 5`; 0068 supplies that input at the principal consumer sites.

## Proof flow

1. Choose `n / 25` as the witness for `M`.
2. Obtain the standard quotient-remainder decomposition of `n` from `Nat.mod_add_div n 25`.
3. Give that decomposition together with `hmod : n % 25 = 5` to `omega`.
4. Derive `n = 5 + 25 * (n / 25)` and close the existential goal.

## Lean-specific processing

The equality produced by `Nat.mod_add_div` need not have exactly the same orientation or term ordering as the human-readable form `n = n % 25 + 25 * (n / 25)`. The current proof stores it as `hsplit` and lets `omega` handle the routine rearrangement.

`refine ⟨n / 25, ?_⟩` fixes the existential witness first, so the constructive content of the proof remains explicit: `M` is not an abstract existence witness but the standard quotient.

## Redundancy and duplication

The proof is extremely short and has essentially no logical duplication. The local name `hsplit` is used only once, however, so it could potentially be inlined immediately before `omega`.

The constants 25 and 5 are also specialized. If analogous lemmas are needed for other moduli and residues, a common theorem of the form

```lean
n % m = r → ∃ q, n = r + m * q
```

would avoid duplication.

## Optimization candidates

The first candidate is to replace part of the `omega` work with a `calc` chain based on `Nat.mod_add_div`, making the division-algorithm data flow more explicit.

The second candidate is to generalize the theorem over the modulus and residue, then recover this result by specialization. Nothing in the mathematics is specific to 25 and 5.

The third candidate is to combine this bridge with `five_dvd_of_eq_five_add_twentyFive_mul` and derive `5 ∣ n` directly from `n % 25 = 5`. The current intermediate equation nevertheless has pedagogical and auditing value because it exposes the precise 5-adic shape.

## Required Mathlib imports and import optimization candidates

The generated `Flt5DkMath/FLT5StandAlone.lean` uses `import Mathlib`. This theorem itself mainly requires natural-number division/remainder APIs, `Nat.mod_add_div`, and the `omega` tactic.

A plausible minimal import set would therefore consist of the Nat division/modulus API plus the module providing `omega`, such as `Mathlib.Tactic.Omega`. The exact imports of the split source file `DkMath/FLT/Five/SignedFiveAdic.lean` were not directly verified on this branch, so concrete minimal-import names remain an explicit inference rather than a confirmed fact.

No Lean build was run in this article, so import minimization has not been tested.

## Comparator challenge suitability

Yes. This is a small theorem with clear proof-style alternatives.

- Current: witness `n / 25` + `Nat.mod_add_div` + `omega`
- Candidate A: a `calc` / rewrite-oriented tactic-light proof
- Candidate B: specialization of a general modulus/residue helper
- Candidate C: derive `5 ∣ n` directly and omit the intermediate existential decomposition

Useful comparison criteria are not merely line count, but visibility of the division algorithm, dependence on `omega`, generality, and clarity at downstream consumer sites.

## Evidence and explicit uncertainty

The theorem name, type, and complete proof body were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. The same source shows both the difference and sum branches using this lemma immediately after 0068 and passing the resulting shape to `five_dvd_of_eq_five_add_twentyFive_mul`.

GitHub code search returned a transient upstream error during this run, so the already known standalone source was fetched directly instead. No concrete matching page in the existing Japanese or English PDFs was verified, and no PDF-specific page number or narrative detail has been guessed.

## Next theorem to read

```lean
private theorem five_dvd_of_eq_five_add_twentyFive_mul
    {n M : ℕ} (h : n = 5 + 25 * M) :
    5 ∣ n
```

This is the next bridge: it extracts an explicit factor of 5 from the shape produced by 0069.

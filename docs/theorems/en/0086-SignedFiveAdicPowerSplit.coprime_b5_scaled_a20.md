# 0086 — `SignedFiveAdicPowerSplit.coprime_b5_scaled_a20`

## Lean type

```lean
theorem SignedFiveAdicPowerSplit.coprime_b5_scaled_a20
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (s.b ^ 5) (5 ^ 15 * s.a ^ 20) :=
  s.coprime_scaled_a20_b5.symm
```

## Mathematical statement

This is the companion lemma obtained by reversing the orientation of the result proved in 0085,

$$
\gcd(5^{15}a^{20},b^5)=1,
$$

so that we have

$$
\gcd(b^5,5^{15}a^{20})=1.
$$

Its mathematical content is identical to 0085. It introduces no new number-theoretic information; it uses only the symmetry of coprimality in order to present the proposition in the argument order required by later theorems.

## Role in the overall proof

The role of this theorem is not arithmetic discovery but API-orientation adjustment.

0085 provides coprimality in the order

$$
5^{15}a^{20}
\quad\text{and}\quad
b^5,
$$

whereas later golden-order code has sites where $b^5$ is treated as the first factor. In the standalone source on the target branch, this theorem is later consumed as

```lean
have hab := p.exceptional.powerSplit.coprime_b5_scaled_a20
have habs : Nat.Coprime (p.exceptional.powerSplit.b ^ 5)
    (5 ^ 15 * p.exceptional.powerSplit.a ^ 20) := hab
```

and is then passed directly to `Nat.eq_one_of_dvd_coprimes`.

Thus the proof flow is

$$
\gcd(5^{15}a^{20},b^5)=1
\Longrightarrow
\gcd(b^5,5^{15}a^{20})=1
\Longrightarrow
\text{the orientation required by the downstream API}.
$$

## Direct definitions and lemmas used

- `SignedFiveAdicPowerSplit`
- `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5` (0085)
- `Nat.Coprime.symm`

This theorem does not directly use `s.five_not_dvd_b`, `s.coprime_a_b`, the primality of 5, or the power-preservation lemmas for coprimality. All of that arithmetic work has already been encapsulated by 0085.

## Proof flow

The proof has exactly one step.

1. From 0085 obtain

$$
\operatorname{Coprime}(5^{15}a^{20},b^5).
$$

2. Apply `Nat.Coprime.symm` to obtain

$$
\operatorname{Coprime}(b^5,5^{15}a^{20}).
$$

In Lean this is compressed to the single expression

```lean
s.coprime_scaled_a20_b5.symm
```

## Lean-specific processing

`Nat.Coprime` is a two-argument proposition. Although it is symmetric mathematically, the Lean expressions

```lean
Nat.Coprime A B
```

and

```lean
Nat.Coprime B A
```

are distinct types. If a downstream lemma expects the latter orientation, the former cannot simply be supplied unchanged.

The `.symm` method therefore acts as an orientation adapter.

In

```lean
s.coprime_scaled_a20_b5.symm
```

Lean infers $A=5^{15}a^{20}$ and $B=b^5$ from the receiver `s.coprime_scaled_a20_b5`, and the symmetric result matches the goal directly.

No `by` block, `exact`, or intermediate `have` is needed.

## Redundancy and duplication

Mathematically, this theorem completely duplicates 0085. In isolation it could be removed, with call sites writing

```lean
s.coprime_scaled_a20_b5.symm
```

directly.

However, the later source uses `coprime_b5_scaled_a20` as a named API whose orientation itself is meaningful. Therefore this one-line theorem is duplicated mathematics, but not necessarily duplicated API surface.

In particular, giving the reverse orientation a stable companion name can make downstream proof scripts easier to read and search than repeatedly applying `.symm` to a long qualified theorem name.

## Optimization candidates

There are three natural choices.

1. Keep the current design.
   - Export both forward and reverse orientations as explicit companion theorems.
2. Remove this theorem.
   - Use `s.coprime_scaled_a20_b5.symm` directly at each call site.
3. Standardize orientation in downstream APIs.
   - If the project can enforce one factor order for coprimality statements, some companion theorems may become unnecessary.

Because this declaration is actually used downstream as a named API, retaining it has a clear justification. The optimization question is not proof length but whether the project-wide orientation convention is coherent.

## Required Mathlib imports and import optimization

The target branch's `Flt5DkMath/FLT5StandAlone.lean` is built with `import Mathlib`, and the manifest places this declaration in `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`.

The only Mathlib functionality used directly by this theorem is `Nat.Coprime.symm`, so `import Mathlib` is obviously much broader than necessary when considering this declaration alone.

However, the actual source module also needs the `SignedFiveAdicPowerSplit` structure and preceding theorems. Therefore minimal imports should be determined for the whole module dependency graph rather than for this one declaration in isolation. This run does not verify the split module's import list with a Lean build, so no exact minimal import module is asserted.

## Comparator challenge suitability

Possible, but too small as a proof-search challenge. It is better suited to an API-design comparator.

Reasonable variants are:

1. The current named reverse companion theorem.
2. Direct `.symm` at every call site.
3. A project-wide convention fixing the orientation of coprimality factors.

The useful metrics are not line count but downstream readability, searchability, discoverability through completion, and refactor stability.

## PDF correspondence

Existing Japanese and English PDFs are treated as narrative evidence, but this theorem is a pure one-line symmetry adapter for 0085, and no one-to-one PDF page or section for this declaration was confirmed in this run.

GitHub code search also returned a transient 502 upstream error, so the PDF location is not filled in by conjecture. The formal authority is the actual Lean declaration in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next theorem to read

The next declaration in source order is

```lean
private theorem nonempty_signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nonempty (SignedFiveAdicPowerSplit u v w) := by
  let c := p.carrier / 5
  let r := p.residual / 5
  let d := p.distinguished / 5
  ...
```

0083 defined the power-split record, and 0084–0086 prepared its downstream properties. The next private theorem finally constructs actual `SignedFiveAdicPowerSplit` data from a `SignedFiveAdicPacket`.

The proof therefore moves to

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit}),
$$

marking the transition from structure/API declarations to the constructor layer.
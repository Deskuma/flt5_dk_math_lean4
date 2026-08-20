# 0166 — `goldenConj_phi`

## Lean type

```lean
/-- Conjugation sends `φ` to `1-φ`. -/
@[simp] theorem goldenConj_phi :
    goldenConj goldenPhi = goldenSub goldenOne goldenPhi := by
  decide
```

This is a `theorem`. It explicitly states, on the raw-operation API, that the conjugation `goldenConj` sends the generator `goldenPhi` to `1-φ`.

## Mathematical statement and meaning of the declaration

Read an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

Declaration 0163 defines

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

which is the coordinate transformation

$$
(a,b)\mapsto(a+b,-b).
$$

Declaration 0161 defines

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩,
```

so conjugating the generator gives

$$
(0,1)\mapsto(1,-1),
$$

that is,

$$
\overline{\varphi}=1-\varphi.
$$

The right-hand side `goldenSub goldenOne goldenPhi` also has coordinates `(1,-1)`. Thus the theorem exposes the nontrivial quadratic conjugation as a concrete API identity.

## Role in the overall proof

Declaration 0165 `golden_phi_sq` exposes the generator relation

$$
\varphi^2=\varphi+1.
$$

The present theorem supplies the corresponding quadratic symmetry: the second root of the polynomial is `1-φ`, and the nontrivial conjugation exchanges the two roots.

This becomes foundational for later declarations such as `goldenConj_invol`, `goldenConj_mul`, `goldenNorm_conj`, and `golden_mul_conj`. Those results connect conjugation to the norm

$$
N(x)=x\overline{x},
$$

and then to units, divisibility, and the Euclidean-domain arithmetic used later in the FLT5 development.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- `goldenPhi`
- `goldenOne`
- `goldenConj`
- `goldenSub`

Conceptually,

$$
\texttt{goldenPhi},\ \texttt{goldenConj},\ \texttt{goldenOne},\ \texttt{goldenSub}
\longrightarrow
\texttt{goldenConj\_phi}.
$$

## Proof / construction flow

The proof is simply

```lean
by
  decide
```

Both sides evaluate to closed concrete `GoldenInt` values. The left side is

$$
goldenConj(0,1)=(1,-1),
$$

while the right side is

$$
goldenOne-goldenPhi=(1,0)-(0,1)=(1,-1).
$$

Equality on `GoldenInt` is decidable, so `decide` evaluates the coordinate computation and closes the proof.

## Lean-specific processing

`decide` proves a proposition through its `Decidable` instance. Here this is effectively a closed integer-coordinate computation rather than proof search.

The theorem is also marked `@[simp]`. Hence simp may normalize

```lean
goldenConj goldenPhi
```

to

```lean
goldenSub goldenOne goldenPhi,
```

which is exactly the rewrite rule

$$
\varphi\mapsto1-\varphi.
$$

Since `golden_sub_eq` is already available, standard notation can subsequently normalize the right-hand side toward `1 - goldenPhi` as well.

## Redundancy and duplication

The theorem is computationally derivable by unfolding `goldenConj` and `goldenPhi`, so it republishes information already present in the definitions.

That duplication is useful. The action of conjugation on the generator is central mathematical API information for a quadratic order. A named theorem avoids repeated coordinate unfolding and separates the internal coordinate implementation from the external algebraic interface.

## Optimization candidates

Several proof and API choices are worth comparing.

1. Keep the current `by decide` and emphasize the closed computation.
2. Check whether `rfl` closes the theorem and, if so, use it to emphasize definitional equality.
3. Use `norm_num [goldenConj, goldenPhi, goldenSub, goldenOne, goldenAdd, goldenNeg]` to expose the computation path explicitly.
4. Add a standard-notation theorem `goldenConj goldenPhi = 1 - goldenPhi` for downstream readability.

No Lean build is performed in this museum pass, so option 2 remains unverified.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself directly needs only the upstream `GoldenInt` definitions, integer arithmetic, decidable equality, and `decide`.

It is therefore unlikely that all of `Mathlib` is required solely for this theorem. The true minimal import set is governed by the complete `GoldenOrder` module, which also uses algebraic typeclasses, ring tactics, and `Zsqrtd`. Since no build is run here, the exact minimal import set remains unverified.

## Comparator challenge suitability

Yes. A compact comparison can test:

- `by decide`
- whether `by rfl` is accepted
- `by norm_num [...]`
- `ext <;> norm_num [...]`

Useful criteria are proof-term simplicity, robustness under definition changes, error-message quality, computational transparency, and import dependencies.

The API design itself can also compare the raw theorem

```lean
goldenConj goldenPhi = goldenSub goldenOne goldenPhi
```

with the standard-notation theorem

```lean
goldenConj goldenPhi = 1 - goldenPhi.
```

The question is which should be the primary simp rule and which should remain an implementation bridge.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The target branch also contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

On the next run, the declaration immediately following `goldenConj_phi` should be re-read from the repository source before selecting the next museum entry. Nearby declarations include norm and conjugation lemmas such as `goldenNorm_phi` and `goldenConj_invol`, so the source order should be verified rather than inferred from memory.
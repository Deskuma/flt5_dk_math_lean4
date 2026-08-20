# 0171 — `goldenConj_mul`

## Lean type

```lean
/-- Conjugation respects multiplication. -/
theorem goldenConj_mul (x y : GoldenInt) :
    goldenConj (goldenMul x y) =
      goldenMul (goldenConj x) (goldenConj y) := by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

This is a `theorem` stating that the golden-integer conjugation `goldenConj` preserves the multiplication `goldenMul`.

## Mathematical statement and meaning of the declaration

Read elements of `GoldenInt` as

$$
x=a+b\varphi,\qquad y=c+d\varphi.
$$

Upstream, multiplication reduced by

$$
\varphi^2=\varphi+1
$$

is implemented by

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd),
$$

while conjugation is implemented by

$$
(a,b)\mapsto(a+b,-b),
$$

i.e. by the nontrivial quadratic action $\varphi\mapsto1-\varphi$.

The theorem asserts

$$
\overline{xy}=\overline{x}\,\overline{y}.
$$

Thus conjugation is not merely an involution on the underlying set: it is compatible with the multiplicative structure of the quadratic order.

To see the coordinate identity explicitly, write $xy=(A,B)$ with

$$
A=ac+bd,\qquad B=ad+bc+bd.
$$

The left-hand side then has coordinates

$$
(A+B,-B)=(ac+ad+bc+2bd,\ -ad-bc-bd).
$$

On the other hand,

$$
\overline{x}=(a+b,-b),\qquad \overline{y}=(c+d,-d),
$$

and multiplying these two conjugates gives the same coordinate pair.

## Role in the overall proof

Declaration 0170 `goldenConj_invol` established

$$
\overline{\overline{x}}=x,
$$

so conjugation is self-inverse. The present theorem immediately adds

$$
\overline{xy}=\overline{x}\,\overline{y}.
$$

Together these facts make `goldenConj` visibly behave as a multiplicative self-symmetry of the golden quadratic order. The following results develop its interaction with the norm, including `goldenNorm_mul`, `goldenNorm_conj`, and `golden_mul_conj`.

The theorem is also used directly later in the generated `GoldenDivisibility` section. In particular,

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]
```

uses `goldenConj_mul` as the multiplicative induction step. Thus 0171 is not merely descriptive infrastructure; it is an operational API theorem for later conjugation of powers, including fifth powers.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- `goldenMul`
- 0163 `goldenConj`
- `GoldenInt.ext`
- the `fst` and `snd` coordinates of `GoldenInt`
- simplifier support and the `ring` tactic over the integer ring

Although 0170 `goldenConj_invol` is the immediately preceding structural fact, this proof does not use it. Both sides are proved equal by direct coordinate expansion.

Conceptually,

$$
\texttt{goldenMul},\ \texttt{goldenConj},\ \texttt{GoldenInt.ext}
\longrightarrow
\texttt{goldenConj_mul}.
$$

## Proof / construction flow

The entire proof is

```lean
by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

It has three stages.

1. `ext` reduces equality of `GoldenInt` structures to equality of their two integer coordinates.
2. `simp [goldenConj, goldenMul]` unfolds conjugation and multiplication into explicit coordinate expressions.
3. `ring` normalizes the remaining polynomial identities over `ℤ`.

The proof flow is therefore

```text
goldenConj (goldenMul x y)
  = goldenMul (goldenConj x) (goldenConj y)
→ split into fst / snd goals with GoldenInt.ext
→ unfold goldenConj and goldenMul
→ polynomial equalities over ℤ
→ close by ring normalization
```

## Lean-specific processing

`ext` uses the registered extensionality theorem `GoldenInt.ext`, avoiding manual `cases x` and `cases y` decomposition.

The `<;>` combinator applies the following tactic to every goal produced by the preceding tactic. Here both coordinate goals receive the same

```lean
simp [goldenConj, goldenMul]
```

and then the same `ring` normalization.

The simplifier performs definitional unfolding and elementary integer simplification; `ring` handles the genuinely nontrivial polynomial rearrangement. `ring` is a better fit than `nlinarith` here because there are no inequalities or hypotheses to exploit: the goals are pure commutative-ring identities.

The statement deliberately uses the raw coordinate API `goldenMul` rather than standard `*` notation. Declaration 0159 `golden_mul_eq` connects the two presentations, but this theorem itself records multiplicative preservation at the explicit coordinate layer.

## Redundancy and duplication

The proof expands both `goldenConj` and `goldenMul` completely, so mathematically it verifies a standard homomorphism law by coordinate algebra.

Later, in the generated `GoldenDivisibility` section, the source separately proves

- `goldenConj_add`
- `goldenConj_neg`
- `goldenConj_sub`
- `goldenConj_pow`

so the structural laws of conjugation are distributed across several named theorems.

This is clear and auditable for an explicit coordinate API, but from the abstract algebra viewpoint the additive law, multiplicative law, and preservation of `1` could be bundled into a `RingHom`; together with 0170 involutivity, conjugation could eventually be presented as a `RingEquiv`.

However, `goldenConj_add` is currently located in a later module, so constructing a complete ring equivalence at declaration 0171 would require reordering declarations or reorganizing module boundaries.

## Optimization candidates

Possible improvements include:

1. retain the current short coordinate proof;
2. restate or supplement the theorem using standard notation, `goldenConj (x * y) = goldenConj x * goldenConj y`;
3. keep both raw and standard-notation bridge theorems;
4. move additive preservation into the same module and bundle conjugation as `GoldenInt →+* GoldenInt`;
5. combine the homomorphism laws with 0170 to construct a ring equivalence `GoldenInt ≃+* GoldenInt`;
6. abstract conjugation for a general quadratic order and recover the golden case by specialization.

The local proof is already close to minimal. The larger optimization opportunity is structural: bundle the conjugation laws so later results such as `goldenConj_pow` can follow from generic algebra APIs instead of dedicated inductions.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. In isolation, this theorem requires the upstream `GoldenInt`, `goldenMul`, `goldenConj`, and `GoldenInt.ext` definitions, together with integer simplification and the tactic infrastructure providing `ring`.

Therefore importing all of Mathlib is likely excessive for this theorem alone. At module scope, however, `GoldenOrder` also uses `Zsqrtd`, `CommRing`, `omega`, `norm_num`, and other facilities, so the true minimal import set should be determined by an actual module-level Lean build.

No exact reduced import list is claimed here because this museum pass does not run Lean builds.

## Comparator challenge suitability

Yes. This theorem is a clean comparison point between explicit coordinate proofs and bundled algebra structure.

Useful variants are:

- the current raw coordinate proof;
- a theorem stated with standard `*` notation;
- obtaining the result as `map_mul` from a bundled `RingHom`;
- obtaining it from a bundled `RingEquiv`;
- deriving it from a generic quadratic-order conjugation construction.

Comparison criteria include proof-term size, amount of definitional unfolding, simp normal forms, simplification of downstream results such as `goldenConj_pow`, dependency-cycle risk, reuse for general quadratic orders, and preservation of coordinate transparency.

This makes a good benchmark for the trade-off between many tiny transparent coordinate lemmas and an earlier investment in abstract homomorphism infrastructure.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following 0171 in the Lean source is

```lean
/-- The structure norm is the previously exposed binary golden norm. -/
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

Therefore the next museum entry is **0172 `goldenNorm_eq_GoldenNorm`**. After establishing multiplicative preservation of conjugation, the development next connects the structured norm `goldenNorm` to the earlier two-variable quadratic form `GoldenNorm`, bridging the newer `GoldenInt` structure API back to the pre-existing norm API.
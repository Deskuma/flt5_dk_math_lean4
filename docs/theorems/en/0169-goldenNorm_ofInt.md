# 0169 — `goldenNorm_ofInt`

## Lean type

```lean
/-- The norm of an embedded integer is its square. -/
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

This is a `theorem` stating that when an integer `a : ℤ` is embedded into the golden integer order by `goldenOfInt`, its golden norm is exactly the ordinary square `a ^ 2`. It is marked `@[simp]` so this reduction is available automatically to the simplifier.

## Mathematical statement and meaning of the declaration

Declaration 0162 defines the integer embedding by

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

and 0164 defines the golden norm by

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

Reading a golden integer as $x=a+b\varphi$, the norm is

$$
N(a+b\varphi)=a^2+ab-b^2.
$$

For the embedded integer `goldenOfInt a`, the second coordinate is $b=0$, hence

$$
N(a)=a^2+a\cdot0-0^2=a^2.
$$

Thus the theorem records that the quadratic norm on the golden order restricts to ordinary squaring on the embedded integer axis.

## Role in the overall proof

Declaration 0168 `goldenConj_ofInt` established that conjugation fixes embedded integers:

$$
\overline{a}=a.
$$

The present theorem immediately complements that fact by recording

$$
N(a)=a^2.
$$

Keeping in mind the standard quadratic-order relation

$$
N(x)=x\overline{x},
$$

this is exactly what should happen on the integer axis, because conjugation is the identity there. However, this theorem occurs before the later theorem connecting multiplication with conjugation, so its Lean proof does not derive the result abstractly from $x\overline{x}$; it simplifies the explicit coordinate norm directly.

In the generated source inspected for this entry, no later explicit use of the name `goldenNorm_ofInt` was identified. It is therefore safest to view its present role as part of the public simp API and as a named foundational fact in the conjugation-and-norm layer.

## Direct dependencies

The direct dependencies are:

- `GoldenInt`
- 0162 `goldenOfInt`
- 0164 `goldenNorm`
- basic `simp` lemmas for zero, multiplication, subtraction, and powers in `ℤ`

Declaration 0168 `goldenConj_ofInt` is mathematically adjacent but is not used by the Lean proof. Likewise, `goldenConj` and the later multiplication-by-conjugate theorem are not direct dependencies.

Conceptually, the dependency chain is

$$
\texttt{goldenOfInt},\ \texttt{goldenNorm}
\longrightarrow
\texttt{goldenNorm_ofInt}.
$$

## Proof / construction flow

The proof is one line:

```lean
by
  simp [goldenNorm, goldenOfInt]
```

After unfolding `goldenOfInt a` to `⟨a,0⟩` and expanding `goldenNorm`, the goal becomes conceptually

$$
a^2+a\cdot0-0^2=a^2.
$$

The simplifier then removes the zero terms using

$$
a\cdot0=0,\qquad 0^2=0,\qquad a^2+0-0=a^2.
$$

The proof flow is therefore

```text
goldenNorm (goldenOfInt a)
→ unfold the embedded integer coordinates
→ unfold the quadratic norm
→ simplify the zero terms in ℤ
→ a^2
```

and is completely transparent at the coordinate level.

## Lean-specific processing

No `ext` step is needed here because the conclusion is an equality in `ℤ`, not an equality of `GoldenInt` structures. Once `goldenNorm` is unfolded, only ordinary integer arithmetic remains.

The `@[simp]` attribute supplies the normalization

```lean
goldenNorm (goldenOfInt a)
```

to

```lean
a ^ 2
```

for downstream proofs. This is a natural direction: a specialized golden-order expression is reduced to standard integer arithmetic.

The proof itself needs only `simp [goldenNorm, goldenOfInt]`; tactics such as `ring`, `norm_num`, or `omega` are unnecessary.

## Redundancy and duplication

The theorem is completely determined by the definitions of `goldenNorm` and `goldenOfInt`, so it adds no new mathematical content. Nevertheless, the identity

$$
N(a)=a^2
$$

is a basic quadratic-order API fact and is useful as a named `@[simp]` theorem.

Together with 0168 `goldenConj_ofInt`, it gives the two basic integer-axis laws

$$
\overline{a}=a,\qquad N(a)=a^2.
$$

If conjugation were later bundled as a ring automorphism and norm were exposed abstractly through multiplication by conjugation, both results could potentially be derived from generic algebraic laws.

There is also API-level overlap between `goldenOfInt a` and the standard cast `(a : GoldenInt)`, since the upstream `intCast` uses the same coordinate rule. A bridge theorem `goldenOfInt a = (a : GoldenInt)` or a standard-cast version of this norm theorem could make downstream code more Mathlib-oriented.

## Optimization candidates

Possible alternatives are:

1. retain the current `simp [goldenNorm, goldenOfInt]` proof;
2. check by Lean build whether `rfl` alone closes the theorem;
3. compare with a `norm_num [goldenNorm, goldenOfInt]` proof;
4. first bridge `goldenOfInt a` to `(a : GoldenInt)` and make the standard-cast norm theorem the primary API;
5. eventually bundle conjugation as a ring automorphism and expose norm through a more generic quadratic-order abstraction.

Option 2 is unverified because this museum pass does not run a Lean build. The current proof is already short and explanatory, so there is little local pressure to change it.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This theorem itself primarily needs the upstream definitions `GoldenInt`, `goldenOfInt`, and `goldenNorm`, together with elementary integer operations and simplifier infrastructure.

Therefore importing all of Mathlib is likely excessive for this theorem in isolation. The full `GoldenOrder` module, however, also uses `CommRing`, `Zsqrtd`, `ring`, `omega`, `norm_num`, and other infrastructure, so the actual minimal import set must be tested at module scope. No exact reduced import set is claimed here because no Lean build is performed in this museum pass.

## Comparator challenge suitability

Yes. This is a small definitional arithmetic theorem for which proof style and API design can be compared cleanly.

Useful variants include:

- the current `simp [goldenNorm, goldenOfInt]` proof;
- `rfl`, if definitional reduction is sufficient;
- a theorem stated using the standard cast `(a : GoldenInt)`;
- a generic derivation from bundled conjugation / norm infrastructure.

Comparison criteria include proof-term size, robustness under definition changes, simp normal forms, compatibility with standard Mathlib APIs, import requirements, and generalizability.

In particular, it provides a compact comparison between the transparency of explicit coordinates and the abstraction of a reusable quadratic-order interface.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The target branch contains both `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not directly identified in this pass, so no page number is inferred.

## Next declaration to read

The declaration immediately following this theorem in the Lean source is

```lean
/-- Conjugation is an involution. -/
theorem goldenConj_invol (x : GoldenInt) :
    goldenConj (goldenConj x) = x := by
  ext <;> simp [goldenConj]
```

Therefore the next museum entry is **0170 `goldenConj_invol`**. After recording the action of conjugation on the generator and its fixed integer axis, the development now proves the global quadratic symmetry

$$
\overline{\overline{x}}=x
$$

for every `GoldenInt`.
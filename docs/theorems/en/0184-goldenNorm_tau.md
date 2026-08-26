# 0184 — `goldenNorm_tau`

## Lean type

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

This is a `theorem` establishing that the distinguished ramifier `goldenTau`, defined in 0178, has golden norm `5`.

## Mathematical statement

The relevant definitions are

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩

def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

Thus, for

$$
\tau=2+\varphi,
$$

we have

$$
N(\tau)=N(2+\varphi)=2^2+2\cdot1-1^2=4+2-1=5.
$$

Declaration 0183 already established

$$
\tau=\varphi\sqrt5.
$$

The earlier development also proves

$$
N(\varphi)=-1,
\qquad
N(\sqrt5)=-5,
\qquad
N(xy)=N(x)N(y),
$$

so structurally one may also read this theorem as

$$
N(\tau)=N(\varphi)N(\sqrt5)=(-1)(-5)=5.
$$

## Role in the full proof

Declarations 0177–0184 organize the concrete elements carrying ramification above five inside `GoldenInt`.

- `goldenSqrtFive = 2φ - 1` has square `5` and norm `-5`.
- `goldenTau = 2 + φ` is equal to `φ * goldenSqrtFive`.
- The present theorem establishes that `goldenTau` has positive norm `5`.

This promotes `goldenTau` from merely a convenient coordinate representative `⟨2,1⟩` to an explicit **norm-five ramifier**.

The immediately following theorem

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

uses `goldenNorm_tau` directly to obtain

$$
\tau\overline{\tau}=5.
$$

After that, `exists_goldenTau_factor_of_five_dvd` extracts an actual `goldenTau` factor from the integer divisibility condition `5 ∣ 2*M+N`. Thus this theorem is the numeric certificate immediately preceding the bridge from ordinary divisibility by five to an explicit ramified factor in the golden order.

## Direct dependencies

The actual Lean proof directly depends mainly on:

- 0164 `goldenNorm`
- 0178 `goldenTau`
- `norm_num`

The current proof does not use 0183 `goldenTau_eq_phi_mul_sqrtFive`, 0167 `goldenNorm_phi`, 0182 `goldenNorm_sqrtFive`, or 0174 `goldenNorm_mul`. Those declarations provide the mathematical provenance of the result rather than its direct implementation dependencies.

Implementation-wise, the dependency chain is

$$
\texttt{goldenNorm},\ \texttt{goldenTau}
\longrightarrow
\texttt{goldenNorm_tau}.
$$

A structural derivation would instead use

$$
\texttt{goldenTau\_eq\_phi\_mul\_sqrtFive},
\ \texttt{goldenNorm\_mul},
\ \texttt{goldenNorm\_phi},
\ \texttt{goldenNorm\_sqrtFive}
\longrightarrow
\texttt{goldenNorm_tau}.
$$

## Proof flow

The current proof is one line:

```lean
by
  norm_num [goldenNorm, goldenTau]
```

1. Unfold `goldenTau` to `⟨2,1⟩`.
2. Unfold `goldenNorm` to its quadratic form.
3. Reduce the goal to the integer calculation

$$
2^2+2\cdot1-1^2=5.
$$

4. Let `norm_num` normalize and close the concrete arithmetic expression.

No abstract ring or ramification theorem is needed; the proof is a closed coordinate calculation.

## Lean-specific processing

In `norm_num [goldenNorm, goldenTau]`, the listed definitions are unfolded in simp style, after which `norm_num` normalizes integer powers, products, additions, and subtraction.

Because the theorem is a closed proposition with no variables, a proof using `decide` is also likely possible. It may even reduce to `rfl` if kernel reduction alone normalizes the complete integer expression. Neither alternative is verified here because this museum pass does not run a Lean build.

A more structural proof could conceptually look like

```lean
rw [goldenTau_eq_phi_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_phi, goldenNorm_sqrtFive]
norm_num
```

although the exact rewrite shape is unverified here, in particular because `goldenNorm_mul` is stated using raw `goldenMul`.

## Redundancy and duplication

The value `N(τ)=5` can be obtained along two routes.

1. Directly substitute the coordinate value `τ = ⟨2,1⟩` into the norm.
2. Use `τ=φ√5` together with multiplicativity of the norm.

The source chooses route 1, so it does not reuse information already available from 0183, 0167, 0182, and 0174. In that sense there is mathematical duplication.

The direct coordinate proof, however, has a shallower dependency graph and is very robust as long as the chosen coordinate representative is unchanged. The structural proof better explains why the sign is `+5`.

The next theorem `golden_tau_mul_conj` is almost entirely the composition of `golden_mul_conj` with the present result, so keeping `goldenNorm_tau` as a named theorem provides a useful API boundary.

## Optimization candidates

Four approaches are worth considering.

1. **Keep the current direct coordinate proof**
   - shortest and locally self-contained;
   - consistent with the explicit coordinate model.

2. **Replace it with a structural proof**
   - reuse `τ=φ√5`, norm multiplicativity, and the two known norms;
   - makes the mathematical provenance more visible.

3. **Keep both viewpoints**
   - preserve the direct theorem as a coordinate certificate;
   - document or add a separate structural derivation.

4. **Bundle the ramified-element API**
   - store an `element : GoldenInt` together with `norm_eq_five`, conjugate-product facts, and factor-extraction properties;
   - downstream exceptional-branch code could then carry the meaning “norm-five ramifier” as structure rather than convention.

At the present scale the theorem is small enough that the one-line proof remains attractive. Bundling becomes more compelling only if the ramification API continues to grow.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The theorem itself needs only a small surface:

- `GoldenInt`
- `goldenNorm`
- `goldenTau`
- integer arithmetic
- the `norm_num` tactic

No advanced analytic or number-theoretic API is invoked directly.

A structural proof would additionally depend on `goldenTau_eq_phi_mul_sqrtFive`, `goldenNorm_mul`, `goldenNorm_phi`, and `goldenNorm_sqrtFive`, all of which are upstream declarations in the same `GoldenOrder` module.

Because no Lean build is run in this museum pass, the exact minimal Mathlib import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The theorem provides a clean comparison of proof styles.

Possible contestants are:

- A: current `norm_num [goldenNorm, goldenTau]`
- B: closed equality via `decide`
- C: explicit coordinate proof
- D: structural proof using `τ=φ√5` and norm multiplicativity

Useful metrics include:

- proof-term size
- shallowness of direct dependencies
- visibility of mathematical provenance
- robustness under upstream definition changes
- tactic dependence
- semantic consistency with the subsequent ramification theorems

The comparison between A and D is especially useful as a small test of “computational certificate” versus “structural proof” style.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on `docs/flt5-theorem-museum-v2`. The source contains the sequence

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide

theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]

theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

The branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

that is, **0185 `golden_tau_mul_conj`**.

Now that 0184 establishes

$$
N(\tau)=5,
$$

0185 specializes the general identity

$$
x\overline{x}=N(x)
$$

to `x=τ`, yielding

$$
\tau\overline{\tau}=5
$$

as an equality internal to the golden order. This is the final bridge before the explicit factor-extraction theorem.
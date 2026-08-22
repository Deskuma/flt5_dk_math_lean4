# 0186 — `exists_goldenTau_factor_of_five_dvd`

## Lean type

```lean
theorem exists_goldenTau_factor_of_five_dvd
    {M N : ℤ} (h : (5 : ℤ) ∣ 2 * M + N) :
    ∃ k : ℤ, ∃ beta : GoldenInt,
      2 * M + N = 5 * k ∧
      beta = ⟨M - k, 2 * k - M⟩ ∧
      (⟨M, N⟩ : GoldenInt) = goldenMul goldenTau beta := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ⟨M - k, 2 * k - M⟩, hk, rfl, ?_⟩
  ext <;> simp [goldenMul, goldenTau]
  · ring
  · omega
```

This is a `theorem` that turns the integral linear divisibility condition

$$
5\mid 2M+N
$$

into an explicit factorization of the golden integer

$$
\alpha=M+N\varphi
$$

by the distinguished ramifier

$$
\tau=2+\varphi.
$$

## Mathematical statement

From `h : (5 : ℤ) ∣ 2 * M + N`, there exists an integer `k` such that

$$
2M+N=5k.
$$

The theorem then explicitly constructs

$$
\beta=(M-k)+(2k-M)\varphi
$$

and proves

$$
M+N\varphi=\tau\beta.
$$

Because `goldenTau = ⟨2,1⟩`, substituting

$$
(a,b)=(2,1),\qquad(c,d)=(M-k,2k-M)
$$

into the golden multiplication law

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

gives first coordinate

$$
2(M-k)+(2k-M)=M,
$$

and second coordinate

$$
2(2k-M)+(M-k)+(2k-M)=5k-2M=N,
$$

where the last equality is exactly the rearrangement of `2*M + N = 5*k`.

Thus 0186 does more than record that five appears numerically in a norm. It reconstructs an actual `τ` factor inside the golden order from an integral congruence condition.

## Role in the full proof

Declarations 0177–0185 introduce and certify the concrete ramified elements above five:

- `goldenSqrtFive = 2φ - 1`
- `goldenTau = 2 + φ`
- `N(τ)=5`
- `τ * conj τ = 5`

Declaration 0186 advances one step further. It converts the coordinate condition

$$
5\mid 2M+N
$$

into the ring-theoretic fact

$$
\tau\mid(M+N\varphi)
$$

with an explicit quotient.

This is crucial in the later exceptional five-adic branch. The downstream ramifier-stripping argument derives a divisibility condition of the form `5 ∣ 2*M+N`, then invokes

```lean
rcases exists_goldenTau_factor_of_five_dvd h5A with
    ⟨k, beta, hk, hbeta, halpha⟩
```

to obtain the concrete identity `alpha = goldenMul goldenTau beta`.

So 0186 acts as an **extractor** that translates visible five-adic divisibility on integer coordinates into a visible ramified factor in the golden order.

## Direct dependencies

The principal direct dependencies are:

- `GoldenInt`
- 0178 `goldenTau`
- 0124 `goldenMul`
- integer divisibility `∣`
- `GoldenInt.ext`

The proof uses the tactics:

- `rcases`
- `refine`
- `ext`
- `simp`
- `ring`
- `omega`

Although 0184 `goldenNorm_tau` and 0185 `golden_tau_mul_conj` are important mathematical background, they are not direct Lean dependencies of this proof. The theorem constructs the factor directly from the divisibility witness.

## Proof flow

The proof has four stages.

### 1. Extract the quotient `k` from the divisibility hypothesis

```lean
rcases h with ⟨k, hk⟩
```

Expanding `(5 : ℤ) ∣ 2*M+N` yields

```lean
k : ℤ
hk : 2 * M + N = 5 * k
```

### 2. Construct the quotient candidate `beta`

```lean
refine ⟨k, ⟨M - k, 2 * k - M⟩, hk, rfl, ?_⟩
```

The existential witnesses are supplied explicitly:

$$
\beta=\langle M-k,\;2k-M\rangle.
$$

The first conjunct is discharged by `hk`, and the coordinate definition of `beta` by `rfl`.

### 3. Reduce the golden-integer equality to coordinate equalities

```lean
ext <;> simp [goldenMul, goldenTau]
```

`GoldenInt.ext` turns

$$
\langle M,N\rangle=\tau\beta
$$

into first- and second-coordinate goals, while `simp` unfolds the explicit multiplication and the coordinates of `goldenTau`.

### 4. Close the first coordinate algebraically and the second using `hk`

```lean
· ring
· omega
```

The first coordinate is a pure polynomial identity and closes by `ring`.

The second requires

$$
N=5k-2M,
$$

which follows from `hk : 2M+N=5k`; `omega` handles that linear arithmetic step.

## Lean-specific processing

### `rcases h with ⟨k, hk⟩`

Integer divisibility is represented by an existential witness, so the quotient `k` is extracted directly. The orientation of `hk` already matches the first conjunct of the theorem statement and can be reused without rewriting.

### Nested existential construction with `refine`

The target begins with

```lean
∃ k : ℤ, ∃ beta : GoldenInt, ...
```

so `refine ⟨k, beta, ...⟩` simultaneously supplies both witnesses and the conjunction components.

### `ext`

Since `GoldenInt` is an explicit two-coordinate structure, reducing structure equality to `.fst` and `.snd` makes the remaining goals ordinary integer arithmetic.

### `simp [goldenMul, goldenTau]`

This deliberately drops back to the raw coordinate layer. In contrast with 0185, which reused theorem-level APIs, 0186 must construct a quotient witness explicitly, so exposing the coordinate formulas is natural.

### Division of labor between `ring` and `omega`

The first coordinate is hypothesis-free polynomial normalization, hence `ring`. The second depends on the linear relation `hk`, hence `omega`.

## Redundancy and duplication

Mathematically, multiplication by `tau` is the lattice map

$$
(c,d)\mapsto(2c+d,\;c+3d).
$$

The current proof solves the inverse problem under the congruence condition `5 ∣ 2M+N` by writing the quotient coordinates directly as

$$
(c,d)=(M-k,2k-M).
$$

This is locally minimal and highly auditable, but if similar factor-extraction arguments are later needed for other ramified elements, the inverse-coordinate calculation could become duplicated.

There is also a conceptual relationship with 0185:

- 0185 gives the internal factorization of the rational prime: `5 = τ * conj τ`.
- 0186 extracts a `τ` factor from a linear divisibility criterion.

These are not logically redundant, but they naturally belong to the same ramification API cluster.

## Optimization candidates

### 1. Keep the current explicit-witness proof

This is the clearest option when auditability matters: the quotient coordinates are visible directly in the theorem statement and proof.

### 2. Restate the result through `GoldenDivides`

The following module introduces

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

so a later wrapper could expose the theorem as

```lean
(5 : ℤ) ∣ 2 * M + N →
GoldenDivides goldenTau (⟨M,N⟩ : GoldenInt)
```

which is closer to the mathematical reading “`tau` divides `M+Nφ`”.

The present placement inside `GoldenOrder.lean`, however, intentionally avoids depending on the later `GoldenDivisibility.lean` module.

### 3. Abstract the inverse lattice map

Multiplication by `tau` can be represented by an integer matrix of determinant `5`. One could characterize its image by a congruence condition and derive 0186 as a specialization.

This is mathematically cleaner and more general, but introduces substantial abstraction for a theorem that is currently short and concrete.

### 4. Compare arithmetic closing tactics

After simplification, it may be possible to close both coordinate goals uniformly with `omega`, `ring_nf`, or another normalization route. This is not verified here because no Lean build is run.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The theorem directly needs functionality around:

- integer divisibility
- structure extensionality
- `simp`
- `ring`
- `omega`

A minimal modular import would therefore likely involve integer algebra/divisibility plus ring normalization and the Omega tactic. The exact minimal import set is not verified in this museum pass, and the full `GoldenOrder` module already uses `norm_num`, `ring`, and `omega` elsewhere.

Accordingly, import minimization here is recorded as a candidate rather than a confirmed reduction.

## Comparator challenge suitability

Yes. This theorem is a good small benchmark for **constructive factor extraction**.

Possible implementations include:

- A: current explicit witness + `ext` + `ring` / `omega`
- B: characterize multiplication by `tau` as an integer lattice map
- C: prove a `GoldenDivides` formulation first
- D: derive factorization indirectly through 0185 `τ * conj τ = 5`
- E: use a quotient / `AdjoinRoot` / quadratic-algebra representation and ideal-theoretic ramification

Useful comparison axes are:

- visibility of the quotient witness
- proof-term size
- dependency depth
- mathematical provenance
- downstream usability
- generalizability
- tactic dependence

The contrast between A and B is especially useful: direct coordinate solving versus a determinant-five lattice-map interpretation.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this theorem immediately after 0185 and immediately before the end of `GoldenOrder.lean`:

```lean
theorem golden_tau_mul_conj : ...

/-- Divisibility by five of `2*M+N` explicitly extracts a factor of `tau`. -/
theorem exists_goldenTau_factor_of_five_dvd ...

end DkMath.FLT.Five

/-! ===== END GENERATED SOURCE: DkMath/FLT/Five/GoldenOrder.lean ===== -/
/-! ===== BEGIN GENERATED SOURCE: DkMath/FLT/Five/GoldenDivisibility.lean ===== -/
```

The branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0187 `GoldenDivides`**, the first declaration of the next module, `GoldenDivisibility.lean`:

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

Declaration 0186 explicitly extracts a `tau` factor. Declaration 0187 then names that kind of internal factorization as a general golden-divisibility relation.

The next layer is therefore

$$
\text{explicit factor witness}
\longrightarrow
\text{golden divisibility API}
\longrightarrow
\text{norm divisibility / units / relative primality}.
$$

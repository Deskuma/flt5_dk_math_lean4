# 0187 — `GoldenDivides`

## Lean type

```lean
/-- Explicit golden divisibility, definitionally compatible with ring divisibility. -/
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

This is a `def`, not a theorem. It defines divisibility in the golden order by the explicit existence of a quotient `q`.

## Mathematical statement and meaning of the declaration

`GoldenDivides d x` represents

$$
d\mid x
$$

inside the raw golden-order API, and its definition is exactly

$$
\exists q\in\mathbb Z[\varphi],\quad x=dq.
$$

Lean's standard ring divisibility `d ∣ x` has the same mathematical meaning, but the present definition fixes multiplication through the raw operation `goldenMul` rather than the standard `*` notation.

Thus `GoldenDivides` does not introduce a new number-theoretic notion. It is an auditable domain-specific divisibility interface between the explicit coordinate API used by the FLT5 development and Mathlib's standard algebra API.

## Role in the full proof

Declaration 0186 `exists_goldenTau_factor_of_five_dvd` converted the integer condition

$$
5\mid 2M+N
$$

into an explicit factorization

$$
M+N\varphi=\tau\beta.
$$

Immediately afterward, at the beginning of `GoldenDivisibility.lean`, 0187 gives a general name to the relation “one golden integer occurs as a factor of another.”

The source then develops the basic API:

* `goldenDivides_iff_dvd`
* `goldenDivides_refl`
* `goldenDivides_trans`
* `goldenDivides_sub`
* `goldenNorm_dvd_of_goldenDivides`

In later relative-primality arguments, a common divisor `d` is propagated to differences through code such as

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

and then `goldenNorm_dvd_of_goldenDivides` transports golden divisibility to ordinary integer divisibility of norms.

The same module eventually defines

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

so `GoldenDivides` becomes the primitive vocabulary underlying the later proof that an element and its conjugate have no nonunit common divisor.

## Direct dependencies

The definition has only a very small direct dependency surface:

* `GoldenInt`
* 0124 `goldenMul`
* Lean's existential proposition `∃`

Because this is a definition, there is no proof script and no direct dependency on an earlier theorem.

Conceptually,

$$
\texttt{GoldenInt}
+\texttt{goldenMul}
\longrightarrow
\texttt{GoldenDivides}.
$$

The immediately following theorem `goldenDivides_iff_dvd` proves equivalence with the standard `Dvd.dvd` relation.

## Construction flow

The construction consists of a single layer:

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

1. `d` is the candidate divisor and `x` the dividend.
2. A quotient `q : GoldenInt` is required to exist.
3. The definition requires `x` to be exactly `goldenMul d q`.

Mathematically this is the ordinary definition of divisibility. The only special feature is that multiplication is exposed through the explicit raw coordinate operation.

## Lean-specific processing

`GoldenDivides d x` has type `Prop`, so it is a proposition rather than computational data.

Because it is defined by an existential witness, a hypothesis

```lean
h : GoldenDivides d x
```

can later be destructured by

```lean
rcases h with ⟨q, hq⟩
```

to recover both the quotient `q` and the factorization equality.

Moreover, `goldenMul` has already been connected definitionally to the `Mul GoldenInt` instance. Therefore the next theorem can move between raw and standard divisibility almost for free:

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

The fact that `simpa` suffices in both directions is the key implementation property: the custom relation is definitionally compatible with the standard ring multiplication.

## Redundancy and duplication

Mathematically, `GoldenDivides` duplicates Mathlib's standard `d ∣ x`. The immediately following equivalence theorem confirms that the custom relation adds no logical expressive power.

There are nevertheless good reasons to keep the wrapper:

* it can be stated entirely in the raw `goldenMul` layer;
* theorem names make it explicit that the argument is about divisibility in the golden order;
* the Bézout-free / norm-based part of the FLT5 proof reads naturally in domain-specific vocabulary;
* the relation can be used independently of later Euclidean-domain infrastructure.

On the other hand, by this stage `GoldenInt` already has `CommRing` and `IsDomain` instances, so a design using only standard divisibility would also be viable.

## Optimization candidates

1. **Keep the current domain-specific wrapper**

   * preserves auditability and a clear raw/standard API boundary.

2. **Remove `GoldenDivides` and use only standard `∣`**

   * the wrapper lemmas `goldenDivides_refl/trans/sub` could then be replaced by standard Mathlib lemmas, reducing code volume.

3. **Introduce custom notation**

   * this might improve local readability, but it would compete with the standard `∣` notation and is therefore of limited value.

4. **Document the bootstrap rationale more explicitly**

   * if module boundaries are later reorganized, a comment explaining why a custom divisibility wrapper is retained would improve auditability.

The current design is already safe because `goldenDivides_iff_dvd` appears immediately afterward and guarantees easy interoperability with the standard API.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

This definition itself effectively requires only:

* `GoldenInt`
* `goldenMul`
* basic proposition and existential syntax

No advanced Mathlib theorem or tactic is required by the definition itself.

The surrounding `GoldenDivisibility.lean` module soon uses standard divisibility lemmas, integer divisibility, norms, and unit arguments, so the minimal import set for the full module will be broader than the minimal surface of 0187 alone.

Because this museum pass does not run a Lean build, the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The comparison is particularly clean:

* A: current `GoldenDivides` wrapper plus bridge theorem
* B: use standard `d ∣ x` everywhere
* C: write existential raw factorizations directly in each theorem
* D: redesign the later API around gcd / associated elements after `EuclideanDomain GoldenInt` is available

Useful metrics include:

* downstream theorem size
* readability of theorem names
* typeclass dependency depth
* usability before Euclidean-domain construction
* simp / rewrite burden
* interoperability with Mathlib's standard divisibility API

The contrast between A and B is especially useful for measuring whether a domain-specific wrapper provides enough proof-audit value to justify its extra API layer.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The module header explains that this layer develops divisibility, units, and relative primality in the golden order, using the Bézout-free statement that every common divisor is a unit in the element/conjugate factorization argument.

The target branch also contains Japanese and English PDFs. The exact PDF page or section corresponding to this small definition was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0188 `goldenDivides_iff_dvd`**:

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

0187 introduces the domain-specific raw divisibility relation; 0188 immediately proves that it is exactly equivalent to Mathlib's standard ring divisibility. This bridge lets the following reflexivity, transitivity, and subtraction-closure lemmas reuse the standard `dvd` API.

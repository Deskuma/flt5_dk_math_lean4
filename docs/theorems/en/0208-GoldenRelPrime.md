# 0208 — `GoldenRelPrime`

## Lean type

```lean
/-- Relative primality expressed by saying that every common divisor is a unit, hence
has norm `±1`. -/
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

This is a `def`, not a theorem. It defines relative primality of two golden integers by requiring every common divisor to be a unit.

## Mathematical statement and meaning of the declaration

Mathematically,

$$
GoldenRelPrime(x,y)
$$

means

$$
\forall d\in\mathbb Z[\varphi],\quad d\mid x\land d\mid y\Longrightarrow d\in\mathbb Z[\varphi]^\times.
$$

In an integral domain or Euclidean domain, relative primality admits several equivalent formulations: the gcd is a unit, Bézout coefficients exist, or there is no common nonunit divisor. This definition deliberately chooses the most direct formulation for the present proof: **every common divisor is a unit**.

By declarations 0198–0207, the `GoldenUnit` API and its basic closure properties are already available, so the common-divisor endpoint can now be expressed by the single proposition `GoldenUnit d`.

Declaration 0202 also shows that unitness is equivalent to norm `±1`, so in later proofs the definition can be transported to the integer statement

$$
d\mid x,\ d\mid y
\Longrightarrow
N(d)=\pm1.
$$

That projection is central to the later proof that a stripped golden element and its conjugate are relatively prime.

## Role in the full proof

`GoldenRelPrime` is the final foundational predicate in `GoldenDivisibility.lean`. It becomes the contract passed into the following Euclidean-domain and fifth-power factor-extraction layers.

The intended later use is a pair such as `beta` and `goldenConj beta`. Given an arbitrary common divisor `d`, the proof proceeds conceptually as follows.

1. Assume `d` divides both `beta` and `conj beta`.
2. By 0191 `goldenDivides_sub`, `d` divides `beta - conj beta`.
3. By 0192 `goldenNorm_dvd_of_goldenDivides`, `N(d)` divides both `N(beta)` and `N(beta-conj beta)`.
4. Integer coprimality information from the packet shows that those two integer masses have no nonunit common divisor.
5. Hence `N(d)=±1`.
6. By 0201 `goldenUnit_of_norm_eq_one_or_neg_one`, conclude `GoldenUnit d`.

Thus the definition provides exactly the final goal shape needed to solve a common-divisor problem in the golden order by projecting it to ordinary integer divisibility through the norm.

For fifth-power factor extraction, one needs the standard Euclidean-domain principle that relatively prime factors of a fifth power are themselves fifth powers up to units. `GoldenRelPrime` supplies the relative-primality hypothesis in a form tailored to the explicit golden-order API.

## Direct dependencies

The definition itself has only three project-local direct dependencies:

- `GoldenInt`
- 0187 `GoldenDivides`
- 0198 `GoldenUnit`

Beyond universal quantification and implication, it directly depends on no theorem or tactic.

Conceptually,

$$
GoldenDivides
+GoldenUnit
\longrightarrow
GoldenRelPrime.
$$

The later proofs establishing `GoldenRelPrime` rely more substantially on 0191 `goldenDivides_sub`, 0192 `goldenNorm_dvd_of_goldenDivides`, and the 0201/0202 unit–norm criterion.

## Construction flow

The predicate is a single universal-property definition:

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

It reads in four steps.

1. Take an arbitrary golden integer `d`.
2. Assume `d` divides `x`.
3. Assume `d` also divides `y`.
4. Require `d` to be a unit.

No gcd witness and no Bézout coefficients are stored. Only the universal property of common divisors is retained.

## Lean-specific processing

The definition returns `Prop`, so it acts as a logical contract rather than a data structure.

Given

```lean
hrel : GoldenRelPrime x y
```

and

```lean
hdx : GoldenDivides d x
hdy : GoldenDivides d y
```

one obtains the unit conclusion simply by

```lean
exact hrel d hdx hdy
```

Conversely, proving `GoldenRelPrime x y` naturally starts with

```lean
intro d hdx hdy
```

and then shows that an arbitrary common divisor is a unit.

Compared with gcd-based or ideal-theoretic coprimality, this produces a very direct local proof goal and avoids introducing auxiliary Bézout data.

## Redundancy and duplication

Mathematically, `GoldenRelPrime` may overlap with standard coprimality notions from the general algebra hierarchy.

`GoldenInt` already has an `IsDomain` instance and is later upgraded to a `EuclideanDomain`, so the final development could in principle express relative primality through gcd, associated elements, or a standard `IsCoprime`-style API.

The custom predicate nevertheless has clear advantages here:

- it is usable before Euclidean-domain construction;
- it avoids Bézout coefficients;
- the exact downstream requirement is already “every common divisor is a unit”;
- it composes directly with the auditable raw predicates `GoldenDivides` and `GoldenUnit`.

Thus it sacrifices some generality in exchange for a very precise domain-specific proof interface.

## Optimization candidates

1. **Keep the present universal-common-divisor definition**
   - it makes downstream goals explicit and easy to audit.

2. **Add bridge theorems to standard coprimality APIs**
   - once Euclidean-domain structure is available, an equivalence with gcd / coprime predicates could unlock more Mathlib lemmas.

3. **Connect `GoldenDivides` and `GoldenUnit` to standard `∣` and `IsUnit`**
   - this could reduce wrapper layers, at some cost to explicit-coordinate readability.

4. **Publish symmetry explicitly**
   - `GoldenRelPrime x y → GoldenRelPrime y x` is immediate from the definition and may be worth naming if frequently reused.

5. **Compare against a gcd-is-unit primary definition**
   - after `EuclideanDomain GoldenInt` is available, the two approaches can be compared for proof size and dependency depth.

The current definition is already minimal; the main optimization opportunity is interoperability with standard algebra APIs rather than local compression.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib` globally.

This definition itself directly needs almost nothing beyond its project-local dependencies:

- `GoldenInt`
- `GoldenDivides`
- `GoldenUnit`
- basic `Prop`, `∀`, and `→`

It directly uses no `ring`, `norm_num`, gcd theorem, or integer-divisibility theorem.

The surrounding `GoldenDivisibility.lean` module uses a substantially broader surface, including norms, integer divisibility, conjugation, and unit arguments, so import minimization should be evaluated at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Relative-primality representation gives a clean design comparison.

Possible contestants are:

- A: current `GoldenRelPrime` — every common divisor is a `GoldenUnit`
- B: standard `IsCoprime` / gcd API
- C: a Bézout relation `∃ a b, a*x + b*y = 1`
- D: `gcd x y` is a unit / associated to `1`
- E: a norm-side coprimality predicate as the primary representation

Useful metrics include availability before Euclidean-domain construction, proof dependency depth, witness size, Mathlib reuse, size of downstream FLT5 proofs, and mathematical readability.

The A-versus-C comparison is especially instructive because this development intentionally favors a Bézout-free relative-primality contract.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The current 0207 documents identify this definition as the declaration immediately following the completed unit block.

The target branch also contains `FLT5-main-ja-v0-r1.pdf` and `FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this small predicate was not identified in this pass, so no page reference is inferred.

## Next declaration to read

`GoldenRelPrime` appears at the end of `GoldenDivisibility.lean`. The next module is `GoldenEuclidean.lean`.

The next declaration in dependency order is **0209 `GoldenRat`**, the rational-coordinate type used to construct Euclidean division:

```lean
abbrev GoldenRat := ℚ × ℚ
```

After 0208 fixes the relative-primality contract, the next module constructs norm-Euclidean division by forming a rational quotient, rounding its two coordinates, and proving that the remainder has strictly smaller absolute norm than the divisor.
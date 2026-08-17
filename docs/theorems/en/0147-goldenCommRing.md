# 0147 — `goldenCommRing`

## Lean type

```lean
instance goldenCommRing : CommRing GoldenInt := by
  refine
    { goldenAddGroupWithOne with
      npow := fun n x => goldenPow x n
      npow_zero := by intro x; rfl
      npow_succ := by
        intro n x
        change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
        rfl
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
    simp <;> ring
```

This is not a theorem but a named `instance` providing the complete commutative-ring structure `CommRing GoldenInt`. It reuses the additive and cast structure prepared by 0145 `goldenAddCommGroup` and 0146 `goldenAddGroupWithOne`, aligns `goldenMul` and `goldenPow` with standard multiplication and natural powers, and proves the remaining ring laws by reducing them to coordinate calculations.

## Mathematical statement and meaning of the declaration

`GoldenInt` represents

$$
a+b\varphi
$$

by the integral coordinate pair `(a,b)`, while `goldenMul` is defined so that the generator satisfies

$$
\varphi^2=\varphi+1.
$$

Hence

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi.
$$

The present instance asserts that the explicitly defined addition, negation, subtraction, multiplication, unit, and natural powers satisfy all axioms of a commutative ring. Thus Lean / Mathlib may treat `GoldenInt` not merely as an integer pair but as an ordinary commutative ring.

Mathematically, this corresponds to the fact that the coordinate model of the golden integer ring $\mathbb Z[\varphi]$ is a commutative ring. This declaration does not itself construct an isomorphism with an `AdjoinRoot` or quotient-ring representation; it proves the ring laws directly for the explicit coordinate operations.

## Role in the overall proof

This is a major boundary in the `GoldenOrder` layer. By 0145, `GoldenInt` has a commutative additive-group structure, and 0146 adds the natural/integer cast layer through `AddGroupWithOne`. Declaration 0147 then supplies multiplication, powers, distributivity, unit laws, associativity, and commutativity, completing

$$
\texttt{GoldenInt}
\longrightarrow
\texttt{CommRing GoldenInt}.
$$

After this instance is available, downstream code can use not only the raw `goldenMul` API but also ordinary Mathlib notation and infrastructure such as

```lean
x * y
x ^ n
x ∣ y
```

Later layers connect explicit `GoldenDivides` to ordinary divisibility `d ∣ x`, construct `NoZeroDivisors`, and proceed toward Euclidean-domain structure, gcd theory, and fifth-power factorization. Therefore `goldenCommRing` is the central interface connecting the explicit coordinate model to Mathlib's generic ring theory.

## Direct dependencies

The main direct dependencies are:

- `GoldenInt`
- 0146 `goldenAddGroupWithOne`
- 0124 `goldenMul`
- 0125 `goldenPow`
- `GoldenInt.ext`
- the coordinate `@[simp]` projection theorems 0133–0144
- Mathlib's `CommRing`
- the `ring` tactic

In particular, the multiplication laws depend on 0143 `golden_fst_mul` and 0144 `golden_snd_mul`, which expand standard `*` notation into integer-coordinate polynomials. The earlier simp API for addition, zero, one, negation, and subtraction likewise forms the basis of the final `ext <;> simp` reduction.

The broad dependency chain is

$$
\texttt{raw coordinate operations}
\longrightarrow
\texttt{projection simp lemmas}
\longrightarrow
\texttt{goldenAddCommGroup}
\longrightarrow
\texttt{goldenAddGroupWithOne}
\longrightarrow
\texttt{goldenCommRing}.
$$

## Proof / construction flow

The construction has two stages.

First, it reuses the structure from 0146 and registers natural powers by

```lean
npow := fun n x => goldenPow x n
```

while proving the zero-exponent and successor clauses directly from the recursive definition of `goldenPow`.

```lean
npow_zero := by intro x; rfl
```

closes the law

$$
x^0=1
$$

definitionally.

For the successor case,

```lean
change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
rfl
```

changes the goal to exactly the successor clause of the raw recursive definition.

Second, the remaining ring laws

- `add_comm`
- `left_distrib`
- `right_distrib`
- `zero_mul`
- `mul_zero`
- `mul_assoc`
- `one_mul`
- `mul_one`
- `mul_comm`

are left as structure holes and discharged uniformly by

```lean
intros <;> ext <;>
simp <;> ring
```

The `ext` tactic decomposes equality of `GoldenInt` values into equalities of the `fst` and `snd` integer coordinates. The `simp` step uses the projection API accumulated in 0133–0144 to expand the operations into coordinate formulas, and `ring` finally closes the resulting integer polynomial identities.

## Lean-specific processing

The key Lean technique is the combination of structure update and a uniform tactic pipeline.

```lean
{ goldenAddGroupWithOne with ... }
```

reuses the additive-group, `0`, `1`, and cast fields already established in 0146, so this declaration only supplies what is still needed for the complete ring structure rather than rebuilding `CommRing` from scratch.

The `change` command in `npow_succ` aligns the standard power law with the raw recursive API. Once the goal is rewritten to the exact defining equation of `goldenPow`, `rfl` suffices; no separate theorem about powers is needed.

The final script

```lean
intros <;> ext <;> simp <;> ring
```

captures the overall implementation strategy:

$$
\text{GoldenInt equality}
\to
\text{coordinate equalities}
\to
\text{integer polynomial identities}.
$$

Because `ext` and the projection simp lemmas form a strong API boundary, the proof reaches a normalized setting in which the generic `ring` tactic can finish the algebra.

## Redundancy and duplication

The instance appears to supply `add_comm` again even though commutative addition was already proved in 0145. This reflects the concrete structure-update shape used by the source and the Mathlib hierarchy available there; it should not automatically be classified as mathematical duplication.

Likewise, `left_distrib` / `right_distrib`, `zero_mul` / `mul_zero`, and `one_mul` / `mul_one` occur in symmetric pairs. In ordinary mathematics, some can be derived from commutativity once enough ring structure is available. During construction of the structure itself, however, the completed `CommRing` instance is not yet available for unrestricted reuse, so proving each requested field directly by coordinate normalization is a transparent bootstrap strategy.

The shared `simp <;> ring` tail already compresses a large amount of otherwise repetitive proof code.

## Optimization candidates

Several directions are worth comparing.

1. Keep the current explicit coordinate `CommRing` construction.
2. Derive symmetric fields from earlier proved laws when possible, reducing repeated coordinate `ring` work.
3. Abstract a general quadratic-coordinate ring satisfying

$$
\theta^2=p\theta+q
$$

and specialize the golden case to $p=q=1$.
4. Build the structure through Mathlib infrastructure such as `AdjoinRoot`, quotient rings, or quadratic-algebra representations, then transport the result to the explicit coordinate model through an isomorphism.
5. Reconsider whether the custom recursive `goldenPow` should remain a separate bootstrap definition or be identified with standard ring powers after the `CommRing` structure is available.

Options 4 and 5 may reduce some local proof burden but introduce additional abstraction layers. The current implementation has the auditing advantage that all ring laws can ultimately be inspected as explicit integer-coordinate identities.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

This instance directly relies on the `CommRing` hierarchy, extensionality support, `simp`, and the `ring` tactic. Compared with the simpler structure declarations immediately before it, the tactic-side dependency is therefore more visible.

The full `Mathlib` umbrella import is unlikely to be necessary solely for this declaration. A narrower combination of algebra-hierarchy imports and ring-normalization tactic imports may suffice. The exact minimal import set is version-dependent and would need to be confirmed by a Lean build. No Lean build is performed in this museum pass, so no exact minimal modules are claimed.

## Suitability as a Comparator challenge

This declaration is highly suitable as a Comparator challenge because implementation strategy now has direct downstream consequences.

Useful alternatives include:

- the current explicit coordinate + `ext` + `simp` + `ring` approach;
- specialization of a generic quadratic-coordinate ring;
- an `AdjoinRoot` / quotient-based implementation;
- structure transport from an existing quadratic-algebra representation.

Evaluation criteria include:

- proof size required to construct `CommRing`;
- number of fields closed by `rfl`;
- stability of simp normal forms;
- downstream proof burden for divisibility, norms, and Euclidean-domain structure;
- transparency of the representation;
- Mathlib import size;
- generalizability.

In particular, this makes a strong challenge for measuring the trade-off between shorter abstract constructions and preservation of coordinate-level visibility.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`. There, 0146 `goldenAddGroupWithOne` is followed immediately by this `goldenCommRing`, and `goldenDoubleEmbedding` appears immediately afterward.

The mathematical meaning of this instance is consistent with the PDFs' treatment of the golden integer ring, but the concrete PDF page or section corresponding to this implementation declaration was not directly identified in this pass. Therefore no page number is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

This is a `def`, not a theorem. It defines an explicit coordinate map sending the golden integer $a+b\varphi$ toward the `Zsqrtd 5` representation after doubling. Once 0147 has completed the commutative-ring structure on `GoldenInt`, the next stage connects this explicit ring to the existing `Zsqrtd 5` infrastructure in preparation for excluding zero divisors and moving toward integral-domain arguments.
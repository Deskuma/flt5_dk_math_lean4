# 0145 — `goldenAddCommGroup`

## Lean type

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  refine
    { sub := goldenSub
      nsmul := @nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩
      zsmul := @zsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩ ⟨goldenNeg⟩
        (@nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]
```

This is not a theorem but a named `instance` equipping `GoldenInt` with Lean / Mathlib's standard `AddCommGroup` structure.

## Mathematical statement and meaning of the declaration

Write an element of `GoldenInt` as

$$
x=a+b\varphi.
$$

The upstream zero, addition, and negation operations are implemented coordinatewise as

$$
(a,b)+(c,d)=(a+c,b+d),
$$

$$
0=(0,0),
$$

and

$$
-(a,b)=(-a,-b).
$$

Thus the additive structure of `GoldenInt` is essentially the coordinatewise additive structure of the integer lattice $\mathbb Z^2$. It satisfies associativity, the zero laws, additive inverses, and commutativity.

This instance registers that fact as `AddCommGroup GoldenInt` in Lean's algebra hierarchy. The relevant mathematics here is the additive basis structure of $1,\varphi$, not the multiplicative quadratic relation $\varphi^2=\varphi+1$.

## Role in the overall proof

By 0133–0144, the coordinate projection simp API for `Zero`, `One`, `Add`, `Neg`, `Sub`, and `Mul` has been established. This declaration collects the additive part of that API and promotes the raw coordinate operations to a genuine commutative additive group.

Once this instance exists, downstream code can use generic additive-group lemmas, integer and natural scalar multiplication, subtraction, and cancellation on `GoldenInt` through standard Mathlib interfaces. It is also the foundation for the immediately following `goldenAddGroupWithOne` and then `goldenCommRing` constructions.

In the full FLT5 development, golden-integer factorization, conjugation, norm, divisibility, and Euclidean-domain arguments require `GoldenInt` to participate in ordinary ring-theoretic APIs. This declaration closes the additive half of that interface.

## Direct dependencies

The declaration directly or effectively depends on:

- `GoldenInt`
- `goldenZero`
- `goldenAdd`
- `goldenNeg`
- `goldenSub`
- `GoldenInt.ext`
- the `Zero GoldenInt`, `Add GoldenInt`, `Neg GoldenInt`, and `Sub GoldenInt` instances
- the coordinate `@[simp]` projection theorems from 0133–0142
- `nsmulRec`
- `zsmulRec`
- the standard `AddCommGroup` typeclass

`GoldenInt.ext` reduces equality of golden integers to equality of the `fst` and `snd` coordinates. Then `simp` uses projection lemmas such as `golden_fst_zero`, `golden_snd_zero`, `golden_fst_add`, `golden_snd_add`, `golden_fst_neg`, and `golden_snd_neg`, reducing the goals to ordinary integer additive identities.

## Proof / construction flow

The proof starts by constructing the structure explicitly with `refine`:

```lean
refine
  { sub := goldenSub
    nsmul := @nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩
    zsmul := @zsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩ ⟨goldenNeg⟩
      (@nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ }
```

Subtraction, natural scalar multiplication, and integer scalar multiplication are supplied explicitly, while the group laws remain as proof goals.

The final tactic chain

```lean
<;> intros <;> ext <;> simp [add_comm, add_left_comm]
```

handles those laws uniformly.

Conceptually, for each goal it performs the following sequence:

1. `intros` introduces the relevant variables.
2. `ext` splits equality in `GoldenInt` into `fst` and `snd` coordinate equalities.
3. `simp` expands golden-integer operations into integer coordinate operations.
4. Integer addition identities such as `add_comm` and `add_left_comm` normalize and close the goals.

For example, associativity

$$
(x+y)+z=x+(y+z)
$$

becomes ordinary associativity of integer addition on both coordinates. Commutativity is reduced in exactly the same way.

## Lean-specific processing

A notable point is that the declaration does not merely rely on instance inference to assemble the structure. It fills the relevant `AddCommGroup` fields explicitly.

The explicit uses of `nsmulRec` and `zsmulRec` fix natural-number and integer scalar multiplication to recursive implementations built from the raw coordinate operations. This keeps the bootstrap dependency direction visible and avoids opaque dependence on an instance that is still being constructed.

The tactic chain

```lean
intros <;> ext <;> simp [add_comm, add_left_comm]
```

is also a Lean-specific compression of several structure-field proofs into one uniform pattern. `ext` uses `GoldenInt.ext`, while `simp` uses the projection theorems prepared immediately before this declaration as a rewrite database.

Thus the many small `@[simp]` projection theorems from 0133–0144 are collected here for the first time into a larger automated algebra proof.

## Redundancy and duplication

Mathematically, the additive structure of `GoldenInt` is equivalent to componentwise addition on $\mathbb Z\times\mathbb Z$, so proving the group laws coordinate by coordinate reconstructs a standard product structure.

Likewise, explicitly giving `sub := goldenSub`, `nsmul := nsmulRec ...`, and `zsmul := zsmulRec ...` can look verbose compared with designs where the hierarchy fills in more structure automatically.

The current approach nevertheless has important advantages:

- the connection between raw operations and the algebra hierarchy remains explicit;
- bootstrap dependence on instance search is reduced;
- it is easy to audit exactly which operations define the `GoldenInt` additive group.

For an auditable FLT5 formalization, this transparency can be more valuable than simply minimizing line count.

## Optimization candidates

Several alternatives are worth comparing:

1. retain the current explicit field-by-field `AddCommGroup` construction;
2. define an additive equivalence between `GoldenInt` and `ℤ × ℤ` and transport the existing product `AddCommGroup` structure;
3. represent `GoldenInt` more directly as a product-like type and inherit more instances automatically;
4. allow the hierarchy to provide `nsmul` / `zsmul` when possible, reducing explicit fields;
5. generate the repetitive projection simp lemmas systematically to reduce boilerplate around the manual structure proof.

The relevant criteria are not only source length but also definitional transparency, simp normal forms, stability of instance search, and the simplicity of the later `CommRing` construction.

## Required Mathlib imports and import optimization

The standalone artifact uses

```lean
import Mathlib
```

The functionality needed by this declaration includes `AddCommGroup`, `nsmulRec`, `zsmulRec`, extensionality, simplification, and the additive group structure of integers. Therefore the entire `Mathlib` umbrella import is unlikely to be required solely for this instance.

However, determining the exact minimal import requires checking the upstream `GoldenInt` definitions together with tactic support in an actual Lean build. No Lean build is performed in this museum pass, so possible reduction toward `Mathlib.Algebra.Group.*`-style imports is recorded only as an optimization hypothesis, not as a verified minimal import set.

## Suitability as a Comparator challenge

This declaration is particularly suitable.

Natural implementation families include:

- the current field-by-field `AddCommGroup` construction;
- transport of the structure from `ℤ × ℤ` through an additive equivalence;
- direct use of a product-like representation with inherited instances.

Useful metrics include proof length, the number of laws closed by `rfl` or `simp`, instance-search stability, readability of definitional unfolding, effects on the later `AddGroupWithOne` / `CommRing` constructions, and resilience to representation changes.

Compared with an individual projection theorem, this declaration exposes a much clearer trade-off between API design and algebra-hierarchy construction, making it a strong Comparator challenge candidate.

## Relation to the PDFs and Lean source

The target branch contains the Japanese PDF `FLT5-main-ja-v0-r1.pdf` and the English PDF `FLT5-main-en-v0-r1.pdf`.

The formal source of truth is the generated `DkMath/FLT/Five/GoldenOrder.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean`, together with the source placement recorded in the preceding 0144 museum document. There, `golden_snd_mul` is followed by this `goldenAddCommGroup` instance, then `goldenAddGroupWithOne`, and then `goldenCommRing`.

The concrete PDF page or section corresponding to this instance was not directly identified in this pass, so no PDF location is guessed.

## Next declaration to read

The next declaration in dependency order is

```lean
instance goldenAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { goldenAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }
```

With the present declaration, the commutative additive group structure of `GoldenInt` is complete. The next step adds the standard embeddings of natural numbers and integers to obtain `AddGroupWithOne`, after which `goldenCommRing` completes the commutative ring structure including multiplication.
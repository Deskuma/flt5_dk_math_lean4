# 0053 — `SignedBranchANormalForm`

## 1. Lean declaration

```lean
/-- A primitive exponent-five candidate equipped with its signed five-adic orientation. -/
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

The fully qualified name is `DkMath.FLT.Five.SignedBranchANormalForm`.

## 2. Lean type

```lean
SignedBranchANormalForm (u v w : ℕ) : Prop
```

The generated constructor and projections have approximately the following types.

```lean
SignedBranchANormalForm.mk
  : CounterexamplePack u v w →
    SignedBranchAOrientation u v w →
    SignedBranchANormalForm u v w

SignedBranchANormalForm.pack
  : SignedBranchANormalForm u v w → CounterexamplePack u v w

SignedBranchANormalForm.orientation
  : SignedBranchANormalForm u v w → SignedBranchAOrientation u v w
```

## 3. Mathematical statement

`SignedBranchANormalForm u v w` states that the triple $(u,v,w)$ is a positive primitive exponent-five candidate and is simultaneously equipped with an orientation for entering the signed five-adic descent.

The `pack` field records, schematically,

$$
u>0,\qquad v>0,\qquad w>0,
$$

$$
\gcd(u,v)=1,
$$

$$
u^5+v^5=w^5.
$$

The `orientation` field records one of the two directions from the previous article:

$$
5\mid u\ \land\ 5\mid(w-v),
$$

or

$$
5\mid w\ \land\ 5\mid(u+v).
$$

Thus this structure proves no new arithmetic conclusion by itself. It packages the facts required by the common downstream descent into one normalized input.

## 4. Role in the full proof

The initial Branch-B input is `CounterexamplePack x y z` together with $5\nmid(z-y)$. After the modulo-five analysis, the case $5\mid y$ swaps the two left coordinates and sends `(y,x,z)` to the difference orientation, while the case $5\mid z$ sends `(x,y,z)` to the sum orientation.

```text
Branch-B pack
    ↓ mod 5 routing
┌─────────────────────────────┐
│ differenceGap: swapped pack │
│ sumGap:        original pack│
└─────────────────────────────┘
    ↓
SignedBranchANormalForm
    ↓
common exact five-adic descent
```

Because of this structure, the later construction of `SignedFiveAdicPacket` does not need to reconsider the Branch-B origin or the history of the swap. It receives only `pack` and `orientation`.

## 5. Direct dependencies

The declaration body directly depends on two repository-specific declarations:

- `CounterexamplePack u v w`
- `SignedBranchAOrientation u v w`

On the standard Lean side, it uses only:

- the natural-number type `ℕ`;
- `structure ... : Prop`;
- dependent field types and the automatically generated constructor and projections.

There is no proof term. The declaration is a named-field product of two existing propositions.

## 6. Construction flow

Since this is a structure declaration, there is no proof script.

1. Store a `CounterexamplePack u v w`, containing positivity, primitivity, and the Fermat equation, in `pack`.
2. Store evidence for either `differenceGap` or `sumGap` in `orientation`.
3. Once both fields are present, construct `SignedBranchANormalForm u v w`.
4. A consumer extracts the contents using `hNF.pack` and `hNF.orientation`, or `rcases hNF with ⟨hPack, hOrientation⟩`.

The immediately following theorem `signedBranchA_normalForm_of_branchB` is the first main consumer that actually constructs this structure through the two routes.

## 7. Lean-specific processing

### 7.1 `structure ... : Prop`

The structure lives in `Prop`, not `Type`. Its purpose is to collect proof evidence required downstream, not to return computational data. It is subject to proof irrelevance and is not designed as a runtime data structure.

### 7.2 Shared parameters

The parameters `u v w` belong to the whole structure, so both fields refer to the same triple. A term that combines a pack and an orientation with mismatched coordinates is rejected by the type checker.

### 7.3 Named-field construction

A consumer can construct it as follows.

```lean
refine ⟨hPack, ?_⟩
exact SignedBranchAOrientation.sumGap h5w h5sum
```

Or it can use explicit named fields.

```lean
exact {
  pack := hPack
  orientation := hOrientation
}
```

Because the structure has only two fields, angle-bracket construction is natural in the implementation.

### 7.4 Relation to conjunction

At the propositional level, this is equivalent to:

```lean
CounterexamplePack u v w ∧ SignedBranchAOrientation u v w
```

The dedicated structure provides stable projection names `pack` and `orientation`, a dedicated argument type for downstream APIs, and a mathematical name in the documentation.

## 8. Redundancy and duplication

Logically, this is only a repackaging of `And`; it does not increase proof strength. In that sense, the declaration is redundant.

However, many later layers—`SignedFiveAdicPacket`, the power split, and the square-golden packets—use this normal form as a shared entry point. Bundling the two arguments under one semantic name stabilizes the dependency boundary better than passing them separately each time.

The structure itself does not additionally verify consistency between the equation stored in `CounterexamplePack` and the divisibility conditions stored in the orientation. The subsequent construction theorem supplies valid evidence, so this is sufficient as the intended API boundary.

## 9. Optimization candidates

1. The current two-field structure is already minimal, so there is little to remove from the declaration itself.
2. Replacing it with an `abbrev` for a conjunction would reduce declaration count, but would lose the dedicated type and projection names; this is difficult to recommend.
3. If downstream code repeatedly extracts positivity or the equation through `pack`, delegated helper lemmas could be added. They should wait until actual duplication is observed, because they would enlarge the API.
4. One could encode stronger consistency between the orientation and the pack, but both already share the same `u v w`, and further wrapping would likely be excessive.
5. The name `SignedBranchANormalForm` is long, but accurately records its three roles—signed, Branch A, and normal form—so abbreviation offers little benefit.

## 10. Required Mathlib imports

The generated standalone source on the target branch uses the following import for the whole file:

```lean
import Mathlib
```

This declaration alone requires no new Mathlib facility once `CounterexamplePack` and `SignedBranchAOrientation` are in scope. Conceptually, a minimal extraction might depend on repository modules such as:

```lean
import DkMath.FLT.Five.Basic
import DkMath.FLT.Five.SignedBranchA
```

This is only a conceptual candidate for an isolated declaration. Since the declaration itself lives in `SignedBranchA.lean`, that file cannot import itself. The exact import lines of the split source file were not present in the material retrieved for this run, so the minimal-import discussion is explicitly conjectural.

At file granularity, the preceding congruence arithmetic and the following routing theorem use remainders, `interval_cases`, `norm_num`, and related facilities. Import optimization should therefore measure the whole `SignedBranchA.lean` module rather than this structure alone.

## 11. Comparator challenge suitability

It is suitable for a small API-design challenge.

### Challenge proposal

Package the following two proofs into a propositional structure sharing the same coordinates.

```lean
hPack : CounterexamplePack u v w
hOrientation : SignedBranchAOrientation u v w
```

Requirements:

- place the structure in `Prop`;
- name the fields `pack` and `orientation`;
- construct terms using both constructor notation and named-field notation;
- destruct the structure with `rcases`;
- compare it with plain `And` and explain the advantage of the dedicated structure.

The proof difficulty is low, but the exercise effectively teaches semantic packaging and coordinate consistency through propositional structures.

## 12. Evidence versus conjecture

The declaration name, complete type, two fields, source comment, placement immediately before `signedBranchA_normalForm_of_branchB`, and later storage inside `SignedFiveAdicPacket` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The narrative name used for this structure in the existing PDFs and the exact import lines of the split file `DkMath/FLT/Five/SignedBranchA.lean` were not directly verified in this run. Statements about import minimization are therefore marked as conjectural.

## 13. Next theorem to read

The next declaration is the routing theorem:

```lean
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  ...
```

It classifies a Branch-B candidate modulo five and constructs either the swapped difference-oriented normal form or the original-order sum-oriented normal form. It is the first theorem that fills the container defined in this article with actual arithmetic evidence.
# 0056 — `signedBranchA_normalForm_of_branchB`

## 1. Lean declaration

```lean
/-- Every Branch-B pack is routed into one of the two signed Branch-A orientations. -/
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  have h5x : ¬ 5 ∣ x := five_not_dvd_x_of_branchB hPack hBranch
  rcases five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x hPack.hEq h5x with
    h5y | h5z
  · left
    refine ⟨hPack.swap, ?_⟩
    exact SignedBranchAOrientation.differenceGap h5y
      (five_dvd_z_sub_x_of_fermat5_of_five_dvd_y hPack.hEq h5y)
  · right
    refine ⟨hPack, ?_⟩
    exact SignedBranchAOrientation.sumGap h5z
      (five_dvd_x_add_y_of_fermat5_of_five_dvd_z hPack.hEq h5z)
```

## 2. Lean type

```lean
{x y z : ℕ} →
CounterexamplePack x y z →
(¬ 5 ∣ z - y) →
SignedBranchANormalForm y x z ∨
  SignedBranchANormalForm x y z
```

Given a positive primitive FLT5 candidate `hPack` and the Branch B condition `5 ∤ z - y`, the theorem returns either a difference-gap normal form after swapping the left coordinates, or a sum-gap normal form in the original coordinate order.

## 3. Mathematical statement

`CounterexamplePack x y z` contains, in particular,

$$
x^5+y^5=z^5,
\qquad
x,y,z>0,
\qquad
\gcd(x,y)=1.
$$

Assume in addition the Branch B condition

$$
5\nmid(z-y).
$$

Article 0048 gives

$$
5\nmid x,
$$

and article 0055 then yields

$$
5\mid y
\quad\text{or}\quad
5\mid z.
$$

In the first case, article 0050 gives

$$
5\mid(z-x).
$$

After swapping the left coordinates and setting $(u,v,w)=(y,x,z)$, this becomes

$$
5\mid u,
\qquad
5\mid(w-v),
$$

which is the `differenceGap` orientation.

In the second case, article 0051 gives

$$
5\mid(x+y).
$$

Keeping $(u,v,w)=(x,y,z)$, we obtain

$$
5\mid w,
\qquad
5\mid(u+v),
$$

which is the `sumGap` orientation.

Thus every Branch B candidate is routed into one of the two normal forms accepted by the signed five-adic descent.

## 4. Role in the full proof

This theorem is the convergence point of the first half of `SignedBranchA.lean`. The earlier lemmas extract the five-adic exceptional geometry from Branch B; this theorem packages those facts into the interface consumed by later descent layers.

```text
CounterexamplePack x y z
       +
5 ∤ (z - y)
       ↓ 0048
     5 ∤ x
       ↓ 0055
  5 ∣ y  ∨  5 ∣ z
    ↓             ↓
  0050          0051
5 ∣ z-x       5 ∣ x+y
    ↓             ↓
 swap          keep
    ↓             ↓
differenceGap   sumGap
      \          /
       \        /
 SignedBranchANormalForm
```

The key design gain is that the downstream five-adic development no longer needs to know how the normal form arose from Branch B. It only receives `SignedBranchANormalForm u v w` and may case-split on the two semantic constructors `differenceGap` and `sumGap`.

Accordingly, this theorem is a normalization/routing bridge between the coordinate-specific front end and the common signed five-adic descent.

## 5. Direct dependencies

Repository-local direct dependencies are:

- `CounterexamplePack`
- `CounterexamplePack.swap` — 0046
- `five_not_dvd_x_of_branchB` — 0048
- `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y` — 0050
- `five_dvd_x_add_y_of_fermat5_of_five_dvd_z` — 0051
- `SignedBranchAOrientation` — 0052
- `SignedBranchANormalForm` — 0053
- `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x` — 0055

On the Lean/Mathlib side, the proof mainly uses `rcases`, `Or`, `left`, `right`, `refine`, and structure construction `⟨..., ...⟩`.

The theorem performs no new number-theoretic computation. All arithmetic has already been isolated into 0048, 0050, 0051, and 0055; this proof is purely logical routing and repackaging.

## 6. Proof flow

1. Apply `five_not_dvd_x_of_branchB hPack hBranch` to obtain `h5x : ¬ 5 ∣ x`.
2. Apply `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x hPack.hEq h5x` and split into `h5y : 5 ∣ y` or `h5z : 5 ∣ z`.
3. In the `h5y` branch, choose the left side of the target disjunction.
4. Replace the pack by `hPack.swap : CounterexamplePack y x z`.
5. Use article 0050 to obtain `5 ∣ z - x`, then construct `SignedBranchAOrientation.differenceGap h5y ...`.
6. Pair the swapped pack and the orientation to obtain `SignedBranchANormalForm y x z`.
7. In the `h5z` branch, choose the right side of the target disjunction.
8. Keep the original `hPack`.
9. Use article 0051 to obtain `5 ∣ x + y`, then construct `SignedBranchAOrientation.sumGap h5z ...`.
10. Pair the original pack and the orientation to obtain `SignedBranchANormalForm x y z`.

The arithmetic content has therefore already been discharged; this theorem normalizes its consequences into the expected type.

## 7. Lean-specific processing

### 7.1 `rcases ... with h5y | h5z`

Article 0055 returns the disjunction `5 ∣ y ∨ 5 ∣ z`, so `rcases` turns the mathematical case split directly into two proof-state branches.

### 7.2 `left` / `right`

The target is itself a disjunction:

```lean
SignedBranchANormalForm y x z ∨
SignedBranchANormalForm x y z
```

Hence the input case split matches the output disjunction one-for-one.

### 7.3 `refine ⟨hPack.swap, ?_⟩`

`SignedBranchANormalForm` is defined by

```lean
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

so the first field is filled with the swapped pack and the second field is left as a subgoal. The swap is necessary in the difference-gap branch because `differenceGap` requires the coordinate divisible by five to occupy the first slot.

### 7.4 The type checker verifies the coordinate swap

After using `hPack.swap`, the pack has type `CounterexamplePack y x z`. The following orientation must therefore have type `SignedBranchAOrientation y x z`. Lean checks the coordinate bookkeeping automatically, preventing the common paper-proof error of silently interchanging $x$ and $y$ inconsistently.

## 8. Redundancy and duplication

The proof is short and contains very little real redundancy.

Both branches have the same abstract shape:

```text
choose a disjunct
→ provide a pack
→ provide an orientation
```

but only the difference branch requires `swap`, and the two branches use different orientation constructors. Factoring them into a common combinator would probably reduce readability more than code size.

`hPack.hEq` is passed to two downstream lemmas, but introducing a local alias would not materially simplify the proof.

## 9. Optimization candidates

1. The current proof is already compact, so local proof-script optimization has low priority.
2. If the common “reduce the Fermat equation modulo five” core of 0050 and 0051 were abstracted earlier, this theorem could depend on more semantic routing lemmas and less arithmetic detail.
3. `SignedBranchAOrientation` and `SignedBranchANormalForm` could in principle be merged into one inductive packet, but keeping the pack separate from the orientation gives the downstream API better reuse and projection structure.
4. Another possible design is a single existential normal form carrying an explicit coordinate permutation. That may reduce the outer `Or`, but it would make the mathematically meaningful difference/sum distinction less explicit.

The present design therefore favors an explicit two-entry descent interface over minimal line count.

## 10. Required Mathlib imports and import optimization

The generated branch artifact `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the whole development.

This theorem itself uses no heavy arithmetic tactic directly; it is essentially a composition of repository-local lemmas plus core logical syntax. Consequently, its own incremental Mathlib requirements are very small.

However, the source module `SignedBranchA.lean` also contains the preceding `Fin 25` residue argument, modular arithmetic, `norm_num`, and finite decision machinery. Therefore the minimal import set for the file cannot be inferred from this theorem alone.

A plausible import optimization is to split `SignedBranchA.lean` into a finite-residue arithmetic module and a routing/normal-form packaging module, with the latter importing only the public arithmetic lemmas. This is a design suggestion, not a build-verified minimal-import result.

## 11. Comparator challenge suitability

Suitable, especially as a type-design and routing challenge rather than a difficult arithmetic challenge.

### Challenge idea

Prove the same Branch B routing statement in two styles:

- Solution A: the current explicit `5 ∣ y ∨ 5 ∣ z` case split, constructing `differenceGap` and `sumGap` directly.
- Solution B: introduce a dedicated routing lemma that internalizes the residue split and make the final theorem nearly a one-line composition.

Useful comparison criteria include dependency transparency, resistance to coordinate-swap mistakes, quality of error messages, proof-term simplicity, and downstream API ergonomics.

A second challenge is to replace the `Or` result by a single existential normal form carrying a permutation and compare whether later proofs become simpler or less transparent.

## 12. Evidence versus inference

The declaration name, complete type, proof body, direct calls to 0048/0050/0051/0055, the use of `hPack.swap`, and the immediately following declarations `SignedBranchARefuter` and `branchB_false_of_signedBranchARefuter` were verified in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

The existing museum catalogue also explicitly named this theorem as the item following 0055.

The repository contains Japanese and English PDF exposition as supporting narrative material. The exact PDF section/page corresponding to this declaration was not extracted in this run, so no PDF-specific wording or page claim is inferred here.

The proposed minimal-import/module-splitting ideas are design inferences because no import-reduction build was performed.

## 13. Next declaration to read

The next unexplained declaration is the abbreviation defining the contract expected from all later signed normal-form refuters:

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

Immediately after it comes the theorem that combines this contract with the routing theorem from the present article:

```lean
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False
```

To preserve strict declaration-by-declaration dependency order, the natural next article is `SignedBranchARefuter`.
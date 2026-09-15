# 0351 — `goldenUnit_phiInv`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

## Lean type

```lean
goldenUnit_phiInv : GoldenUnit goldenPhiInv
```

Here `goldenPhiInv : GoldenInt` is the golden integer introduced in 0348:

```lean
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

Mathematically, it represents $\varphi-1=\varphi^{-1}$.

`GoldenUnit epsilon` is the proposition asserting that a golden integer `epsilon : GoldenInt` has a two-sided inverse. The form used by the existing code is

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

Therefore, the type of this theorem states that such an inverse witness exists for `goldenPhiInv`.

## Mathematical statement

By 0348–0350, the development has established

$$
goldenPhiInv=\varphi-1
$$

and the two concrete `GoldenInt` identities

$$
\varphi(\varphi-1)=1,
\qquad
(\varphi-1)\varphi=1.
$$

This theorem chooses

$$
\eta=\varphi
$$

as the inverse witness. Then both

$$
(\varphi-1)\eta=1
$$

and

$$
\eta(\varphi-1)=1
$$

hold, so $\varphi-1$ is a `GoldenUnit`.

Mathematically, the declaration records

$$
\varphi^{-1}\in \mathbb Z[\varphi]^\times
$$

as an explicit certificate in the project-specific `GoldenUnit` interface.

## Role in the overall proof

At the start of `GoldenUnitClassification`, the development first constructs the inverse of $\varphi$ entirely inside the coordinate model, because the subsequent unit descent needs multiplication both by $\varphi$ and by its integral inverse.

The dependency flow is

```text
goldenPhiInv
  ├─ golden_phi_mul_inv
  └─ golden_inv_mul_phi
          ↓
     goldenUnit_phiInv
          ↓
     goldenUnit_descent
          ↓
 goldenUnitFifthClass_of_unit
          ↓
 goldenUnitClassesModFifth
```

0348 `goldenPhiInv` is only a concrete `GoldenInt` value; by itself it does not carry the logical fact that it is a unit. Declarations 0349 and 0350 prove the two inverse laws, and this theorem packages those facts into a `GoldenUnit` existence certificate.

Later, `goldenUnit_descent` constructs candidates such as

```lean
let y := goldenMul x goldenPhiInv
```

and proves that the result remains a unit by using

```lean
goldenUnit_mul hx goldenUnit_phiInv
```

Hence this theorem directly guarantees that the descent map stays inside the set of golden units.

## Direct dependencies

The theorem directly refers to the following project declarations.

- `GoldenUnit` — the proposition that a golden integer has a two-sided inverse.
- `goldenPhiInv` — 0348, the golden integer `⟨-1,1⟩` representing $\varphi-1$.
- `goldenPhi` — the golden integer representing $\varphi$.
- `golden_inv_mul_phi` — 0350:
  ```lean
  goldenMul goldenPhiInv goldenPhi = goldenOne
  ```
- `golden_phi_mul_inv` — 0349:
  ```lean
  goldenMul goldenPhi goldenPhiInv = goldenOne
  ```

The witness for `GoldenUnit` is `goldenPhi` itself. No new arithmetic computation is performed in this theorem.

## Proof / construction flow

The proof is a one-line constructor term:

```lean
exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

Expanding `GoldenUnit goldenPhiInv` conceptually, the goal is

```lean
∃ eta : GoldenInt,
  goldenMul goldenPhiInv eta = goldenOne ∧
  goldenMul eta goldenPhiInv = goldenOne
```

The theorem supplies the three required pieces in order:

1. `eta := goldenPhi`
2. `golden_inv_mul_phi`
3. `golden_phi_mul_inv`

In other words:

```text
witness          : goldenPhi
left inverse law : goldenPhiInv * goldenPhi = 1
right inverse law: goldenPhi * goldenPhiInv = 1
```

These are packed directly into the existential/conjunction structure.

## Lean-specific details

### Using `⟨...⟩` to build both the existential and the conjunction

In Lean,

```lean
⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

constructs the nested `Exists.intro` and `And.intro` in one compact expression.

Conceptually, it corresponds to

```lean
Exists.intro goldenPhi
  (And.intro golden_inv_mul_phi golden_phi_mul_inv)
```

There is no proof search here; the theorem simply places already-proved terms into the slots required by the target proposition.

### The order of the two inverse laws matters

The target is `GoldenUnit goldenPhiInv`, so `epsilon = goldenPhiInv` and the chosen witness is `eta = goldenPhi`.

Therefore the first required equality is

```lean
goldenMul goldenPhiInv goldenPhi = goldenOne
```

which is exactly 0350 `golden_inv_mul_phi`.

The second is

```lean
goldenMul goldenPhi goldenPhiInv = goldenOne
```

which is 0349 `golden_phi_mul_inv`.

Mathematically the ring is commutative, but the proof terms still have to match the field/order expected by the proposition exactly.

### A proof-term-oriented interface theorem

The declaration does not use `refine`, `constructor`, or `use` to decompose the goal. Instead it provides a complete proof term to `exact`. This makes the theorem a very local interface layer: downstream code can use the single certificate `goldenUnit_phiInv` without reopening the two inverse-law proofs.

## Redundancy and duplication

The theorem itself contains essentially no redundancy. Its sole job is to combine the two closed computations from 0349 and 0350 into a single `GoldenUnit` certificate.

Mathematically, commutativity implies that one inverse law could be derived from the other, so there is duplication in keeping both 0349 and 0350 as independent theorems. From the viewpoint of this declaration, however, the definition of `GoldenUnit` explicitly asks for both directions, and supplying the two existing lemmas is the most direct implementation.

If the project were redesigned around Mathlib's standard `IsUnit` / `Units` API for a commutative ring, some explicit two-sided certificate structure might become unnecessary. That would be an API-level redesign, not a local optimization of this theorem.

## Optimization candidates

The current proof

```lean
by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

is already extremely short.

Possible refinements include:

1. Switch to pure term style:
   ```lean
   theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv :=
     ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
   ```
2. If a bridge between `GoldenUnit` and Mathlib's `IsUnit` / `Units` becomes useful downstream, reduce duplication between the custom unit certificate and the standard unit API.
3. Derive one of 0349/0350 from commutativity instead of maintaining both as independent closed computations.
4. Keep `goldenUnit_phiInv` explicitly as a unit-closure lemma rather than treating it as a simplification rule; the proposition itself is not naturally a `[simp]` rewrite lemma.

Candidate 1 is purely syntactic. Candidates 2 and 3 should be judged against the wider dependency graph and downstream API usage.

## Required Mathlib imports and import optimization candidates

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the complete development.

This theorem itself does not directly invoke arithmetic tactics from Mathlib. Its proof requires mainly

- the basic logical structures `Exists` and `And`,
- the project APIs `GoldenInt` and `GoldenUnit`,
- the already-proved theorems 0349 and 0350.

So the proof term itself is far lighter than importing all of `Mathlib`. However, the exact minimal Mathlib import set depends on the modules defining `GoldenInt`, `GoldenUnit`, `goldenMul`, and the ring instances they rely on.

Because no Lean build is performed in this task, a finer-grained minimal import set is **not verified**.

## Comparator challenge suitability

**Suitable; difficulty: beginner.**

A minimal challenge is

```lean
example : GoldenUnit goldenPhiInv := by
  ?_
```

with

```lean
golden_inv_mul_phi
golden_phi_mul_inv
```

available as lemmas. The solver must read the existential/conjunction shape of `GoldenUnit`, choose `goldenPhi` as the witness, and place the two inverse laws in the correct order.

The expected shortest solution is

```lean
exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

The challenge tests

- understanding the constructor shape of a proposition,
- selecting an existential witness,
- distinguishing the directions of the two inverse lemmas,
- reusing existing proof terms.

If 0349 and 0350 were hidden and the solver had to reconstruct them from coordinates, that would become a different challenge. For this theorem itself, a small proof-composition task is the natural Comparator form.

## Next declaration to read

The next declaration is **0352 `golden_mul_phi_coords`**, of kind **`theorem`**.

```lean
theorem golden_mul_phi_coords (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ext <;> simp [goldenMul, goldenPhi]
```

By 0351, `goldenPhiInv` has been promoted to a certified unit. Declaration 0352 now begins the **coordinate transformation laws** needed for the unit descent.

Mathematically,

$$
(a+b\varphi)\varphi
=b+(a+b)\varphi,
$$

so the coordinate transformation is

$$
(a,b)\longmapsto(b,a+b).
$$

Together with the following `golden_mul_phiInv_coords`, this provides the computational basis for `goldenUnit_descent`, which chooses a direction that strictly decreases the coordinate measure

$$
|a|+|b|.
$$

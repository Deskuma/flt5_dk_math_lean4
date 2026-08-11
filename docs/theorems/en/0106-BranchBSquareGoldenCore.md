# 0106 — `BranchBSquareGoldenCore`

## Lean type

```lean
/-- The narrowed receiver after both fifth-power and square-golden reduction. -/
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

## Mathematical statement

`BranchBSquareGoldenCore` is not an ordinary theorem proving a numerical identity. It is the **type of a contradiction receiver**: whenever it is given a Branch-B square/golden normal-form packet, it must return `False`.

Mathematically, it requires uniformly for all natural numbers $x,y,z,a,b$ that

$$
\operatorname{BranchBSquareGoldenNormalForm}(x,y,z,a,b)
\longrightarrow \bot.
$$

Expanding the packet stored by 0104 `BranchBSquareGoldenNormalForm`, one has the original Branch-B fifth-power normal form together with

$$
M=z^2+y^2,\qquad N=zy,
$$

$$
\operatorname{GoldenNorm}(M,N)=b^5,
$$

$$
M-2N=a^{10},
$$

$$
M^2-4N^2=(z^2-y^2)^2,
$$

$$
(2M+N)^2-5N^2=4b^5.
$$

Thus `BranchBSquareGoldenCore` is the **contract for the final contradiction core** that must prove that no packet satisfying these invariants can exist.

## Role in the whole proof

Up through 0105 `exists_branchB_squareGoldenNormalForm`, the proof is on the **construction side**: starting from the Branch-B assumptions, it builds witnesses $a,b$ and a square/golden packet.

At this declaration the proof architecture reverses direction.

$$
\text{Branch-B candidate}
\longrightarrow
\text{square/golden packet}
\longrightarrow
\text{BranchBSquareGoldenCore}
\longrightarrow
\bot.
$$

All arithmetic, casts, and coordinate conversions from the first half are therefore sealed behind 0105. The second half only needs to receive a single `BranchBSquareGoldenNormalForm` and derive a contradiction.

From a proof-engineering perspective this is a **reduction boundary**: the Branch-B proof is separated into construction of a normal form and elimination of that normal form.

## Direct definitions and lemmas depended on

The only directly referenced project-local declaration is 0104 `BranchBSquareGoldenNormalForm`.

```lean
BranchBSquareGoldenNormalForm x y z a b → False
```

is the entire contract. The declaration itself does not directly mention 0097, 0099, 0102, 0103, or 0105.

Semantically, however, the fields of 0104 are supplied by those earlier results and 0105 constructs an inhabitant of the packet. Thus, in the dependency graph, this core receives the whole preceding square/golden bridge through 0104.

## Proof flow

Because this is an `abbrev`, there is no proof script. Lean merely assigns the short name `BranchBSquareGoldenCore` to the proposition

```lean
∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

The following theorem then uses this name as the actual consumer interface.

```lean
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

0105 produces the packet; this core rejects the packet; Branch B is therefore closed.

## Lean-specific processing

### 1. Transparent naming with `abbrev`

The declaration uses `abbrev` rather than `def`, so `BranchBSquareGoldenCore` is a reducible alias. Lean can readily unfold it to

```lean
∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

when needed.

Here the purpose is not computational abstraction but giving a meaningful name to a long higher-order proposition, so `abbrev` is a natural choice.

### 2. Implicit binders make the receiver witness-independent

All variables are implicit:

```lean
∀ {x y z a b : ℕ}, ...
```

A consumer therefore does not need to pass the concrete values $x,y,z,a,b$ explicitly; Lean can infer them from the packet `hNF`.

That design is what makes the downstream line

```lean
exact hCore hNF
```

possible.

### 3. A contradiction core as a function returning `False`

In Lean, the negation of a proposition $P$ is `P → False`. This core is not the negation of one fixed packet but a polymorphic refuter that supplies such a negation for every choice of witnesses.

## Redundancy and duplication

### Same proof-interface pattern as `BranchBFifthPowerCore`

An earlier phase has the analogous interface

```lean
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBFifthPowerNormalForm x y z a b → False
```

The present declaration is the same architectural pattern specialized to `BranchBSquareGoldenNormalForm`.

This is intentional repetition rather than harmful duplication. Each reduction phase ends with an explicit boundary saying, in effect, “from here onward only this packet matters.”

### `∀ ... → False` corresponds logically to `¬ ∃ ...`

Mathematically,

$$
\forall x,y,z,a,b,\ P(x,y,z,a,b)\to\bot
$$

corresponds to

$$
\neg\exists x,y,z,a,b,\ P(x,y,z,a,b).
$$

So the interface could instead be expressed as an existential nonexistence theorem.

For downstream Lean code, however, the current form is more direct: once a packet has been obtained, one can immediately write `hCore hNF`.

## Optimization candidates

### Candidate A — generic packet-refuter alias

Because several normal-form cores have the same shape, one could consider an abstraction such as

```lean
abbrev Refuter (P : α → Prop) : Prop := ∀ x, P x → False
```

The current core, however, has several implicit witnesses inside a dependent proposition, so generic abstraction would require tuple or structure packaging. The present API has the advantage that the proof phase is immediately visible from its name.

### Candidate B — compare against a `¬ ∃ ...` formulation

One could define instead

```lean
¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

which is logically equivalent. But the downstream theorem would then need to repackage the witnesses existentially.

The current function form connects directly to the packet produced by 0105 and therefore gives the shorter consumer-side proof.

### Candidate C — internalize the witnesses in a packet structure

If an existential packet structure stored $x,y,z,a,b$ as fields rather than leaving them as parameters of `BranchBSquareGoldenNormalForm`, the core could be reduced to

```lean
SquareGoldenPacket → False
```

On the other hand, the current parameterized structure exposes the witnesses in theorem statements and makes rewriting against the existing arithmetic API straightforward. This is an API-design trade-off rather than a simple shortening opportunity.

## Required Mathlib imports and import optimization candidates

This declaration alone uses only `Prop`, universal quantification, `False`, natural numbers, and an existing project-local structure. It requires no tactic at all.

Therefore `BranchBSquareGoldenCore` itself does not justify a broad Mathlib import. Its actual import requirement is whatever project-local module provides `BranchBSquareGoldenNormalForm`.

The standalone artifact uses `import Mathlib` globally, but this individual declaration could clearly live under much narrower imports.

A practical module-level optimization would be to make explicit only the imports required by `SquareGoldenNormalForm.lean` for tactics such as `ring`, `exact_mod_cast`, and `simpa`, together with the previous project modules. No Lean build is run in the museum workflow, so the exact minimal import set is recorded only as a candidate rather than asserted.

## Comparator challenge suitability

**Suitable**, but primarily as a proof-interface design challenge rather than an algebraic proof challenge.

Three designs are natural to compare:

```lean
-- A: current function core
abbrev CoreA : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False

-- B: existential nonexistence
abbrev CoreB : Prop :=
  ¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b

-- C: package the witnesses into one existential packet and refute that packet
-- abbrev CoreC : Prop := ExistentialSquareGoldenPacket → False
```

Useful comparison criteria are downstream theorem size, witness inference, ease of rewriting, clarity of error messages, and ease of later generalization.

The present design A is particularly strong on consumer-side brevity because it permits `exact hCore hNF`.

## Correspondence with existing materials

The formal source of truth is the `DkMath/FLT/Five/SquareGoldenNormalForm.lean` generated section contained in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum` branch.

Existing Japanese and English PDFs are treated as narrative context according to the museum policy. During this run, GitHub connector code search returned an upstream error, so the specific PDF page or section containing the corresponding discussion could not be verified. No page or section number has therefore been guessed.

## Next theorem to read

The immediately following theorem is

```lean
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

0105 constructs a packet from Branch B, and 0106 defines the abstract receiver that rejects such a packet. The next theorem connects those two pieces in two lines and closes Branch B.

Thus the natural next article should examine the final interface composition

$$
\text{existence of packet}
+\text{universal packet refuter}
\Longrightarrow \bot.
$$

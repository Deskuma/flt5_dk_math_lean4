# 0246 — `signedGoldenConjugateCoprimePacket_of_stripped`

## Lean type

```lean
/-- Construct the conjugate-coprime packet without any choice. -/
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

This is a `def`, not a theorem. It takes a `SignedGoldenRamifierStrippedPacket` constructed in 0231, attaches the relative-primality result for `beta` and its conjugate proved in 0244, and constructs a value of the 0245 structure `SignedGoldenConjugateCoprimePacket`.

## Mathematical statement and meaning of the declaration

The input `p` is the stripped state obtained after removing the visible ramifier `tau` once. Conceptually it carries certificates such as

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
\qquad
\tau\nmid\beta.
$$

Declaration 0244 additionally proves

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta}),
$$

meaning that every common divisor of `beta` and `goldenConj beta` is a `GoldenUnit`.

The present definition stores that already-established fact in the `relPrime` field of

```lean
SignedGoldenConjugateCoprimePacket.
```

It therefore proves no new number-theoretic fact. Instead, it realizes the proof-state refinement

$$
\text{ramifier-stripped state}
\longrightarrow
\text{conjugate-coprime certified state}
$$

as the canonical producer of the certified packet type.

## Role in the full proof

In the exceptional FLT5 branch, knowing only that

$$
N(\beta)=b^5
$$

does not by itself imply that `beta` is a fifth power up to a unit. One first needs relative primality of `beta` and its conjugate so that Euclidean-domain / gcd / factor-splitting arguments can be applied.

Declarations 0241–0244 build that arithmetic layer:

- 0241 factors `beta - conj beta` in the `sqrtFive` direction;
- 0242 computes the norm of that difference as `-5 * snd^2`;
- 0243 substitutes the stripped packet's exact coordinates and obtains the precise five-adic mass;
- 0244 constrains the norm of any common divisor by two coprime integer quantities and concludes that the common divisor is a unit;
- 0245 packages the stripped packet together with this relative-primality certificate;
- 0246, the present definition, upgrades any stripped packet to that certified structure in the canonical way.

Consequently, the downstream fifth-power extraction layer does not need to rerun the long divisibility argument from 0244. It can accept `SignedGoldenConjugateCoprimePacket` as input and begin from the invariant that conjugate relative primality has already been established.

## Direct dependencies

The direct dependencies are:

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`
- 0245 `SignedGoldenConjugateCoprimePacket`

The 0245 structure is conceptually

```lean
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

so the present construction is simply

$$
p
\mapsto
\bigl(p,\;p.\mathrm{beta\_relPrime\_conj}\bigr).
$$

`GoldenRelPrime`, `GoldenUnit`, `goldenConj`, and the norm information on `beta` occur transitively through the target structure and 0244, but this definition does not recompute or reprove any of them.

## Construction flow

The body is a single constructor expression:

```lean
⟨p, p.beta_relPrime_conj⟩
```

1. Put the input `p` directly into the first field `stripped`.
2. Fill the second field `relPrime` with the theorem from 0244 through dot notation, `p.beta_relPrime_conj`.
3. Both fields of `SignedGoldenConjugateCoprimePacket u v w` are now populated.

Mathematically, this adds no new argument; it attaches an already-proved invariant to the data.

## Lean-specific processing

### 1. Construction of a dependent field

The second field of `SignedGoldenConjugateCoprimePacket` is

```lean
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

and therefore depends on the first field `stripped`.

In

```lean
⟨p, p.beta_relPrime_conj⟩
```

Lean first fixes the first field to `p`. The expected type of the second field then specializes to

```lean
GoldenRelPrime p.beta (goldenConj p.beta),
```

which is exactly the type provided by 0244.

### 2. Dot notation

```lean
p.beta_relPrime_conj
```

is dot notation for the namespaced theorem

```lean
SignedGoldenRamifierStrippedPacket.beta_relPrime_conj p.
```

It is not a structure field. Lean can nevertheless use the first explicit argument's type to expose the theorem in method-like syntax.

### 3. A choice-free ordinary `def`

The source comment explicitly says `without any choice`. Unlike declarations such as 0234 that obtain a packet through `Classical.choice`, the present definition receives a concrete packet `p`, and the proof term from 0244 is already determined. It can therefore be an ordinary `def` rather than a `noncomputable def`.

This is an important boundary in the implementation: classical choice may occur upstream in producing some stripped packet, but the certification upgrade itself requires no new choice.

## Redundancy and duplication

Logically, 0244 proves conjugate relative primality for **every** `SignedGoldenRamifierStrippedPacket`. Thus the `relPrime` field of 0245 carries information that can always be reconstructed from the underlying `p`.

In principle, downstream code could simply keep a stripped packet and invoke

```lean
p.beta_relPrime_conj
```

whenever needed. In that sense, both the certified packet layer and this constructor are logically redundant.

The architectural benefits are nevertheless substantial:

- the proof phase is visible in the type name;
- downstream consumers do not need to know the theorem name from 0244;
- “ramifier stripped” and “conjugate coprime certified” states remain distinct API stages;
- the input contract for fifth-power extraction is narrow and explicit;
- the proof of relative primality can later change without forcing packet consumers to change.

The redundancy is therefore intentional proof-state redundancy rather than mathematical duplication without purpose.

## Optimization candidates

1. **Use named fields in the constructor**

```lean
{ stripped := p
  relPrime := p.beta_relPrime_conj }
```

This is more verbose but makes the role of each component explicit and is more robust if the structure gains fields later.

2. **Remove the 0245 certified packet layer**

Because 0244 works for every stripped packet, downstream theorems could accept `SignedGoldenRamifierStrippedPacket` directly and call the relative-primality theorem on demand. This removes an API layer but weakens the explicit phase boundary.

3. **Represent the certified state as a subtype**

Conceptually one could write something like

```lean
{ p : SignedGoldenRamifierStrippedPacket u v w //
  GoldenRelPrime p.beta (goldenConj p.beta) }
```

A named structure may still be more readable for downstream field projection and future extension.

4. **Keep the current smart-constructor split**

The existing design separates 0245, which defines the certified state type, from 0246, which fixes its canonical construction policy. This is already a clean API boundary, so local compression is not especially valuable.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. This definition itself invokes no tactic at all; it only uses project-local declarations and Lean structure construction.

Its direct visible dependencies are essentially:

- `SignedGoldenRamifierStrippedPacket`
- `SignedGoldenConjugateCoprimePacket`
- `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`

Therefore the declaration in isolation almost certainly does not require the whole `Mathlib` import. However, the surrounding `SignedGoldenConjugateCoprime.lean` module uses integer divisibility, norms, conjugation, and relative-primality arguments, so actual import minimization should be measured at module scope.

No Lean build is run in this museum pass, so the exact minimal import set remains unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. This declaration is more interesting as a proof-state packaging comparison than as a theorem-proving challenge.

Useful variants are:

- A: current `structure` plus canonical producer `def`
- B: use stripped packets directly and invoke 0244 on demand
- C: store the certificate in a subtype
- D: keep the current structure but use a named-field smart constructor

Useful comparison axes include:

- downstream proof size
- visibility of the invariant in types
- elaboration simplicity
- coupling to theorem names
- refactoring robustness
- wrapper/API code volume
- ease of proof auditing

The contrast between A and B is particularly useful for measuring the value of storing a logically derivable certificate explicitly in a proof-state type.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this declaration immediately after the 0245 structure:

```lean
/-- Construct the conjugate-coprime packet without any choice. -/
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

The target branch also contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and the English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact page or section corresponding to this one-line architectural constructor was not identified in this pass, so no PDF page reference is inferred. The primary formal evidence here is the Lean source together with the upstream relative-primality theorem 0244.

## Next declaration to read

The next declaration in dependency order is **0247 `signedGoldenConjugateCoprimePacket_of_normalForm`**:

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

Declaration 0246 provides the canonical upgrade from a stripped packet to a conjugate-coprime certified packet. Declaration 0247 moves one level upstream and composes normal-form-to-stripped construction with 0246, providing a facade that reaches the certified state directly from `SignedBranchANormalForm`.
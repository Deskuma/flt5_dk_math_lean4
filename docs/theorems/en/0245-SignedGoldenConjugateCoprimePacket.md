# 0245 — `SignedGoldenConjugateCoprimePacket`

## Lean type

```lean
/-- A packet retaining the stripped data and certified conjugate coprimality. -/
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

This is a `structure`, not a theorem. It packages the ramifier-stripped data carried by 0231 `SignedGoldenRamifierStrippedPacket` together with the conjugate-coprimality certificate proved in 0244.

## Mathematical statement and meaning of the declaration

An inhabitant of this structure is not merely a value `beta`. It is a certified state carrying two pieces of information simultaneously:

1. `stripped` — a packet from which the visible ramified factor `tau` has already been removed.
2. `relPrime` — a proof that the packet's `beta` and `goldenConj beta` are relatively prime in the golden order.

Mathematically, the structure therefore records

$$
\beta \text{ is ramifier-stripped}
$$

and

$$
\gcd(\beta,\overline\beta)\sim 1.
$$

Here `GoldenRelPrime x y` is the Bézout-free formulation saying that every common divisor is a unit. Thus the `relPrime` field represents the certificate

$$
\forall d,\quad d\mid\beta\land d\mid\overline\beta
\Longrightarrow d\text{ is a unit}.
$$

## Role in the full proof

Declarations 0231–0244 establish increasingly strong information about the stripped golden factor `beta` arising from the exceptional branch. In particular, they give

$$
N(\beta)=b^5,
$$

$$
\tau\nmid\beta,
$$

and finally, in 0244,

$$
GoldenRelPrime(\beta,\overline\beta).
$$

Declaration 0245 promotes those results into a packet that downstream code can consume directly.

The source immediately follows this structure by

```lean
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

so instead of repeatedly pairing a stripped packet with theorem 0244, the development constructs a certified state once and passes that object to the later fifth-power extraction layer.

The source then adds a direct constructor from signed normal form and a receiver contract on packets carrying certified conjugate coprimality. Thus 0245 acts as a representation boundary between the local arithmetic proof and the higher-level contradiction/fifth-power pipeline.

## Direct dependencies

The structure type directly depends on:

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0208 `GoldenRelPrime`
- 0163 `goldenConj`

The second field has the dependent type

```lean
GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

and therefore refers to the value stored in the preceding `stripped` field.

Declaration 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` does not occur textually in the structure definition, but it is the producer theorem used immediately afterward to fill the `relPrime` field via

```lean
⟨p, p.beta_relPrime_conj⟩.
```

Conceptually,

$$
\texttt{SignedGoldenRamifierStrippedPacket}
+
\texttt{beta\_relPrime\_conj}
\longrightarrow
\texttt{SignedGoldenConjugateCoprimePacket}.
$$

## Construction flow

There is no proof script in this declaration. Lean defines a new record type with two fields:

```lean
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

When constructing an inhabitant, the `stripped` field is supplied first. That value determines the expected type of the `relPrime` field.

The following source declaration constructs the record as

```lean
⟨p, p.beta_relPrime_conj⟩.
```

After `p` has filled the first field, the second field is expected to have type

```lean
GoldenRelPrime p.beta (goldenConj p.beta),
```

which is exactly theorem 0244 specialized to `p`.

## Lean-specific processing

The key Lean feature is the dependent field

```lean
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta).
```

This is not an independent proposition field: its type depends on the value of the earlier `stripped` field in the same structure.

Therefore, from a packet `p`, downstream code can project

```lean
p.stripped
p.relPrime
```

and the proof certificate is guaranteed by the type system to refer to the same stripped packet data.

This is a standard dependent-record pattern in Lean. It avoids passing a stripped packet and a separately indexed proof as independent arguments and thereby prevents mismatched data/certificate pairs.

Because this is a `structure`, Lean also generates the constructor and projection functions automatically. Since `relPrime` lives in `Prop`, proof irrelevance means that the particular proof term need not be treated as computational data.

## Redundancy and duplication

From a logical-information perspective, 0245 adds little beyond 0231 plus theorem 0244. For every

```lean
p : SignedGoldenRamifierStrippedPacket u v w
```

0244 already provides

```lean
p.beta_relPrime_conj.
```

A downstream development could therefore keep only the stripped packet and invoke 0244 whenever relative primality is needed.

The dedicated certified packet nevertheless has important architectural benefits:

- the fifth-power extraction layer need not know how conjugate coprimality was proved;
- the transition “ramifier stripped” → “ramifier stripped and conjugate-coprime certified” is visible in the type system;
- producer and consumer module boundaries become explicit;
- receiver contracts can accept a single certified state instead of separate data and proof arguments.

Thus the apparent redundancy is intentional state refinement rather than accidental duplication.

## Optimization candidates

1. **Keep the current certified packet**
   - preserves a clear proof-state transition and high auditability.

2. **Remove 0245 and use the stripped packet plus theorem 0244 directly**
   - fewer declarations, but downstream code acquires a direct dependency on the coprimality proof theorem.

3. **Add `relPrime` directly to the 0231 stripped packet**
   - reduces the number of packet types, but merges two distinct proof stages and makes the earlier packet depend on later arithmetic.

4. **Use a generic certified wrapper**
   - a generic record such as `Certified α P` could express the pattern, but for one or a few cases this may be unnecessary abstraction.

5. **Merge this packet with the later fifth-power extraction certificate**
   - a larger packet could also store `beta = epsilon * gamma^5`, but that would erase the useful boundary between coprimality and factor extraction.

The current staged design is particularly suitable for a theorem museum because each major proof milestone is visible as a distinct type.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`, but this structure itself needs very little Mathlib surface area.

Its effective dependencies are only:

- structure and dependent-field machinery;
- `Prop`;
- upstream `SignedGoldenRamifierStrippedPacket`;
- `GoldenRelPrime`;
- `goldenConj`.

No tactic is used by this declaration.

The full `SignedGoldenConjugateCoprime.lean` module, however, includes 0241–0244, which use integer divisibility, `Nat.Coprime`, `omega`, `ring`, casts, and related arithmetic support. Therefore the true minimal import set at module scope is much larger than the needs of 0245 alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. The challenge here concerns representation design rather than proof tactics.

Possible variants are:

- A: current dedicated certified packet;
- B: keep `SignedGoldenRamifierStrippedPacket` and theorem 0244 separately;
- C: merge `relPrime` into the 0231 packet;
- D: use a generic `Certified` wrapper;
- E: merge coprimality and fifth-power-extraction certificates into one larger packet.

Useful comparison axes include:

- number of downstream theorem arguments;
- module dependency depth;
- visibility of proof-state transitions;
- need to reconstruct certificates;
- readability of field projections;
- stability under future refactoring.

The A-versus-B comparison is especially useful for measuring the value of promoting a proved invariant into the type of a certified state.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places this structure immediately after 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`, followed immediately by

```lean
def signedGoldenConjugateCoprimePacket_of_stripped ...
```

The target branch also contains the Japanese PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` and English PDF `docs/pdf/FLT5-main-en-v0-r1.pdf`. The exact PDF page or section corresponding to this structure was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0246 `signedGoldenConjugateCoprimePacket_of_stripped`**:

```lean
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

Declaration 0245 defines the certified-state type; 0246 is the canonical producer that attaches theorem 0244 to any stripped packet and constructs that state without classical choice.
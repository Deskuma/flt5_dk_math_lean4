# 0188 — `goldenDivides_iff_dvd`

## Lean type

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

This is a `theorem` proving that the golden-order-specific divisibility relation `GoldenDivides`, introduced in 0187, is exactly equivalent to Lean / Mathlib's standard divisibility notation `d ∣ x`.

## Mathematical statement

Declaration 0187 defines

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

while standard ring divisibility `d ∣ x` also means the existence of a quotient satisfying

$$
\exists q,\quad x=dq.
$$

Thus the mathematical content of this theorem is

$$
\mathrm{GoldenDivides}(d,x)
\iff
d\mid x.
$$

It guarantees that the local raw API written with `goldenMul` and the Mathlib API written through the `Mul GoldenInt` instance express the same notion of divisibility.

The theorem does not create a new divisibility theory. It is a **representation bridge** allowing the same mathematics to move between two API layers.

## Role in the full proof

`GoldenDivisibility.lean` introduces the domain-specific vocabulary `GoldenDivides` in 0187, but it does not leave that wrapper isolated. By placing 0188 immediately afterward, the development can reuse Mathlib's general divisibility theorems while keeping the FLT5 argument readable in golden-order terminology.

The source immediately continues with

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]

theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

Thus 0188 lets the custom vocabulary inherit reflexivity, transitivity, and closure under subtraction directly from the standard `dvd` API.

Farther downstream, `GoldenCoprimeFactor.lean` uses the same bridge to connect the standard gcd facts

```lean
exact gcd_dvd_left x y
exact gcd_dvd_right x y
```

to the `GoldenRelPrime` interface. In that sense, 0188 is also a long-range bridge between the early explicit-coordinate divisibility layer and the later Euclidean-domain / gcd machinery.

## Direct dependencies

The direct dependencies are:

- 0187 `GoldenDivides`
- `GoldenInt`
- 0124 `goldenMul`
- the `Mul GoldenInt` instance
- Lean / Mathlib's standard `Dvd.dvd`

The proof does not explicitly invoke another named theorem. It destructures existential witnesses on both sides and uses `simpa` to transfer the factorization equality.

Since `goldenMul` is already connected to standard multiplication, the conceptual dependency is

$$
\texttt{GoldenDivides}
+\texttt{Mul GoldenInt}
\longrightarrow
\texttt{goldenDivides\_iff\_dvd}.
$$

## Proof flow

The proof is perfectly symmetric.

```lean
constructor <;> rintro ⟨q, hq⟩
```

splits the equivalence into two implications and extracts, in both directions, the quotient witness `q` together with its factorization equality `hq`.

### `GoldenDivides d x → d ∣ x`

The hypothesis gives

$$
x=goldenMul\ d\ q.
$$

The same `q` is returned as the standard divisibility witness, and

```lean
exact ⟨q, by simpa using hq⟩
```

identifies `goldenMul d q` with standard multiplication `d * q`.

### `d ∣ x → GoldenDivides d x`

Standard divisibility provides a quotient witness of the same shape. The proof returns the same `q` and again uses

```lean
exact ⟨q, by simpa using hq⟩
```

to move back to raw multiplication.

The fact that both directions have identical proof terms is itself evidence that the distinction between the two relations is essentially an API / notation distinction rather than a mathematical one.

## Lean-specific processing

The key Lean mechanisms are `constructor <;> rintro ⟨q, hq⟩` and `simpa`.

`constructor` turns `P ↔ Q` into two goals,

```lean
P → Q
Q → P
```

and `<;>` applies the following `rintro ⟨q, hq⟩` to both goals. Each existential proposition is therefore destructured in the same way.

`simpa using hq` absorbs the representational difference between raw and standard multiplication. Upstream there is also

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

and the `Mul GoldenInt` instance itself is built from `goldenMul`, so this bridge is intentionally very thin.

That thinness is an implementation invariant worth noticing: if conversion between the two divisibility APIs required a substantial proof, it would indicate that the raw and standard multiplication layers had drifted apart.

## Redundancy and duplication

The theorem itself proves that `GoldenDivides` and standard `∣` are logically equivalent, so the API intentionally contains duplication.

The two proof directions are also syntactically identical:

```lean
exact ⟨q, by simpa using hq⟩
```

appears twice. This is small and readable duplication; compressing it further would provide little mathematical benefit.

The larger redundancy lies in the wrapper lemmas that follow, such as `goldenDivides_refl`, `goldenDivides_trans`, and `goldenDivides_sub`. If the development used standard `dvd` everywhere, these wrappers would be unnecessary. Their value is domain readability: the FLT5 proof can remain expressed in golden-order vocabulary even while its algebraic content is delegated to Mathlib.

## Optimization candidates

1. **Keep the current bridge**
   - it provides a single explicit interoperability point between the domain-specific and standard APIs.

2. **Make `GoldenDivides` an abbreviation of standard divisibility**
   - conceptually, `abbrev GoldenDivides d x := d ∣ x` would make this theorem unnecessary;
   - however, it would reduce visibility of the raw `goldenMul` factorization layer.

3. **Reduce the wrapper theorem family**
   - `goldenDivides_refl/trans/sub` could be replaced by direct use of standard Mathlib lemmas;
   - this trades domain-specific theorem names for lower code volume.

4. **Consider marking the bridge as a simp theorem**
   - adding `[simp]` could normalize `GoldenDivides` automatically to standard `dvd`;
   - proposition-level rewriting can become broad, so simp normal forms and proof transparency should be checked before doing so.

The current design is conservative and auditable: the custom wrapper remains explicit, and conversion to standard divisibility occurs only where requested through `rw [goldenDivides_iff_dvd]`.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`.

The surface required by this theorem itself is small:

- `GoldenInt` / `GoldenDivides`
- the standard `Dvd` relation and `∣` notation
- a tactic environment supporting `constructor`, `rintro`, and `simpa`
- the `Mul GoldenInt` instance

The theorem itself does not use `dvd_trans` or `dvd_sub`; those appear in the declarations immediately following it.

Because this museum pass does not run a Lean build, the exact fine-grained Mathlib import set is not verified. It is very likely possible to reduce the global `Mathlib` import to algebraic divisibility plus basic tactic modules, but the precise minimal set remains an optimization candidate rather than a confirmed result.

## Comparator challenge suitability

Yes. The alternatives are especially clear:

- A: current `GoldenDivides` plus `goldenDivides_iff_dvd`
- B: remove `GoldenDivides` and use standard `∣` everywhere
- C: define `GoldenDivides` as an `abbrev` of standard `∣`
- D: keep the current wrapper but mark the bridge `[simp]` for automatic normalization

Useful metrics include:

- downstream theorem size
- simp stability
- auditability of the raw coordinate layer
- interoperability with Mathlib
- proof burden after `EuclideanDomain` / `GCDMonoid` becomes available
- readability of domain semantics from theorem names

The A-versus-B comparison is particularly useful for measuring whether the additional domain-specific API layer pays for itself in proof-audit clarity.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/GoldenDivisibility.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

The source places the declarations consecutively:

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q

theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

and the module header explicitly states that this layer connects the explicit coordinate vocabulary to ordinary commutative-ring divisibility.

The standalone artifact lists `GoldenDivisibility.lean` among its ordered source modules and imports `Mathlib` globally.

The target branch also contains Japanese and English PDFs. The exact page or section corresponding to this bridge theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0189 `goldenDivides_refl`**:

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

Now that 0188 has opened a two-way route between `GoldenDivides` and standard `∣`, 0189 begins the basic custom divisibility API by delegating its laws to Mathlib. Reflexivity comes first, followed by `goldenDivides_trans` and `goldenDivides_sub`.

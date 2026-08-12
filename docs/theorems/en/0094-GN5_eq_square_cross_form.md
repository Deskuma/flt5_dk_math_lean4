# 0094 — `GN5_eq_square_cross_form`

## Lean type

```lean
theorem GN5_eq_square_cross_form (g y : ℕ) :
    GN5 g y =
      (g ^ 2) ^ 2 +
        5 * (g ^ 2) * (y * (g + y)) +
        5 * (y * (g + y)) ^ 2 := by
  unfold GN5
  ring
```

## Mathematical statement

If

$$
\mathrm{GN5}(g,y)
=g^4+5g^3y+10g^2y^2+10gy^3+5y^4,
$$

then this theorem rewrites it as

$$
\mathrm{GN5}(g,y)
=(g^2)^2+5g^2\,y(g+y)+5\bigl(y(g+y)\bigr)^2.
$$

Setting

$$
A=g^2,\qquad B=y(g+y),
$$

the right-hand side becomes the binary quadratic form

$$
A^2+5AB+5B^2.
$$

Thus this is not merely an expansion identity. It compresses the quartic polynomial `GN5` into a quadratic form in two degree-two coordinates.

## Role in the whole proof

Article 0093 introduced the golden-ratio-type quadratic form

$$
N(m,n)=m^2+mn-n^2
$$

as `GoldenNorm`. The present theorem is the first computational stage of the bridge to that target: it reshapes `GN5` into square/cross coordinates before those coordinates are converted into endpoint-square coordinates.

At the proof-graph level, the route is

$$
\mathrm{GN5}(g,y)
\longrightarrow
A^2+5AB+5B^2
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}.
$$

The next theorem, `square_cross_coordinate_change`, supplies

$$
g^2+2y(g+y)=(g+y)^2+y^2,
$$

so the pair built from $A=g^2$ and $B=y(g+y)$ can be reorganized into

$$
m=(g+y)^2+y^2,
\qquad
n=(g+y)y.
$$

## Direct dependencies

The direct dependencies are minimal.

1. `GN5`
2. addition, multiplication, and powers over `ℕ`
3. the `ring` tactic

The only project-local declaration directly referenced is `GN5`.

`GoldenNorm` is semantically relevant to the following bridge, but it is not referenced in this theorem's type or proof body.

## Proof flow

The proof has only two steps.

```lean
unfold GN5
```

exposes the definition

$$
g^4+5g^3y+10g^2y^2+10gy^3+5y^4.
$$

Then

```lean
ring
```

normalizes both sides as polynomial expressions over a commutative semiring and closes the identity.

Expanding the right-hand side by hand gives

$$
(g^2)^2=g^4,
$$

$$
5g^2y(g+y)=5g^3y+5g^2y^2,
$$

$$
5\bigl(y(g+y)\bigr)^2
=5g^2y^2+10gy^3+5y^4,
$$

whose sum is

$$
g^4+5g^3y+10g^2y^2+10gy^3+5y^4.
$$

## Lean-specific processing

### 1. `unfold GN5`

Because `GN5` is an ordinary `def`, the proof explicitly unfolds it before handing the goal to polynomial normalization. This keeps the theorem statement expressed in the semantic name `GN5` while exposing raw algebra only inside the proof.

### 2. `ring`

The identity contains no subtraction, and `ℕ` carries the required commutative-semiring structure, so `ring` applies directly. There is no need to prove distributivity and associativity rewrites manually.

### 3. No coercion annotations yet

Every term remains in `ℕ`, so the `ℕ → ℤ` coercions that become important later in the golden bridge are not needed here. This theorem therefore lies near the end of the purely natural-number side of the bridge.

## Redundancy and overlap

Mathematically this is another normal form for `GN5`, so it belongs to the same family as earlier rewrite lemmas such as

- `GN5_eq_gap_mul_add_five_mul_y_pow_four`,
- `GN5_eq_g_pow_four_add_five_mul`.

The overlap is intentional. Those earlier forms expose divisibility and five-adic structure; this theorem exposes quadratic-coordinate structure. The repeated algebra is therefore better viewed as purpose-specific normal-form duplication rather than accidental redundancy.

## Optimization candidates

### Candidate A — Keep the current theorem

This is the clearest design. It names exactly the intermediate form needed by the later golden bridge.

### Candidate B — Abstract a general quadratic identity

One could introduce a generic helper around

$$
X^2+5XY+5Y^2
$$

and instantiate it with $X=g^2$ and $Y=y(g+y)$.

However, this theorem already closes in one `ring` step, so the abstraction cost would likely exceed the benefit.

### Candidate C — Inline into `GN5_eq_goldenNorm_squareLink`

The later theorem could directly use `unfold GN5 GoldenNorm; ring`, eliminating this declaration.

That would shorten the declaration count but erase the square/cross coordinate layer from the proof graph, reducing auditability and mathematical readability.

### Candidate D — Use `ring_nf`

Replacing `ring` with `ring_nf` is possible, but when the goal is simply to close an equality, `ring` communicates the intention more directly.

## Required Mathlib imports and import optimization

The generated standalone artifact on the target branch uses `import Mathlib`.

For this theorem alone, the requirements are only the definition of `GN5`, the basic semiring structure on natural numbers, and the `ring` tactic. Thus umbrella `Mathlib` is clearly broader than necessary for the isolated declaration.

However, the whole `SquareGoldenBridge.lean` module later uses integer coercions, `push_cast`, `norm_num`, and related machinery. Therefore the minimal module-level import cannot be inferred from this theorem alone.

The original split module import header was not independently verified in this run, and no Lean build was performed as requested, so specific minimal Mathlib module names are not asserted. A safe optimization process would remove imports incrementally while preserving the `ring` and coercion tactic support needed by the full module.

## Comparator challenge suitability

Suitable.

The useful comparison set is:

1. the current `unfold GN5; ring` proof,
2. a rewrite proof composed from earlier `GN5_eq_*` lemmas,
3. a `ring_nf` proof,
4. a design with this theorem removed and its algebra inlined into `GN5_eq_goldenNorm_squareLink`.

The evaluation criteria should include not only proof-term size but also whether the intermediate coordinate system remains visible in theorem names, whether the later golden bridge stays readable, import weight, maintenance cost, and proof-graph auditability.

The current tactic proof is already close to minimal; the more interesting challenge is whether this intermediate theorem should exist as an architectural boundary.

## PDF and source evidence

The formal source of truth is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. It places this theorem immediately after `GoldenNorm` and confirms that the proof is exactly `unfold GN5; ring`.

An attempt to locate the precise corresponding passages in the existing Japanese and English PDFs through GitHub code search again returned an upstream 502 error. Therefore no PDF page numbers, section numbers, or quotations are supplied by inference.

## Next declaration to read

The next declaration in source order is

```lean
theorem square_cross_coordinate_change (g y : ℕ) :
    g ^ 2 + 2 * (y * (g + y)) = (g + y) ^ 2 + y ^ 2 := by
  ring
```

It converts the square/cross linear combination

$$
g^2+2y(g+y)
$$

into the endpoint-square sum

$$
(g+y)^2+y^2.
$$

If 0094 compresses `GN5` into a quadratic form in $(A,B)$, then 0095 will reinterpret those coordinates in the endpoint form suited to the golden norm.
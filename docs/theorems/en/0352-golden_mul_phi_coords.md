# 0352 — `golden_mul_phi_coords`

## Declaration kind

This declaration is a **`theorem`**.

```lean
theorem golden_mul_phi_coords (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ext <;> simp [goldenMul, goldenPhi]
```

## Lean type

```lean
golden_mul_phi_coords
    (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩
```

`GoldenInt` is the coordinate model for elements of the golden integer order $\mathbb Z[\varphi]$. An element is represented as

$$
x=a+b\varphi,
$$

with `x.fst = a` and `x.snd = b`.

`goldenPhi : GoldenInt` is defined by

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

and represents the basis element $\varphi$.

Thus this theorem gives the explicit coordinates obtained when an arbitrary golden integer $a+b\varphi$ is multiplied by $\varphi$.

## Mathematical statement

The golden basis satisfies

$$
\varphi^2=\varphi+1.
$$

Hence

$$
(a+b\varphi)\varphi
=a\varphi+b\varphi^2,
$$

so

$$
(a+b\varphi)\varphi
=b+(a+b)\varphi.
$$

Therefore multiplication by $\varphi$ acts on coordinates as

$$
(a,b)\longmapsto(b,a+b).
$$

The Lean right-hand side

```lean
⟨x.snd, x.fst + x.snd⟩
```

is exactly this coordinate transformation encoded as a `GoldenInt` value.

## Role in the full proof

By 0351 `goldenUnit_phiInv`, the development has established that $\varphi^{-1}=\varphi-1$ is a certified unit. `GoldenUnitClassification` then moves into a descent argument that repeatedly multiplies a unit by $\varphi$ or $\varphi^{-1}$ in a direction that decreases a coordinate measure.

This theorem supplies the coordinate formula for the $\varphi$ direction of that descent.

In the later `goldenUnit_descent`, the source actually constructs

```lean
let y := goldenMul x goldenPhi
```

and then rewrites the measure-comparison goal with

```lean
rw [golden_mul_phi_coords]
```

before discharging integer absolute-value inequalities.

The dependency flow is therefore approximately

```text
goldenMul + goldenPhi
        ↓
golden_mul_phi_coords
        ↓
goldenUnit_descent
        ↓
goldenUnitFifthClass_of_unit
        ↓
goldenUnitClassesModFifth
```

So 0352 is not merely a convenience expansion. It is the computational interface that turns multiplication in the golden order into explicit integer-coordinate inequalities used by the finite descent underlying the unit classification.

## Direct dependencies

The principal declarations referenced directly by this theorem are:

- `GoldenInt` — the type representing golden integers by two integer coordinates.
- `goldenPhi` — the basis element $\varphi$, defined as `⟨0,1⟩`.
- `goldenMul` — multiplication in the golden order after reducing by $\varphi^2=\varphi+1$.

The multiplication definition is

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

Substituting `y = goldenPhi = ⟨0,1⟩`, the first coordinate becomes

$$
a\cdot0+b\cdot1=b,
$$

while the second coordinate becomes

$$
a\cdot1+b\cdot0+b\cdot1=a+b.
$$

This yields exactly the theorem's right-hand side.

No separate number-theoretic lemma is used in the proof body; definition unfolding and elementary simplification of integer arithmetic are sufficient.

## Proof flow

The proof is a one-line coordinate calculation:

```lean
by
  ext <;> simp [goldenMul, goldenPhi]
```

Its steps are:

1. `ext` reduces equality of two `GoldenInt` values to equality of their coordinates.
2. `<;>` applies the following tactic to every generated coordinate goal.
3. `simp [goldenMul, goldenPhi]` unfolds multiplication and the basis element $\varphi$.
4. Simplification of integer arithmetic with $0$ and $1$ reduces both coordinate goals to reflexive equalities.

Conceptually, Lean proves

```text
fst coordinate:
  a * 0 + b * 1 = b

snd coordinate:
  a * 1 + b * 0 + b * 1 = a + b
```

and nothing deeper is hidden in this theorem.

## Lean-specific processing

### Structure equality via `ext`

Because `GoldenInt` is a coordinate structure, the command

```lean
ext
```

can reduce equality of structures to fieldwise goals of the form

```lean
lhs.fst = rhs.fst
lhs.snd = rhs.snd
```

For this theorem, direct coordinate extensionality is substantially simpler than introducing any abstract ring equivalence.

### Applying one tactic to all subgoals with `<;>`

In

```lean
ext <;> simp [...]
```

`<;>` applies the following `simp` command to every goal produced by `ext`. Since both coordinates are solved by the same unfolding and simplification, this is a compact and natural proof pattern.

### Closed coordinate simplification with `simp`

The simplifier is not searching for a new mathematical fact. It only unfolds `goldenMul` and `goldenPhi` and simplifies elementary integer arithmetic involving $0$ and $1$.

The real mathematical content is therefore already encoded in the coordinate definition of `goldenMul`.

## Redundancy and duplication

There is essentially no local redundancy in this theorem itself.

The following declaration is its natural companion:

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ...
```

Together they describe the two coordinate transformations used by the unit descent. Mathematically, the pair could be organized as matrix actions. For example,

$$
M_\varphi=
\begin{pmatrix}
0&1\\
1&1
\end{pmatrix}
$$

and

$$
M_{\varphi^{-1}}=
\begin{pmatrix}
-1&1\\
1&0
\end{pmatrix}.
$$

This would unify the two coordinate theorems conceptually. However, the current downstream proof needs explicit coordinates immediately for `omega` and `natAbs` inequalities. Introducing matrices could therefore make the formal proof heavier rather than shorter. This is a possible abstraction direction, not an obvious local optimization.

## Optimization candidates

The existing proof is already very small. Possible refinements are:

1. If the simplification API around `goldenMul` is strengthened, the explicit unfolding list might be shortened.
2. Registering this theorem as a `[simp]` lemma could remove some explicit downstream `rw [golden_mul_phi_coords]` calls.
3. That `[simp]` choice would also force `goldenMul x goldenPhi` toward an explicit coordinate constructor, which may be undesirable in proofs that want to preserve the abstract multiplication form.
4. This theorem and `golden_mul_phiInv_coords` could be grouped into a small API for the coordinate action of the unit generators.

Option 2 is therefore not automatically an improvement: it changes the simplifier's normal form and should be evaluated against the complete downstream proof before adoption.

## Required Mathlib imports and import optimization

The generated standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

for the development as a whole.

This theorem itself directly needs only a fairly small collection of facilities:

- structure extensionality used by `ext`;
- the simplifier `simp`;
- basic simp lemmas for integer addition, multiplication, $0$, and $1$;
- the earlier project definitions `GoldenInt`, `goldenMul`, and `goldenPhi`.

It does not use `ring`, `omega`, or `norm_num`.

Therefore the theorem in isolation almost certainly does not require all of `Mathlib`. However, the exact minimal import must also account for the module defining `GoldenInt`, its integer-ring infrastructure, the generated extensionality theorem, and the project's module boundaries. Without a Lean build, the exact minimal Mathlib import set is **not verified**.

No build is performed in this run, so a concrete minimal import list is left unconfirmed.

## Suitability as a Comparator challenge

**Suitable; difficulty: beginner to lower-intermediate.**

A direct challenge is

```lean
example (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ?_
```

with `goldenMul` and `goldenPhi` available. The expected compact solution is

```lean
ext <;> simp [goldenMul, goldenPhi]
```

The challenge tests whether a solver can:

- recognize that structure equality should be split by `ext`;
- identify the relevant definitions to unfold;
- avoid unnecessary `ring` or large automation when `simp` suffices;
- understand that the relation $\varphi^2=\varphi+1$ has already been compiled into the definition of `goldenMul`.

A harder variant could hide the right-hand coordinate expression and ask the model to derive it during theorem synthesis. In ordinary Comparator form, however, the goal is fixed, so this theorem is best viewed as a clean micro-challenge in coordinate reasoning.

## Next declaration to read

The next declaration is **0353 `golden_mul_phiInv_coords`**, also a **`theorem`**.

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ext <;> simp [goldenMul, goldenPhiInv]
```

Mathematically,

$$
(a+b\varphi)(\varphi-1)
=(b-a)+a\varphi,
$$

so the coordinate transformation is

$$
(a,b)\longmapsto(b-a,a).
$$

Together with 0352,

$$
(a,b)\longmapsto(b,a+b),
$$

the development now has both coordinate directions induced by multiplication by $\varphi$ and $\varphi^{-1}$. The later `goldenUnit_descent` selects one of these directions according to sign and order conditions so that `goldenUnitMeasure` decreases strictly.
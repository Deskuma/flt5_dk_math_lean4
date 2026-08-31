# 0292 — `GoldenZeroSectorCandidate.H_pos`

## Declaration kind

This declaration is a **`theorem`**.

It combines the nonnegativity of the quartic factor obtained in 0289 `goldenFifthSndFactor_nonneg` with the strict negativity of the product obtained in 0291 `GoldenZeroSectorCandidate.product_neg`, and proves that the quartic factor occurring in a zero-sector candidate is in fact strictly positive.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic factor in a zero-sector candidate is strictly positive. -/
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s := by
  have hnonneg := goldenFifthSndFactor_nonneg p.r p.s
  have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
    intro hzero
    have hpneg := p.product_neg
    rw [hzero, mul_zero] at hpneg
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

Writing

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
$$

the mathematical conclusion is

$$
H(p.r,p.s)>0.
$$

## Mathematical meaning

By 0289, for arbitrary integers $r,s$ one already has

$$
H(r,s)\ge 0.
$$

On the other hand, 0291 gives, for `p : GoldenZeroSectorCandidate`,

$$
p.s\,H(p.r,p.s)<0.
$$

If

$$
H(p.r,p.s)=0,
$$

then the product would be

$$
p.s\cdot0=0,
$$

contradicting the strict negativity from 0291. Hence

$$
H(p.r,p.s)\neq0.
$$

Since the quartic is nonnegative and nonzero,

$$
H(p.r,p.s)>0.
$$

Thus this theorem upgrades the global nonnegativity of the quartic form to **strict positivity using the extra information stored in a zero-sector candidate**.

## Role in the whole proof

The zero-sector inversion must eventually recover signs, not merely manipulate absolute values and even powers.

The chain from 0288 through 0292 starts with

$$
16H=X^4+10X^2s^2+5s^4,
$$

which yields

$$
H\ge0,
$$

and then uses the candidate product equation

$$
sH=-5^6a^{10}<0
$$

to sharpen this to

$$
H>0.
$$

This positivity is used immediately by 0293 `GoldenZeroSectorCandidate.s_neg`: if the product is negative while $H$ is positive, then the remaining factor $s$ must be negative.

The sign-determination chain is therefore

$$
H\ge0
\longrightarrow
sH<0
\longrightarrow
H>0
\longrightarrow
s<0.
$$

Later, `H_eq_tenth` uses `p.H_pos.le` to remove the natural absolute value and recover the signed integer identity

$$
H(p.r,p.s)=p.d^{10}.
$$

Hence 0292 is not merely an order lemma: it also supplies the sign information required for later **absolute-value removal**.

## Direct dependencies

### `GoldenZeroSectorCandidate`

The structure introduced in 0290. This theorem uses the coordinates `p.r`, `p.s` and the namespace theorem `p.product_neg`.

### `goldenFifthSndFactor_nonneg`

The theorem from 0289:

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s
```

It provides global nonnegativity without using any candidate-specific assumptions.

### `GoldenZeroSectorCandidate.product_neg`

The immediately preceding theorem 0291:

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0
```

It supplies the contradiction used to exclude $H=0$.

### `mul_zero`

Under

```lean
hzero : goldenFifthSndFactor p.r p.s = 0
```

it reduces the product to zero.

### `omega`

After rewriting the negative-product statement with $H=0$, only an impossible integer inequality equivalent to $0<0$ remains. `omega` closes that contradiction.

### `lt_of_le_of_ne`

Finally it combines

$$
0\le H,
\qquad
0\neq H
$$

into

$$
0<H.
$$

The local proof `hne` has type `H ≠ 0`, while `lt_of_le_of_ne` needs the inequality in the opposite disequality orientation, so the proof uses `Ne.symm hne`.

## Proof flow

### 1. Obtain global nonnegativity

```lean
have hnonneg := goldenFifthSndFactor_nonneg p.r p.s
```

This gives

```lean
hnonneg : 0 ≤ goldenFifthSndFactor p.r p.s
```

but still allows the value zero.

### 2. Prove that the quartic is nonzero

```lean
have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
  intro hzero
```

The proof proceeds by contradiction.

### 3. Retrieve the negative product

```lean
have hpneg := p.product_neg
```

so that

```lean
hpneg : p.s * goldenFifthSndFactor p.r p.s < 0
```

is available.

### 4. Substitute $H=0$ into the product

```lean
rw [hzero, mul_zero] at hpneg
```

Mathematically, this turns `hpneg` into the contradiction

$$
0<0.
$$

### 5. Close the contradiction with `omega`

```lean
omega
```

This establishes $H\neq0$.

### 6. Combine nonnegativity and nonzeroness

```lean
exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

The theorem concludes with strict positivity.

## Lean-specific processing

No substantial algebraic normalization occurs in this theorem. Its Lean-specific content lies in composing existing theorem types accurately.

First, 0291 is a namespace theorem, so it can be used through dot notation:

```lean
p.product_neg
```

It is not a structure field, but dot notation applies because its first argument is `p : GoldenZeroSectorCandidate`.

Second, the orientation of disequality matters. The local fact is

```lean
hne : H ≠ 0
```

whereas `lt_of_le_of_ne hnonneg` expects `0 ≠ H`; hence

```lean
Ne.symm hne
```

is passed explicitly.

Third, the contradiction is discharged with `omega`, not `nlinarith`. After `rw [hzero, mul_zero]`, the quartic algebra has disappeared and only an impossible linear integer inequality remains.

## Redundancy and duplication

The proof is short and contains no substantial redundancy.

The explicit `mul_zero` in

```lean
rw [hzero, mul_zero] at hpneg
```

may be replaceable by simplification, for example through a `simpa [hzero]` style proof. However, the current version makes the logical sequence particularly transparent: set the factor to zero, reduce the product to zero, and contradict strict negativity.

There is also little value in exporting the intermediate nonzeroness `hne` as a separate theorem. Downstream code needs the stronger statement `H_pos`, so the present theorem is the more useful API boundary.

## Optimization candidates

### 1. Shorten the nonzero subproof

Conceptually one could attempt a shorter form such as

```lean
have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
  intro h
  have := p.product_neg
  simp [h] at this
```

if the simplifier closes the contradiction reliably.

The present explicit `rw` plus `omega` version is arguably more stable and pedagogically clearer.

### 2. Search for a more direct positivity lemma

Mathlib may contain an order lemma expressing directly that a nonnegative nonzero element is positive. Such a lemma could replace

```lean
lt_of_le_of_ne hnonneg (Ne.symm hne)
```

with a name that states the intent more directly.

No Lean build or API experiment is performed in this task, so a specific replacement lemma name is **not verified** and is not asserted here.

### 3. Keep 0291 and 0292 separate

Although `product_neg` and `H_pos` are used consecutively, merging them would blur two distinct proof roles. 0291 projects order information from the signed product equation; 0292 combines that candidate-specific information with a global nonnegativity theorem. Keeping them separate gives a cleaner reusable API.

## Required Mathlib imports and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The functionality directly used by this theorem includes mainly:

- the linear order on integers,
- `lt_of_le_of_ne`,
- equality/disequality and `Ne.symm`,
- `mul_zero`,
- the `omega` tactic,
- the existing theorem `goldenFifthSndFactor_nonneg`,
- the existing theorem `GoldenZeroSectorCandidate.product_neg`.

`ring`, `nlinarith`, `positivity`, `norm_num`, and `exact_mod_cast` are not used by this theorem itself.

The standalone manifest identifies this section with the source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean`. Since this task explicitly does not run a Lean build, the exact minimal import set below `import Mathlib` is **unverified**, and no specific minimal-import claim is made.

## Comparator challenge suitability

**Suitable.**

Although short, it tests several useful Lean skills:

1. finding the global theorem `goldenFifthSndFactor_nonneg`,
2. using `p.product_neg` through dot notation,
3. excluding $H=0$ by collapsing a strictly negative product to zero,
4. converting nonnegative plus nonzero into positive,
5. handling the orientation difference between `H ≠ 0` and `0 ≠ H`.

A useful challenge shape is

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s := by
  ...
```

with 0289 and 0291 available. The proof is small, but it exercises order reasoning and API discovery, so the verdict is **suitable**.

## Correspondence with the PDFs

The target branch repository tree contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`,
- `docs/pdf/FLT5-main-en-v0-r1.pdf`,

and their blobs are visible in the repository metadata.

A direct attempt to open the raw PDFs in this run did not yield an analyzable PDF resource through the available retrieval path. Therefore the exact PDF page, section, and wording corresponding to this theorem are **not verified**, and no such mapping is guessed.

The technical explanation here is grounded in the actual declaration and its neighboring dependencies in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration is 0293 `GoldenZeroSectorCandidate.s_neg`, also a **`theorem`**:

```lean
/-- The visible zero-sector coordinate has the forced negative sign. -/
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  rcases mul_neg_iff.mp p.product_neg with h | h
  · exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
  · exact h.1
```

By 0291 the product $sH$ is negative, and by 0292 the sign of $H$ is known to be nonnegative, in fact strictly positive. The next theorem uses these sign facts to force

$$
p.s<0.
$$

This prepares the later absolute-value removal

$$
p.s=-5^6p.c^{10}.
$$

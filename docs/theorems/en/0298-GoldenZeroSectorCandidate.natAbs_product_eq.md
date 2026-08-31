# 0298 — `GoldenZeroSectorCandidate.natAbs_product_eq`

## Declaration kind

This declaration is a **`theorem`**.

It applies `Int.natAbs` to the signed product equation carried by a zero-sector candidate,

$$
s\,H(r,s)=-5^6a^{10},
$$

and extracts the magnitude identity

$$
|s|\,|H(r,s)|=5^6a^{10},
$$

which is directly usable in the subsequent tenth-power factor comparison over the natural numbers.

## Lean type

```lean
namespace GoldenZeroSectorCandidate

/-- Natural absolute-value form of the signed product equation. -/
theorem natAbs_product_eq (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, pow_succ] using h
```

The conclusion is an equality in `ℕ`.

Mathematically, it states

$$
|p.s|\,|H(p.r,p.s)|=5^6p.a^{10}.
$$

Here

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

is `goldenFifthSndFactor r s`.

## Mathematical meaning

0290 `GoldenZeroSectorCandidate` stores the signed product equation obtained from the raw zero-sector arithmetic:

```lean
p.product_eq :
  p.s * goldenFifthSndFactor p.r p.s =
    -((5 : ℤ) ^ 6 * (p.a : ℤ) ^ 10)
```

This equation lives in `ℤ` and still contains sign information. The same candidate also stores the two magnitude splits

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
p.H_natAbs_eq : (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

in `ℕ`.

To compare all three equations directly in the next stage, the product equation should also be converted to a magnitude identity in `ℕ`. This theorem performs exactly that type-and-sign boundary conversion.

For integer absolute values,

$$
|xy|=|x|\,|y|,
$$

and moreover

$$
|-5^6a^{10}|=5^6a^{10}.
$$

Thus the mathematical content is immediate, but the theorem packages it in the exact Lean type required downstream.

## Role in the overall proof

0296 `s_eq_neg_five_pow_mul_tenth` and 0297 `H_eq_tenth` determine the signs of the individual factors and yield

$$
s=-5^6c^{10},
\qquad
H=d^{10}.
$$

The present theorem takes a different route: it extracts the magnitude of the original product equation as a whole,

$$
|s|\,|H|=5^6a^{10}.
$$

Substituting the candidate fields

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

gives

$$
(5^6c^{10})d^{10}=5^6a^{10}.
$$

After cancelling the positive common factor $5^6$,

$$
(cd)^{10}=a^{10}.
$$

Injectivity of the tenth power on natural numbers then gives

$$
a=cd.
$$

That is exactly the task of the immediately following theorem 0299 `GoldenZeroSectorCandidate.a_eq_c_mul_d`.

Therefore this theorem is the bridge that moves the signed zero-sector equation and the chosen tenth-power split into the same multiplicative world `ℕ`, enabling the base factorization `a=c*d`.

## Direct dependencies

### `GoldenZeroSectorCandidate.product_eq`

This is a field of the structure introduced in 0290 and is the only direct DkMath-side input of the theorem.

Conceptually it stores

$$
p.s\,H(p.r,p.s)=-5^6p.a^{10}.
$$

### `congrArg`

Given an equality

```lean
x = y
```

and a function `f`, Lean's basic theorem `congrArg` yields

```lean
f x = f y.
```

Here

```lean
congrArg Int.natAbs p.product_eq
```

applies `Int.natAbs : ℤ → ℕ` to both sides of the complete signed integer equation.

### `Int.natAbs_mul`

This states the multiplicativity of natural absolute value on integer products.

Conceptually,

$$
\operatorname{natAbs}(xy)=\operatorname{natAbs}(x)\operatorname{natAbs}(y).
$$

It normalizes the left-hand side into the exact shape of the theorem statement.

### `pow_succ`

The current proof explicitly includes `pow_succ` in the simplifier set.

It participates in normalizing the natural absolute value of the negative product of integer powers into

```lean
5 ^ 6 * p.a ^ 10.
```

The current Lean source confirms that `pow_succ` is explicitly used by the proof. Whether it can now be omitted from the simp list is **unverified**, because no Lean build was run.

## Proof flow

1. Take `p.product_eq`.
2. Apply `Int.natAbs` to both sides with `congrArg`, producing `h`.
3. Rewrite the natural absolute value of the product using `Int.natAbs_mul`.
4. Let simplification normalize the sign and the integer powers on the right into natural-number powers.
5. Close the goal with `simpa [Int.natAbs_mul, pow_succ] using h`.

The proof body is only two lines, but it is a very typical Lean pattern: map an equality through a function, then normalize the result into the target algebra.

## Lean-specific processing

On paper one would simply write “take absolute values on both sides.” In Lean this becomes

```lean
congrArg Int.natAbs p.product_eq
```

A particularly important design choice is the use of `Int.natAbs` rather than `Int.abs`. Since `Int.natAbs` has codomain `ℕ`, the resulting equality can be rewritten directly with `p.s_natAbs_eq` and `p.H_natAbs_eq` in the following theorem.

Thus this theorem does more than remove signs: it also moves the equation **from the integer world into the natural-number world** where the downstream factor comparison is performed.

The right-hand side contains a minus sign and integer casts, but those details are delegated to `simpa`. This makes the proof short, while also making it somewhat dependent on the available simp lemmas.

## Redundancy and overlap

0296–0297 also manipulate absolute values and signs, but their purpose is different:

- 0296 reconstructs an exact signed equation from `|s|` and `s<0`.
- 0297 reconstructs an exact signed equation from `|H|` and `H>0`.
- 0298 derives an `ℕ`-valued magnitude equation directly from the complete signed product equation.

So although the three declarations occupy the same absolute-value layer conceptually, replacing 0298 mechanically by a derivation through 0296–0297 would not necessarily be an improvement. The present theorem depends directly on `product_eq` and therefore supplies the magnitude information needed by `a_eq_c_mul_d` by the shortest route, without depending on the individual sign theorems.

The explicit `pow_succ` in the simp list is the part most likely to be implementation-sensitive. A different Mathlib simp configuration could make it redundant.

## Optimization candidates

1. The intermediate `have h := ...` may be compressible to

```lean
simpa [Int.natAbs_mul, pow_succ] using
  congrArg Int.natAbs p.product_eq
```

2. It is worth testing whether `pow_succ` can be removed, leaving only `simpa [Int.natAbs_mul]`.
3. Conversely, one could reduce reliance on broad simplification by handling the right-hand `natAbs` normalization with explicit lemmas. That may be more stable under Mathlib changes, although the current two-line proof is highly readable.
4. If the only consumer were 0299, this theorem could technically be inlined as a local `have`; however, converting a signed equation into its magnitude identity has independent mathematical meaning, so keeping a named theorem is justified.

These alternatives are **unverified** because no Lean build was run.

## Required Mathlib import and import optimization

The standalone canonical source `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

and its generated-source manifest places this declaration in

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

The main external facilities used directly by this theorem are

- `congrArg`
- `Int.natAbs`
- `Int.natAbs_mul`
- `pow_succ`
- `simpa`

The theorem itself does not use `linarith`, `nlinarith`, `ring`, `omega`, `positivity`, `norm_num`, or `exact_mod_cast`.

A smaller set of imports containing the integer absolute-value API, powers, and simplification infrastructure is likely possible. However, under the instruction not to run a Lean build, the exact minimal import set is **not verified**. The theoretical minimum for this theorem alone must also be distinguished from the dependencies of the complete source module containing the preceding candidate API.

## Suitability for a Comparator challenge

**Highly suitable.** The difficulty is low to medium.

A natural challenge is to present only

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  ...
```

and require the prover to derive it from `p.product_eq`.

Useful comparison points are whether the solver can

- express “apply `Int.natAbs` to both sides” with `congrArg`,
- discover `Int.natAbs_mul`,
- recognize why choosing `Int.natAbs : ℤ → ℕ` aligns the result with the downstream structure fields,
- understand how far `simpa` can normalize signs, casts, and powers.

Because the proof is short, differences in tactic choice and API discovery become especially visible in a Comparator setting.

## Relation to the PDFs

The repository tree on the target branch contains

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

The GitHub connector confirms the presence of both PDF blobs, but the normal text retrieval path cannot parse their binary contents. A direct raw-PDF fetch also did not succeed in the present environment. Therefore the exact page, section, or passage corresponding to this theorem in either PDF is **not confirmed**.

Accordingly, the current Lean canonical source `Flt5DkMath/FLT5StandAlone.lean` is used as the primary technical authority here, and no claim is made about unverified PDF details.

## Next declaration to read

The next declaration is **0299 `GoldenZeroSectorCandidate.a_eq_c_mul_d`**, also a `theorem`.

In the Lean canonical source it immediately follows 0298 and begins as follows:

```lean
/-- The original tenth-power base is exactly the product of the split bases. -/
theorem a_eq_c_mul_d (p : GoldenZeroSectorCandidate) : p.a = p.c * p.d := by
  have hprod := p.natAbs_product_eq
  rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod
  have hpows : (p.c * p.d) ^ 10 = p.a ^ 10 := by
    ...
```

It substitutes the two split identities

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

into the magnitude product identity proved here, cancels the common factor $5^6$, compares tenth powers, and finally recovers

$$
a=cd.
$$

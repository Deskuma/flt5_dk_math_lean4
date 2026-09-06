# 0331 — `fifth_mod_eleven_cases`

## Declaration kind

This declaration is a **`theorem`**.

It classifies fifth powers modulo 11, proving that the remainder is always one of `0`, `1`, or `10`.

## Lean type

```lean
/-- Fifth powers modulo eleven are `0`, `1`, or `-1`. -/
theorem fifth_mod_eleven_cases (n : ℕ) :
    n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
  rw [Nat.pow_mod]
  generalize hr : n % 11 = r
  have hlt : r < 11 := by rw [← hr]; omega
  interval_cases r <;> norm_num
```

## Mathematical statement

For every natural number $n$,

$$
n^5 \bmod 11 \in \{0,1,10\}.
$$

Since $10\equiv -1\pmod{11}$, the usual congruence form is

$$
n^5\equiv 0,1,-1\pmod{11}.
$$

This is consistent with the multiplicative group modulo the prime 11 having order 10. For nonzero residue classes, Fermat's little theorem gives $n^{10}\equiv1\pmod{11}$, so $(n^5)^2\equiv1\pmod{11}$ and therefore $n^5\equiv\pm1\pmod{11}$. The remaining case $11\mid n$ gives residue 0.

The Lean proof, however, does not use group theory or Fermat's little theorem. It directly checks the eleven possible values of $r=n\bmod11$.

## Role in the full proof

This lemma is the entry point to the mod-11 obstruction in the zero-sector factorization phase.

The immediately following theorem is

```lean
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
```

There, the fifth powers `e^5`, `d^5`, and `f^5` are each restricted by the present theorem to the three residue values

$$
0,1,-1.
$$

Reducing

$$
e^5+4d^5=f^5
$$

modulo 11 then leaves only finitely many possibilities. Under the assumption $11\nmid d$, those possibilities can be eliminated, forcing

$$
11\mid d.
$$

Thus this theorem acts as a **residue-state-space compression lemma**. In the overall FLT5 proof it marks the transition from the earlier 2-adic factor splitting and coprimality analysis to a local congruence obstruction at the specific odd prime 11.

## Direct dependencies

This theorem does not depend on any FLT5-specific structure or packet field. It is a completely general lemma about natural-number residues.

Its main Mathlib dependencies are the following.

### `Nat.pow_mod`

```lean
rw [Nat.pow_mod]
```

rewrites `n^5 % 11` into the corresponding expression based on `(n % 11)^5 % 11`.

This reduces the problem from an unbounded natural number `n` to a finite residue class.

### `generalize`

```lean
generalize hr : n % 11 = r
```

introduces a new variable `r` for `n % 11` and retains the defining equality as `hr`.

### `omega`

```lean
have hlt : r < 11 := by rw [← hr]; omega
```

records the standard range bound for a remainder modulo 11.

### `interval_cases`

```lean
interval_cases r
```

uses `r < 11` to split into the eleven cases

$$
r=0,1,2,\ldots,10.
$$

### `norm_num`

Each concrete fifth-power modulo-11 calculation is discharged by `norm_num`.

## Proof flow

### 1. Reduce the power modulo 11 to the residue modulo 11

The proof starts with

```lean
rw [Nat.pow_mod]
```

so that the goal is essentially

$$
(n\bmod11)^5\bmod11\in\{0,1,10\}.
$$

### 2. Replace the residue expression by a variable `r`

```lean
generalize hr : n % 11 = r
```

allows the rest of the proof to work only with the simple natural-number variable `r`.

### 3. Establish `r < 11`

```lean
have hlt : r < 11 := by
  rw [← hr]
  omega
```

places the necessary finite-range information in the local context.

### 4. Enumerate all eleven cases

```lean
interval_cases r
```

splits the proof into the values 0 through 10.

Each branch now contains only a concrete calculation such as

$$
2^5=32\equiv10\pmod{11},
$$

or

$$
3^5=243\equiv1\pmod{11}.
$$

### 5. Close every branch with `norm_num`

```lean
<;> norm_num
```

solves all eleven resulting goals.

Mathematically, the proof is exactly a complete table check of the eleven residue classes.

## Lean-specific processing

### Finite reduction via `Nat.pow_mod`

`interval_cases` cannot be applied directly to the unbounded variable `n`. The first rewrite projects the problem to `n % 11`, turning an infinite-domain statement into a finite-state statement.

That is the key Lean-level transformation in this proof.

### `generalize hr : n % 11 = r`

`generalize` replaces a compound expression with a named variable while preserving an equality relating the two.

Here it creates a simple variable suitable for `interval_cases`.

### `hlt` is context information for `interval_cases`

The fact

```lean
have hlt : r < 11 := ...
```

is not explicitly referenced later in source syntax. Instead, `interval_cases r` discovers the bound from the local context.

This is a common tactic-oriented Lean pattern: prepare a bound as a local fact, then let a later tactic consume it automatically.

## Redundancy and duplication

The proof is extremely short and contains little real redundancy.

One could try to avoid the explicit `generalize` and `hlt` steps by using a different finite enumeration pattern, but the current structure has a clear three-stage shape:

1. reduce modulo 11,
2. establish the finite interval,
3. compute every case.

A conceptual proof using Fermat's little theorem or the multiplicative group of a finite field is also possible, but for this isolated lemma the current brute-force proof is shorter and has lighter conceptual overhead.

## Optimization candidates

### 1. Keep the current finite check

Because 11 is small, `interval_cases` together with `norm_num` is robust and transparent.

Replacing it with general theory could increase theorem-search and import complexity without reducing the local proof burden.

### 2. Extract a general prime-congruence lemma

If later development repeatedly needs statements of the form

$$
x^{(p-1)/2}\in\{0,\pm1\}\pmod p,
$$

then a reusable lemma based on finite fields or Fermat's little theorem could be worthwhile.

For a one-off modulus-11 result, however, that would likely be over-abstraction.

### 3. Naming

`fifth_mod_eleven_cases` accurately describes both the exponent and modulus and is easy to locate from downstream code. There is little incentive to rename it.

## Required Mathlib imports and import optimization

The standalone source uses

```lean
import Mathlib
```

for the whole generated file.

This theorem itself mainly needs

- `Nat.pow_mod`,
- `omega`,
- `interval_cases`,
- `norm_num`.

A smaller import set than all of `Mathlib` is therefore likely possible.

However, no Lean build is performed in this task, so the **minimal import set has not been verified**. In particular, the smallest combination that simultaneously provides `interval_cases`, `omega`, `norm_num`, and the relevant natural-number modular arithmetic API would need separate testing.

## Comparator challenge suitability

**Highly suitable.**

This is a small theorem with several clearly distinct proof strategies that can be compared directly.

Possible Comparator variants include:

1. the current exhaustive `interval_cases` + `norm_num` proof,
2. a conceptual proof via Fermat's little theorem and $(n^5)^2\equiv1$ for nonzero residues,
3. a proof transported to `Fin 11` or `ZMod 11` and handled as finite-field arithmetic.

Useful comparison metrics include proof length, import footprint, tactic dependence, generalizability, and readability.

Because the current proof closes in only a few lines, it is also a good test of whether a more abstract proof genuinely improves reuse and maintenance rather than merely introducing heavier machinery.

## Next declaration to read

The next declaration is

```lean
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
```

Therefore the next sequence number is **0332 `eleven_dvd_d_of_fifth_add_four_fifth`**.

The present `fifth_mod_eleven_cases` theorem restricts fifth-power residues to `0`, `1`, and `10`; the next theorem applies that classification to the factor equation

$$
e^5+4d^5=f^5
$$

and forces $11\mid d$.
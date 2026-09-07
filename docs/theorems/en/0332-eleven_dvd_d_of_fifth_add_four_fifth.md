# 0332 — `eleven_dvd_d_of_fifth_add_four_fifth`

## Declaration kind

This declaration is a **`theorem`**.

It is a local congruence lemma asserting that whenever the fifth-power equation

$$
e^5 + 4d^5 = f^5
$$

holds over the natural numbers, the middle variable $d$ must be divisible by 11.

## Lean type

```lean
/-- The odd factor branch forces its fifth-power offset into the prime eleven. -/
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
  by_contra hd
  have he := fifth_mod_eleven_cases e
  have hd' := fifth_mod_eleven_cases d
  have hf := fifth_mod_eleven_cases f
  have hdmod : d ^ 5 % 11 ≠ 0 := by
    intro hz
    apply hd
    apply (by norm_num : Nat.Prime 11).dvd_of_dvd_pow
    exact Nat.dvd_of_mod_eq_zero hz
  have hm := congrArg (fun n : ℕ => n % 11) h
  omega
```

## Mathematical statement

For all natural numbers $e,d,f$, if

$$
e^5 + 4d^5 = f^5,
$$

then

$$
11 \mid d.
$$

The core input is the classification of fifth-power residues modulo 11 established immediately before this theorem. For every natural number $n$,

$$
n^5 \bmod 11 \in \{0,1,10\},
$$

or equivalently

$$
n^5\equiv0,\pm1\pmod{11}.
$$

If $11\nmid d$, then $d^5\not\equiv0\pmod{11}$, so

$$
d^5\equiv\pm1\pmod{11}.
$$

Likewise, $e^5$ and $f^5$ each lie in $\{0,\pm1\}$ modulo 11. Hence in

$$
e^5+4d^5\equiv f^5\pmod{11},
$$

the term $4d^5$ is congruent to either $4$ or $-4$. Adding any element of $\{0,\pm1\}$ cannot produce another element of $\{0,\pm1\}$ modulo 11. Therefore the assumption $11\nmid d$ is impossible, and $11\mid d$ follows.

## Role in the full proof

This theorem supplies the **modulo-11 obstruction for the odd branch** of the zero-sector factorization.

Earlier, `GoldenZeroSectorInversionPacket.odd_factor_halves` prepares the odd-`c` branch so that the inversion factors can be represented in fifth-power form such as

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5.
$$

Their difference then yields

$$
e^5 + 4d^5 = f^5.
$$

The present theorem takes only that equation as input and extracts

$$
11\mid d.
$$

Later, `GoldenZeroSectorFactorData.odd_eleven_channel` combines this fact with `coprime_c_d` to deduce

$$
11\nmid c,
$$

and then uses factor ownership and coprimality to exclude 11 from $e$, $f$, and $ef$ as well.

Thus this theorem acts as a **local-prime channel generator**: it injects the concrete odd prime 11 into the otherwise abstract factor packet.

## Direct dependencies

### `fifth_mod_eleven_cases`

This is the immediately preceding theorem. It restricts the fifth-power residues of `e`, `d`, and `f` to

$$
0,1,10.
$$

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

### `Nat.Prime.dvd_of_dvd_pow`

Using the primality of 11, this turns

$$
11\mid d^5
$$

into

$$
11\mid d.
$$

### `Nat.dvd_of_mod_eq_zero`

This converts `d ^ 5 % 11 = 0` into the divisibility statement

$$
11\mid d^5.
$$

### `congrArg`

The original equality `h` is mapped through `% 11`:

```lean
have hm := congrArg (fun n : ℕ => n % 11) h
```

This inserts the modulo-11 version of the original fifth-power equation into the local context.

### `omega`

After the fifth-power residues have been reduced to a finite set, `omega` closes the remaining finite arithmetic contradiction using `he`, `hd'`, `hf`, `hdmod`, and `hm`.

## Proof flow

### 1. Negate the desired divisibility

```lean
by_contra hd
```

Assume

$$
11\nmid d.
$$

### 2. Classify all three fifth-power residues

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

Thus each of

$$
e^5,d^5,f^5 \pmod{11}
$$

is one of `0`, `1`, or `10`.

### 3. Exclude the zero residue for `d^5`

```lean
have hdmod : d ^ 5 % 11 ≠ 0 := by
  intro hz
  apply hd
  apply (by norm_num : Nat.Prime 11).dvd_of_dvd_pow
  exact Nat.dvd_of_mod_eq_zero hz
```

If `d^5 % 11 = 0`, then $11\mid d^5$, and primality of 11 forces $11\mid d$, contradicting `hd`.

So among the three cases from `hd'`, the zero branch is removed and $d^5$ is restricted to $\pm1$ modulo 11.

### 4. Map the original equation modulo 11

```lean
have hm := congrArg (fun n : ℕ => n % 11) h
```

This gives

$$
(e^5 + 4d^5)\bmod11 = f^5\bmod11.
$$

### 5. Close the finite contradiction with `omega`

At this point `he`, `hd'`, and `hf` are finite residue disjunctions, `hdmod` excludes the zero residue for `d^5`, and `hm` is the modulo-11 equation.

`omega` combines these constraints and verifies that every remaining arithmetic possibility is inconsistent.

The contradiction discharges the negated assumption and yields `11 ∣ d`.

## Lean-specific processing

### Using `by_contra` for divisibility

Instead of constructing a witness for `11 ∣ d` directly, the proof assumes `¬ 11 ∣ d` and converts that assumption into nonvanishing modulo 11. This is much more convenient for the residue argument.

### Supplying primality with `norm_num`

```lean
(by norm_num : Nat.Prime 11)
```

provides the proof object that 11 is prime so that the generic Mathlib divisibility theorem can be applied.

### Applying `% 11` through `congrArg`

Rather than manually rewriting both sides of the original equation, the proof applies the function `fun n : ℕ => n % 11` to the equality via congruence.

### Letting `omega` consume residue disjunctions

The proof does not explicitly split `he`, `hd'`, and `hf` into up to 27 cases with `rcases`. Instead, `omega` uses the disjunctions and the arithmetic constraints in the local context to close the finite search automatically.

Mathematically, this should be understood as an automated exhaustive check of the fifth-power residue table.

## Redundancy and duplication

The proof is already short and contains little obvious redundancy.

The three lines

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

repeat the same theorem application, but they make the proof extremely clear. If similar mod-$p$ obstructions become common later, one could package several residue classifications into a small helper structure, but for this single use such abstraction would probably be unnecessary.

The `hdmod` proof passes through `Nat.Prime.dvd_of_dvd_pow`; a more direct current Mathlib API may exist, but that would need to be checked before claiming an improvement.

## Optimization candidates

### 1. Compare against an explicit case-split proof

Instead of relying on `omega`, one could explicitly `rcases` the three residue classifications and close each case with `norm_num`.

The current proof is shorter, while the explicit version would expose the residue obstruction more visibly in the proof term.

### 2. Use `ZMod 11`

The argument could be phrased in `ZMod 11`, treating

$$
x^5\in\{0,1,-1\}
$$

as ring equalities rather than natural-number remainders. This is conceptually cleaner algebraically, but may introduce additional coercions and imports for a theorem this small.

### 3. Generalize the local obstruction

For future exploration of equations of the form

$$
a^5+k b^5=c^5,
$$

one could parameterize the coefficient $k$, the modulus, and the finite fifth-power residue set, turning the present argument into a reusable finite local-obstruction checker.

For the current FLT5 proof, however, the dedicated coefficient-4 / modulus-11 theorem makes the intent exceptionally clear.

## Required Mathlib imports and import optimization

The standalone source currently uses

```lean
import Mathlib
```

for the complete file.

The main features directly needed by this theorem are:

- `Nat.Prime`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_of_mod_eq_zero`
- `norm_num`
- `omega`
- the preceding local theorem `fifth_mod_eleven_cases`

It is very likely that a smaller import set than all of `Mathlib` is sufficient. However, no Lean build is performed here, so the **minimal import set has not been verified**. In particular, the smallest combination covering `omega`, `norm_num`, and the natural-number prime/remainder APIs would need separate validation.

## Suitability for a Comparator challenge

**Very suitable.**

At least four proof styles can be compared:

1. the current `fifth_mod_eleven_cases` + `omega` proof;
2. explicit residue case splitting followed by `norm_num`;
3. a `ZMod 11` proof using ring arithmetic;
4. a generalized finite fifth-power-residue lemma from which this theorem is instantiated.

Useful evaluation axes include proof length, visibility of the number-theoretic idea, tactic dependence, import size, and generalizability.

The current proof is especially interesting because `omega` hides a substantial amount of finite checking, making the tradeoff between brevity and mathematical transparency easy to measure.

## Next declaration to read

The next declaration in the repository source is

```lean
inductive GoldenZeroSectorFactorBranch
  | odd
  | evenLeftLow
  | evenRightLow
  deriving DecidableEq
```

Therefore the next sequence entry is **0333 `GoldenZeroSectorFactorBranch`**.

This is not a theorem but an **`inductive`** declaration. It fixes the exhaustive two-adic factorization branches at the type level:

- `odd`
- `evenLeftLow`
- `evenRightLow`

The present modulo-11 theorem completes the local obstruction used by the odd branch, after which the source introduces the branch-label type used to organize the subsequent exact factor data.
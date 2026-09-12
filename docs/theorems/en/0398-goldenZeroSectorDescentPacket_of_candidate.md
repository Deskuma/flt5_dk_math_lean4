# 0398 `goldenZeroSectorDescentPacket_of_candidate`

## Declaration kind

`def`

This definition constructs a `GoldenZeroSectorDescentPacket` from a `GoldenZeroSectorCandidate`, thereby providing the input expected by the well-founded descent closure of 0397.

## Lean code

```lean
/-- Every certified zero-sector candidate enters the recursive descent invariant. -/
def goldenZeroSectorDescentPacket_of_candidate
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorDescentPacket where
  base := ⟨p.r, p.s⟩
  t := 5 * p.c ^ 2
  D := p.d ^ 2
  t_pos := mul_pos (by norm_num) (pow_pos p.c_pos 2)
  D_pos := pow_pos p.d_pos 2
  coprime_coords := p.coprime_coords
  snd_eq := Or.inr (by
    rw [p.s_eq_neg_five_pow_mul_tenth]
    push_cast
    ring)
  H_eq := by
    rw [p.H_eq_tenth]
    push_cast
    ring
  five_not_dvd_norm := by
    intro hFive
    apply p.five_not_dvd_b
    rcases p.norm_eq_or_eq_neg with h | h
    · rw [h] at hFive
      exact_mod_cast hFive
    · rw [h] at hFive
      exact_mod_cast (Int.dvd_neg.mp hFive)
```

## Lean type

```lean
goldenZeroSectorDescentPacket_of_candidate :
  GoldenZeroSectorCandidate → GoldenZeroSectorDescentPacket
```

The input is a certified zero-sector candidate `p`; the output is a packet satisfying the recursive descent invariant.

Because this declaration is a `def`, not a theorem, its role is not primarily to establish a new proposition. It is a **constructor / repackaging map** that reorganizes already-proved candidate data into the structure required by the descent machinery.

## Mathematical meaning

The candidate `p` carries integer coordinates

$$
(r,s)
$$

and positive natural parameters $c,d$, together with the certified zero-sector relations. The descent parameters are chosen as

$$
\gamma=(r,s),\qquad
 t=5c^2,\qquad
 D=d^2.
$$

The candidate-side tenth-power identities are then rewritten into the fifth-power form required by the recursive packet.

For `s`, the candidate provides a negative expression of the form

$$
s=-5^6c^{10}.
$$

This is reorganized as

$$
s=-5(5c^2)^5=-5t^5,
$$

which fills the negative branch of `snd_eq`.

Likewise the quartic factor $H(r,s)$ is rewritten from

$$
H(r,s)=d^{10}
$$

to

$$
H(r,s)=(d^2)^5=D^5,
$$

which supplies `H_eq`.

Finally, the candidate norm condition

$$
N(r,s)=d^2
\quad\text{or}\quad
N(r,s)=-d^2
$$

together with the candidate's nondivisibility information implies

$$
5\nmid N(r,s).
$$

Thus the definition is mathematically the transport

$$
\text{candidate arithmetic}
\longrightarrow
\text{recursive descent invariant}.
$$

## Role in the full proof

0397 `goldenZeroSectorDescentPacket_false` proves that any `GoldenZeroSectorDescentPacket` yields `False`. However, it does not directly accept the earlier `GoldenZeroSectorCandidate` structure.

0398 bridges precisely that interface gap:

$$
\text{GoldenZeroSectorCandidate}
\xrightarrow{\text{0398}}
\text{GoldenZeroSectorDescentPacket}
\xrightarrow{\text{0397}}
\bot.
$$

Consequently, the next declaration 0399 `goldenZeroSectorCandidate_false` needs almost no fresh arithmetic: it simply feeds the packet built here into the contradiction theorem of 0397.

## Direct dependencies

The main direct dependencies are:

- `GoldenZeroSectorCandidate`
- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `GoldenZeroSectorCandidate.r`
- `GoldenZeroSectorCandidate.s`
- `GoldenZeroSectorCandidate.c`
- `GoldenZeroSectorCandidate.d`
- `GoldenZeroSectorCandidate.c_pos`
- `GoldenZeroSectorCandidate.d_pos`
- `GoldenZeroSectorCandidate.coprime_coords`
- `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`
- `GoldenZeroSectorCandidate.H_eq_tenth`
- `GoldenZeroSectorCandidate.five_not_dvd_b`
- `GoldenZeroSectorCandidate.norm_eq_or_eq_neg`
- `mul_pos`
- `pow_pos`
- `Int.dvd_neg`
- tactics `norm_num`, `push_cast`, `ring`, `exact_mod_cast`

The fields of `GoldenZeroSectorDescentPacket` filled by this definition are

```lean
base
t
D
t_pos
D_pos
coprime_coords
snd_eq
H_eq
five_not_dvd_norm
```

## Construction flow

1. Reuse the candidate's integer coordinates as the packet base.

   ```lean
   base := ⟨p.r, p.s⟩
   ```

2. Choose parameters matching the recursive fifth-power shape:

   ```lean
   t := 5 * p.c ^ 2
   D := p.d ^ 2
   ```

3. Obtain positivity of `t` and `D` directly from `p.c_pos` and `p.d_pos`.

4. Reuse the candidate's coordinate coprimality without modification.

   ```lean
   coprime_coords := p.coprime_coords
   ```

5. For `snd_eq`, select the negative branch with `Or.inr`. Rewrite the candidate's tenth-power identity, normalize casts, and use ring normalization to prove

   $$
   -5^6c^{10}=-5(5c^2)^5.
   $$

6. For `H_eq`, rewrite the candidate's tenth-power identity and prove

   $$
   d^{10}=(d^2)^5.
   $$

7. Prove `five_not_dvd_norm` by assuming that 5 divides the norm and splitting the candidate's signed norm alternative.

8. In both sign branches, transport integer divisibility back to the natural-number statement with `exact_mod_cast`, contradicting `p.five_not_dvd_b`.

## Lean-specific processing

### Repackaging through a structure literal

The core form is

```lean
def ... : GoldenZeroSectorDescentPacket where
```

Mathematically this is mostly a reorganization of known facts, but Lean requires every target field to be supplied with exactly the correct type.

### `Or.inr`

`GoldenZeroSectorDescentPacket.snd_eq` admits two signed branches. The candidate provides the negative sign, so the construction explicitly selects

```lean
Or.inr
```

before proving the required equality.

### `push_cast`

The parameters $c,d$ live in `ℕ`, whereas `s`, `H`, and the packet equalities live in `ℤ`. `push_cast` moves casts through multiplication and powers, producing a polynomial expression that `ring` can normalize.

### `ring`

Here `ring` does not establish any new number-theoretic content. It certifies the exponent rearrangements that convert tenth powers into the packet's fifth-power format.

### `exact_mod_cast`

The norm divisibility assumption is over `ℤ`, while `p.five_not_dvd_b` lives on the natural-number side. `exact_mod_cast` transports the divisibility fact across that type boundary.

In the negative norm branch, the code first uses

```lean
Int.dvd_neg.mp hFive
```

to turn

$$
5\mid -d^2
$$

into

$$
5\mid d^2
$$

before casting.

## Redundancy and duplication

The definition is short and contains little substantive duplication, but two reusable patterns are visible.

First, the exponent normalizations

$$
c^{10}=(c^2)^5
$$

and

$$
d^{10}=(d^2)^5
$$

appear separately in `snd_eq` and `H_eq`. A generic helper such as

```lean
pow_ten_eq_sq_pow_five
```

could remove some local `push_cast; ring` work.

Second, the pattern

```lean
N = D ∨ N = -D
```

together with `¬ 5 ∣ D` implying `¬ 5 ∣ N` is reusable wherever signed norms are handled. A small divisibility helper could isolate the sign bookkeeping.

That said, the current implementation keeps the provenance of each field immediately visible, which is valuable for auditing. Abstraction purely for shortening the code is not necessary.

## Optimization candidates

### 1. Exponent-normalization helper

A lemma of the shape

```lean
(c : ℤ) ^ 10 = ((c ^ 2 : ℕ) : ℤ) ^ 5
```

would shorten both `snd_eq` and `H_eq`.

### 2. Signed divisibility transport

A helper conceptually like

```lean
not_dvd_of_eq_or_eq_neg
```

could package the implication

$$
N=D\lor N=-D,
\qquad 5\nmid D
\Longrightarrow
5\nmid N.
$$

### 3. Make the candidate-to-packet boundary explicit

0398 is an important proof-layer boundary. If the source is later modularized further, a dedicated candidate-to-descent interface would make the separation between arithmetic discovery and well-founded descent even clearer.

## Required Mathlib imports and import optimization

The standalone source `Flt5DkMath/FLT5StandAlone.lean` currently uses

```lean
import Mathlib
```

For 0398 itself, the directly visible Mathlib facilities are basic integer/natural arithmetic, `pow_pos`, `mul_pos`, integer divisibility, and the tactics `norm_num`, `push_cast`, `ring`, and `exact_mod_cast`.

Therefore a narrower import set than all of `Mathlib` is likely possible. However, this declaration also depends on repository-local definitions and lemmas for `GoldenZeroSectorCandidate` and `GoldenZeroSectorDescentPacket`. Because no Lean build is performed in this run, the **exact minimal import set is not verified**.

A safe import-minimization pass would start from the source module's local imports and remove tactic/algebra modules one by one while checking the build.

## Comparator challenge suitability

**Suitable; medium difficulty.**

For a standalone challenge, it would be preferable to replace the full FLT5 structures with minimal records containing only the fields actually consumed here.

The essential challenge consists of three tasks:

1. Normalize $-5^6c^{10}$ to $-5(5c^2)^5$.
2. Normalize $d^{10}$ to $(d^2)^5$.
3. Transport $5\nmid N$ from a signed norm equation $N=\pm d^2$ across the `ℕ`/`ℤ` boundary.

This makes the declaration a good test of structure construction, cast management, `push_cast`, and `exact_mod_cast`.

It is not, however, one of the deep arithmetic bottlenecks of FLT5 itself. Its primary content is **transport and packaging** of already-established facts.

## Next declaration to read

The next declaration is **0399 `goldenZeroSectorCandidate_false`**, a `theorem`:

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

Because 0398 converts a candidate into a descent packet, 0399 closes the candidate directly by applying 0397.

Thus the local chain is

$$
\text{candidate}
\xrightarrow{0398}
\text{descent packet}
\xrightarrow{0397}
\bot.
$$

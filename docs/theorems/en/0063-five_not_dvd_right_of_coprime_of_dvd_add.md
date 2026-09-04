# 0063 — `five_not_dvd_right_of_coprime_of_dvd_add`

## 1. Target declaration

```lean
private theorem five_not_dvd_right_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ v := by
  intro h5v
  have h5u : 5 ∣ u := (Nat.dvd_add_left h5v).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop
```

This declaration is a `private theorem` used only inside the `SignedFiveAdic` layer. It is the exact left-right symmetric counterpart of 0062, `five_not_dvd_left_of_coprime_of_dvd_add`.

## 2. Lean type

For implicit natural numbers `u v`, it provides

```lean
Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ v
```

`Nat.Coprime u v` expresses coprimality over the natural numbers, while the conclusion `¬ 5 ∣ v` says that 5 does not divide the right component `v`.

## 3. Mathematical statement

Mathematically this is the same principle as in 0062.

$$
\gcd(u,v)=1,
\qquad
5\mid(u+v).
$$

Assume for contradiction that $5\mid v$. Since $5\mid(u+v)$, it follows that $5\mid u$. Thus 5 is a common divisor of `u` and `v`. Because $5>1$, this contradicts $\gcd(u,v)=1$. Hence

$$
5\nmid v.
$$

The essential fact is not the primality of 5 but that the common divisor is larger than 1. More generally, if $1<d$, $\gcd(u,v)=1$, and $d\mid u+v$, then $d$ divides neither component.

## 4. Role in the FLT5 proof

This lemma fixes that the right component `v` is not divisible by 5 immediately before the sum-orientation five-adic analysis.

The following theorem, `SumGN5_cast_mod25_eq_five`, uses 0062 and the present lemma side by side:

```lean
have h5u : ¬ 5 ∣ u :=
  five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
have h5v : ¬ 5 ∣ v :=
  five_not_dvd_right_of_coprime_of_dvd_add hcop h5sum
```

It therefore secures nondivisibility by 5 for both `u` and `v`, and then uses that information to force the value of `SumGN5 u v` modulo 25 to be exactly 5.

Thus 0062–0063 form the preprocessing pair

```text
Coprime u v + 5 | (u+v)
          ↓
   5 ∤ u  and  5 ∤ v
          ↓
  SumGN5 mod 25 analysis
```

The lemma is tiny in isolation, but it supplies half of the input condition needed for the residual valuation argument downstream.

## 5. Direct dependencies

The proof directly uses:

- `Nat.Coprime u v`
- `Nat.dvd_add_left`
- `Nat.not_coprime_of_dvd_of_dvd`
- `norm_num` to prove `(1 < 5)`

In particular,

```lean
(Nat.dvd_add_left h5v).mp h5sum
```

fixes the known fact `5 ∣ v` and uses the relevant direction of

```lean
5 ∣ u + v ↔ 5 ∣ u
```

to extract `h5u : 5 ∣ u`.

## 6. Proof flow

The proof is the mirror image of 0062.

1. `intro h5v` opens the negated conclusion and assumes `5 ∣ v`.
2. `Nat.dvd_add_left h5v` together with `h5sum` yields `h5u : 5 ∣ u`.
3. From `1 < 5`, `5 ∣ u`, and `5 ∣ v`, conclude that `u` and `v` are not coprime.
4. Apply that contradiction to `hcop : Nat.Coprime u v` and close `False`.

The proof tree is

```text
hcop : Coprime u v
h5sum : 5 | u+v
  assume h5v : 5 | v
       ↓ dvd_add_left
     h5u : 5 | u
       ↓ common divisor 5 > 1
  ¬ Coprime u v
       ↓ hcop
      False
```

## 7. Lean-specific processing

### 7.1 `¬ P` is `P → False`

The conclusion `¬ 5 ∣ v` is definitionally `5 ∣ v → False`, so the proof naturally begins with `intro h5v`.

### 7.2 Direction of `Nat.dvd_add_left`

Where 0062 uses `Nat.dvd_add_right h5u`, the present theorem uses `Nat.dvd_add_left h5v`. Only the known summand has been exchanged; the proof architecture is exactly symmetric.

### 7.3 Refuting `Nat.Coprime` by a common divisor

The theorem

```lean
Nat.not_coprime_of_dvd_of_dvd
```

receives

```lean
(by norm_num : 1 < 5)
```

and the two divisibility proofs. No proof of `Nat.Prime 5` is needed. This exposes that the theorem, while living in a five-adic layer, is really a more general gcd fact.

## 8. Redundancy and duplication

The main duplication is the left-right symmetry with 0062. The two proofs differ only by

- swapping `u` and `v`, and
- swapping `dvd_add_right` with `dvd_add_left`.

Mathematically both can be derived from one general lemma. Still, the current form has a local readability advantage because the consumer `SumGN5_cast_mod25_eq_five` immediately names `h5u` and `h5v` separately.

## 9. Optimization candidates

The first option is to derive the present theorem from 0062 by symmetry. Conceptually one could use

```lean
have := five_not_dvd_left_of_coprime_of_dvd_add hcop.symm ?_
```

and rewrite the sum with `Nat.add_comm`. For such a short theorem, however, the added rewriting may be less readable than the current direct proof.

The second option is a genuine generalization, for example

```lean
lemma not_dvd_of_coprime_of_one_lt_of_dvd_add
    {d u v : ℕ}
    (hd : 1 < d)
    (hcop : Nat.Coprime u v)
    (hsum : d ∣ u + v) :
    ¬ d ∣ u ∧ ¬ d ∣ v
```

which would combine 0062 and 0063 into one common statement.

A third option is a private helper tailored to the consumer, such as

```lean
five_not_dvd_both_of_coprime_of_dvd_add
```

and destructure the pair once inside `SumGN5_cast_mod25_eq_five`.

The current code is nevertheless short, standard, and easy to maintain.

## 10. Required Mathlib imports and import optimization

The generated standalone artifact available on the target branch uses

```lean
import Mathlib
```

The lemma itself only requires natural-number gcd / coprimality / divisibility APIs and the `norm_num` tactic. The artifact manifest confirms that the original source module is `DkMath/FLT/Five/SignedFiveAdic.lean`, but that split source file was not directly available from this museum branch, so the exact minimal import line was not verified.

As an explicit inference, the imports could likely be reduced to the natural-number gcd/coprime modules providing these lemmas plus something equivalent to `Mathlib.Tactic.NormNum`. Exact module names are not asserted because no Lean build was run.

## 11. Comparator challenge suitability

This is a good micro challenge, especially when paired with 0062.

The fixed target type is

```lean
{u v : ℕ} → Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ v
```

Possible implementations to compare include:

- the current `dvd_add_left` + `not_coprime_of_dvd_of_dvd` proof,
- a proof reusing 0062 after swapping `u` and `v`,
- a proof manipulating gcd directly,
- projection from a lemma returning both nondivisibility statements at once.

Useful comparison criteria are proof length, number of dependencies, reuse of symmetry, elaboration stability, and import size.

## 12. Evidence and inference

The confirmed source is `Flt5DkMath/FLT5StandAlone.lean` on the target branch. Its generated header records `DkMath/FLT/Five/SignedFiveAdic.lean` as an ordered source module, and the artifact contains both the complete Lean body of this theorem and its direct use in the immediately following `SumGN5_cast_mod25_eq_five`.

The exact page correspondence in the existing Japanese and English PDFs was not checked in this run, so no PDF-specific wording or page number has been invented. Import minimization is also explicitly marked as inference because the split source file was not directly fetched.

## 13. Next declaration to read

The next declaration is the immediately following private theorem

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5
```

This is the first point where `5 ∤ u` from 0062 and `5 ∤ v` from the present article are combined to pin down the exact modulo-25 residual of `SumGN5`. It is therefore the natural next declaration in dependency order.

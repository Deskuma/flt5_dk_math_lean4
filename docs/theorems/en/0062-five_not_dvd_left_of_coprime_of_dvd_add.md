# 0062 — `five_not_dvd_left_of_coprime_of_dvd_add`

## 1. Target declaration

```lean
private theorem five_not_dvd_left_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ u := by
  intro h5u
  have h5v : 5 ∣ v := (Nat.dvd_add_right h5u).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop
```

This declaration is a `private theorem`, used only as an internal helper in the `SignedFiveAdic` layer.

## 2. Lean type

For implicit natural numbers `u v`, it provides

```lean
Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ u
```

Here `Nat.Coprime u v` corresponds to `gcd u v = 1`, while the conclusion `¬ 5 ∣ u` states that 5 does not divide the left component `u`.

## 3. Mathematical statement

Mathematically this is a very basic consequence of coprimality.

$$
\gcd(u,v)=1,
\qquad
5\mid(u+v).
$$

If $5\mid u$, then from $5\mid(u+v)$ one also obtains $5\mid v$. Thus 5 would be a common divisor of $u$ and $v$; since $5>1$, this contradicts coprimality. Hence

$$
5\nmid u.
$$

The essential property is not primality but merely `1 < 5`. More generally, if $1<d$, $\gcd(u,v)=1$, and $d\mid u+v$, then $d$ cannot divide either summand.

## 4. Role in the overall FLT5 proof

This lemma is a preprocessing step before evaluating the sum orientation residual `SumGN5` modulo 25.

The later theorem `SumGN5_cast_mod25_eq_five` directly invokes it as

```lean
have h5u : ¬ 5 ∣ u :=
  five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
```

and obtains `¬ 5 ∣ v` from the symmetric right-hand version. With both inputs known to be nonmultiples of 5, the proof can then pin down the value of `SumGN5 u v` in `ZMod 25` to 5.

Its role is therefore

```text
coprime(u,v) + 5 | (u+v)
          ↓
       5 ∤ u
          ↓
  mod-25 residual analysis
```

as a local five-adic preprocessing step.

## 5. Direct dependencies

The declaration directly uses:

- `Nat.Coprime u v`
- `Nat.dvd_add_right`
- `Nat.not_coprime_of_dvd_of_dvd`
- `norm_num` to close `(1 < 5)`

In particular,

```lean
(Nat.dvd_add_right h5u).mp h5sum
```

uses the known divisibility `5 ∣ u` to extract the needed direction of

```lean
5 ∣ u + v ↔ 5 ∣ v
```

and produces `h5v : 5 ∣ v`.

## 6. Proof flow

The proof has only four steps.

1. `intro h5u` assumes the negated conclusion, introducing `5 ∣ u`.
2. `Nat.dvd_add_right h5u` together with `h5sum` yields `h5v : 5 ∣ v`.
3. From `5 > 1`, `5 ∣ u`, and `5 ∣ v`, conclude that `u` and `v` are not coprime.
4. Apply that contradiction to `hcop : Nat.Coprime u v`.

The proof tree is

```text
hcop : Coprime u v
h5sum : 5 | u+v
  assume h5u : 5 | u
       ↓ dvd_add_right
     h5v : 5 | v
       ↓ common divisor 5 > 1
  ¬ Coprime u v
       ↓ hcop
      False
```

## 7. Lean-specific processing

### 7.1 Opening a negation with `intro`

The conclusion `¬ 5 ∣ u` is internally

```lean
5 ∣ u → False
```

so the proof begins as an ordinary implication proof with `intro h5u`.

### 7.2 Direction of `Nat.dvd_add_right`

`Nat.dvd_add_right h5u` fixes the already-known fact that 5 divides `u` and relates divisibility of the sum to divisibility of the remaining term. `.mp h5sum` moves from the sum to the right summand.

### 7.3 `Nat.not_coprime_of_dvd_of_dvd`

This lemma directly expresses that a common divisor greater than 1 destroys coprimality. The proof does not need 5 to be prime; it passes only

```lean
(by norm_num : 1 < 5)
```

which is an important structural point.

## 8. Redundancy and duplication

Immediately afterward comes the completely symmetric theorem

```lean
five_not_dvd_right_of_coprime_of_dvd_add
```

which differs essentially only by using `Nat.dvd_add_left`.

Mathematically, the two lemmas could be derived from one general statement, so there is deliberate left/right duplication in the current code.

The current form does, however, make downstream code locally readable because the two facts can be named separately as `h5u` and `h5v`.

## 9. Optimization candidates

The first candidate is generalization. Conceptually one could introduce

```lean
lemma not_dvd_left_of_coprime_of_one_lt_of_dvd_add
    {d u v : ℕ}
    (hd : 1 < d)
    (hcop : Nat.Coprime u v)
    (hsum : d ∣ u + v) :
    ¬ d ∣ u
```

and derive the present lemma as the case `d = 5`.

A second option is to derive the right-hand theorem from the left-hand one by swapping `u` and `v`, using symmetry of `Nat.Coprime` and commutativity of addition. For such a short lemma, however, the current direct proof may remain simpler for both elaboration and human reading.

A third option is to return both facts at once,

```lean
¬ 5 ∣ u ∧ ¬ 5 ∣ v
```

if downstream code always needs the pair together.

## 10. Required Mathlib imports and import optimization

The standalone artifact available on the target branch uses

```lean
import Mathlib
```

For this lemma alone, the actual requirements are natural-number gcd/coprimality/divisibility results plus the `norm_num` tactic. The original split file `DkMath/FLT/Five/SignedFiveAdic.lean` could not be fetched directly from this museum branch, so the exact minimal import set is not confirmed.

As an explicit inference, the import could likely be reduced to the module providing the relevant `Nat` gcd/coprime API together with the `NormNum` tactic module. Exact module names are not asserted without a build check.

## 11. Comparator challenge suitability

This is well suited to a small Comparator challenge.

Fix the type

```lean
{u v : ℕ} → Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ u
```

and compare implementations based on:

- the current `dvd_add_right` + `not_coprime_of_dvd_of_dvd` proof;
- a proof that manipulates gcd directly;
- a proof through a generalized divisor lemma;
- projection from a lemma returning both nondivisibility facts at once.

Useful comparison criteria are not only line count, but dependency count, reusability for the symmetric theorem, tactic dependence, and minimal import size.

The mathematical difficulty is low, but it is a good micro challenge for learning the `Nat.Coprime` and additive divisibility APIs.

## 12. Evidence and explicit inferences

The confirmed source is the Lean code embedded in `Flt5DkMath/FLT5StandAlone.lean` on the target branch. There the symmetric right-hand lemma follows immediately, and `SumGN5_cast_mod25_eq_five` then directly invokes both lemmas.

The concrete page correspondence in the existing Japanese and English PDFs was not checked in this run, so no PDF-specific wording or page number is supplied. Import minimization is also marked as inference because the split source file could not be retrieved directly from this branch.

## 13. Next theorem to read

The next declaration is the immediately following private lemma

```lean
private theorem five_not_dvd_right_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ v
```

After confirming this exact left/right symmetric companion, dependency order naturally proceeds to `SumGN5_cast_mod25_eq_five`, where both lemmas merge.

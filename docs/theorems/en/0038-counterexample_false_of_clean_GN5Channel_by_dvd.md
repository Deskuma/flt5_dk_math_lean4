# 0038 — `counterexample_false_of_clean_GN5Channel_by_dvd`

## 1. Declaration

```lean
theorem counterexample_false_of_clean_GN5Channel_by_dvd
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z :=
    Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  apply not_fifth_power_body_of_clean hClean
  exact ⟨x, body5_eq_fifth_power_of_fermat hyz hPack.hEq⟩
```

## 2. Lean type

The theorem takes natural numbers `x y z q` as implicit arguments.

- `hPack : CounterexamplePack x y z` packages positivity, coprimality of `x` and `y`, and the Fermat equation `x^5 + y^5 = z^5`.
- `hClean : CleanGN5Channel (z - y) y q` says that the prime `q` occurs once in the local `GN5` factor and does not occur in the gap.
- The conclusion is `False`, asserting that these two inputs cannot coexist.

## 3. Mathematical statement

From `hPack` we have

$$
x^5+y^5=z^5.
$$

Since `x>0`, we get `y<z`, hence `y≤z`, so the natural-number gap `z-y` reconstructs correctly.

The previous bridge gives

$$
Body5(z-y,y)=x^5.
$$

On the other hand, the clean channel says that a prime `q` divides

$$
Body5(z-y,y)=(z-y)GN5(z-y,y)
$$

but `q^2` does not divide it. A prime dividing a perfect fifth power divides its base, so its square must also divide that fifth power. Therefore this body cannot be a perfect fifth power.

Thus the equality

$$
Body5(z-y,y)=x^5
$$

contradicts the non-fifth-power conclusion supplied by the clean channel.

## 4. Role in the whole proof

This theorem is the endpoint of the local clean-channel route in `BranchB.lean`.

Two independent streams have already been prepared.

1. The Fermat-equation stream: `body5_eq_fifth_power_of_fermat` identifies the full body with `x^5`.
2. The local-divisibility stream: `not_fifth_power_body_of_clean` excludes perfect fifth powers for bodies carrying a clean channel.

This theorem is the adapter joining those streams. It introduces no new number theory; it merely supplies an existing existential witness to an existing negation.

It is not an unconditional elimination of Branch B. The task of supplying `CleanGN5Channel (z-y) y q` is left to the subsequent provider interface. According to the repository comments, the final unconditional FLT5 route instead proceeds through signed five-adic normalization and golden descent.

## 5. Direct dependencies

### 5.1 `CounterexamplePack`

The theorem directly uses only:

- `hPack.hx : 0 < x`
- `hPack.hEq : Fermat5Equation x y z`

### 5.2 `CleanGN5Channel`

`hClean` packages primality of `q`, divisibility of `GN5`, avoidance of the gap, and the no-lift condition. Its fields are not unfolded here; the whole structure is passed to `not_fifth_power_body_of_clean`.

### 5.3 `right_lt_of_fermat5Equation`

```lean
right_lt_of_fermat5Equation hPack.hx hPack.hEq : y < z
```

### 5.4 `body5_eq_fifth_power_of_fermat`

```lean
body5_eq_fifth_power_of_fermat hyz hPack.hEq :
  Body5 (z - y) y = x ^ 5
```

### 5.5 `not_fifth_power_body_of_clean`

```lean
not_fifth_power_body_of_clean hClean :
  ¬ ∃ x : ℕ, (z - y) * GN5 (z - y) y = x ^ 5
```

Because `Body5` is definitionally equal to this product, Lean aligns the goals without an explicit rewrite.

## 6. Proof flow

### 6.1 Build the order condition

```lean
have hyz : y ≤ z :=
  Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
```

This is the safety condition required for natural subtraction.

### 6.2 Apply the non-fifth-power statement

```lean
apply not_fifth_power_body_of_clean hClean
```

In Lean, `¬ P` is a function `P → False`. The goal changes from `False` to the existence of a fifth-power representation.

### 6.3 Supply the witness

```lean
exact ⟨x, body5_eq_fifth_power_of_fermat hyz hPack.hEq⟩
```

The witness is the original Fermat variable `x`, and the previous bridge supplies the required equality.

## 7. Lean-specific processing

### 7.1 `Nat.le_of_lt`

The strict inequality is explicitly weakened to match the type required by the bridge theorem.

### 7.2 Negation as a function

`not_fifth_power_body_of_clean hClean` consumes an existential proof and returns `False`. The `apply` tactic uses this function backward.

### 7.3 Existential construction

`⟨x, proof⟩` constructs the witness for `∃ x, ...`; no search is needed.

### 7.4 Definitional equality

The consumer states the product directly, while the bridge states `Body5`. Since the definition of `Body5` is transparent, Lean reduces both expressions to the same term.

## 8. Redundancy and duplication

The proof is only three logical steps and contains little genuine redundancy.

The derivation of `y≤z` may recur in similar consumers. A reusable lemma such as

```lean
theorem CounterexamplePack.y_le_z
    {x y z : ℕ} (h : CounterexamplePack x y z) : y ≤ z :=
  (right_lt_of_fermat5Equation h.hx h.hEq).le
```

could remove repetition, though the current one-line derivation may not justify expanding the API.

## 9. Optimization candidates

### 9.1 Use `.le`

The current expression may be shortened to:

```lean
(right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
```

### 9.2 Compress into one `exact`

A compact proof is possible:

```lean
exact (not_fifth_power_body_of_clean hClean)
  ⟨x, body5_eq_fifth_power_of_fermat
    (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le hPack.hEq⟩
```

The existing version is preferable for readability because it separates the order fact, the consumer, and the witness.

### 9.3 Add a `Body5` wrapper

A wrapper whose conclusion is phrased directly with `Body5` would hide the definitional equality. It would add no mathematics and would duplicate the API, so the present design is reasonable.

These are proposals only; no Lean build was run while preparing this article.

## 10. Required Mathlib imports and import optimization

The generated standalone source imports `Mathlib`, and the repository source confirms that the theorem works in that environment.

The theorem itself requires only natural-number order conversion, existential and negation logic, and the project-local declarations from earlier modules.

At the modular level, `BranchB.lean` should need project imports providing `CounterexamplePack`, `CleanGN5Channel`, and the `Body5` bridges. `DkMath.FLT.Five.CleanChannel`, together with transitive access to `Basic` and `GN5`, is a plausible minimal route.

However, the exact import line of the original modular `BranchB.lean` is not retained in the generated standalone excerpt used here. Therefore the minimal import set is partly conjectural and should be verified by an import audit or `lake env lean`. No Lean build was performed in this task.

## 11. Comparator challenge suitability

This theorem is well suited to a Comparator challenge.

### Challenge A — Reconstruct the adapter

Provide only the declaration type and these lemmas:

- `right_lt_of_fermat5Equation`
- `body5_eq_fifth_power_of_fermat`
- `not_fifth_power_body_of_clean`

The solution must recognize negation as a function, choose `x` as the witness, and construct `y≤z`.

### Challenge B — Recognize definitional equality

Ask why no explicit rewrite is needed between `Body5 g y` and `g * GN5 g y`.

### Challenge C — Compare explicit and automated proofs

Compare the current proof term with an `aesop`-style proof in dependency transparency, readability, and robustness.

## 12. Confirmed facts and conjectural points

Confirmed:

- declaration name, type, and proof body;
- placement immediately after `body5_eq_fifth_power_of_fermat`;
- termination of `BranchB.lean` immediately after this declaration;
- the generated standalone source imports `Mathlib`.

Conjectural or audit candidates:

- the minimal import set for modular `BranchB.lean`;
- the repository-wide benefit of adding `CounterexamplePack.y_le_z`;
- the usefulness of a `Body5`-phrased wrapper.

The existing PDFs provide narrative context, but the repository Lean source is the final authority for the declaration and proof steps recorded here.

## 13. Next declaration

Next read `DkMath.FLT.Five.BranchBCleanGN5ChannelProvider`.

```lean
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

This article gives the local refuter assuming a clean channel. The next declaration defines the conditional provider interface responsible for supplying such a channel to every Branch-B candidate, cleanly separating local contradiction from prime supply.

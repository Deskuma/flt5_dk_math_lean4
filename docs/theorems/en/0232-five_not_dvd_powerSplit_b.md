# 0232 — `five_not_dvd_powerSplit_b`

## Lean type

```lean
private theorem five_not_dvd_powerSplit_b
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    ¬ 5 ∣ p.powerSplit.b := by
  intro h5b
  have h25 : 25 ∣ p.powerSplit.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [p.powerSplit.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [p.powerSplit.fiveAdic.residual_mod_twentyFive] at hzero
  omega
```

This is a `private theorem`. It proves that the fifth-power base `b` carried by the exact five-adic power split inside `SignedSquareGoldenExceptionalPacket` is not divisible by five.

## Mathematical statement

The statement is simply

$$
5\nmid b.
$$

The source of this information, however, is not a gcd hypothesis. It comes from the modulo-25 certificate stored in the packet's five-adic residual data.

Through `powerSplit.residual_eq`, the residual has an explicit fifth-power shape. If one assumes

$$
5\mid b,
$$

then one may write $b=5c$. Substituting this into the residual formula inserts extra powers of five, and in particular gives

$$
25\mid \mathrm{residual}.
$$

On the other hand, `residual_mod_twentyFive` fixes the residual modulo 25 to a known nonzero value. Hence divisibility by 25 would force

$$
\mathrm{residual}\equiv0\pmod{25},
$$

contradicting the stored modulo-25 certificate.

Thus the theorem converts residual congruence information into the **5-primitivity** of the fifth-power base `b`.

## Role in the full proof

Declaration 0231 `SignedGoldenRamifierStrippedPacket` requires the field

```lean
five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
```

and the present theorem is the private certificate used to fill that field.

The immediately following constructor theorem uses it as

```lean
have h5b : ¬ 5 ∣ p.powerSplit.b := five_not_dvd_powerSplit_b p
```

and then combines it with

$$
N(\beta)=b^5
$$

to derive

$$
5\nmid N(\beta).
$$

That in turn excludes another visible ramifier factor: if

$$
\beta=\tau\gamma,
$$

then norm multiplicativity together with $N(\tau)=5$ would force $5\mid N(\beta)$, a contradiction. Therefore

$$
\tau\nmid\beta.
$$

Consequently 0232 is the starting point of the strippedness chain

$$
5\nmid b
\Longrightarrow
5\nmid N(\beta)
\Longrightarrow
\tau\nmid\beta.
$$

The same invariant is later reused in conjugate-coprime and unit-sector arguments, so this theorem provides a persistent five-adic primitive condition throughout the exceptional branch.

## Direct dependencies

The main direct dependencies are:

- `SignedSquareGoldenExceptionalPacket`
- the packet's `powerSplit`
- `p.powerSplit.b`
- `p.powerSplit.residual_eq`
- `p.powerSplit.fiveAdic.residual`
- `p.powerSplit.fiveAdic.residual_mod_twentyFive`
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

The proof does not use `GoldenInt` or `goldenNorm` directly. It is closed entirely on the natural-number / integer five-adic residual side.

## Proof flow

### 1. Assume `5 ∣ b`

```lean
intro h5b
```

Since the goal is `¬ 5 ∣ b`, the proof proceeds by contradiction.

### 2. Construct divisibility of the residual by 25

```lean
have h25 : 25 ∣ p.powerSplit.fiveAdic.residual := by
  rcases h5b with ⟨c, hc⟩
  use 5 ^ 4 * c ^ 5
  rw [p.powerSplit.residual_eq, hc]
  ring
```

The divisibility witness gives $b=5c$. After substitution into the explicit residual formula, the proof supplies

```lean
5 ^ 4 * c ^ 5
```

as the quotient witnessing divisibility by 25. `ring` closes the resulting polynomial identity.

### 3. Convert divisibility by 25 into a zero remainder

```lean
have hzero := Nat.mod_eq_zero_of_dvd h25
```

This yields

$$
\mathrm{residual}\bmod25=0.
$$

### 4. Rewrite using the packet's modulo-25 certificate

```lean
rw [p.powerSplit.fiveAdic.residual_mod_twentyFive] at hzero
omega
```

After rewriting the residual modulo 25 to its certified explicit value, `hzero` becomes an impossible arithmetic statement. `omega` closes the contradiction.

## Lean-specific processing

`rcases h5b with ⟨c, hc⟩` extracts the quotient witness from the divisibility hypothesis. The equation `hc` can then be used directly by `rw` to replace `b` with its multiple-of-five form.

`use 5 ^ 4 * c ^ 5` explicitly constructs the quotient for `25 ∣ residual`. Compared with an opaque divisibility tactic, this keeps the additional five-adic mass visible in the proof term.

`Nat.mod_eq_zero_of_dvd` is the standard bridge from divisibility to a modular equality. The last step is then purely arithmetic after the known residue modulo 25 has been rewritten into the hypothesis.

## Redundancy and duplication

Conceptually, the theorem factors into two reusable ideas:

$$
5\mid b\Longrightarrow25\mid\mathrm{residual}
$$

and

$$
\mathrm{residual}\not\equiv0\pmod{25}.
$$

If the same pattern occurs for other residual bases, a general helper such as `five_dvd_base_implies_twentyFive_dvd_residual` could avoid repeating the witness arithmetic.

The explicit quotient `5^4*c^5` is also tied closely to the concrete residual exponent. A valuation-based proof could express the same idea more conceptually. The current proof, however, has the advantage of being elementary, lightweight, and directly auditable.

## Optimization candidates

1. **Abstract through a five-adic valuation lemma**
   - express that `5 ∣ b` forces sufficiently large 5-adic valuation of the residual.

2. **Introduce a generic mod-25 contradiction helper**
   - combine `25 ∣ n` with a known nonzero `n % 25` value.

3. **Store `¬ 25 ∣ residual` as a semantic packet invariant**
   - if downstream code never needs the exact residue value, this could expose the relevant consequence more directly.

4. **Keep the current explicit witness proof**
   - it avoids additional valuation infrastructure and makes the exact five-power accounting transparent.

The current theorem is already short and structurally clear, so local proof compression is not a high-priority optimization.

## Required Mathlib imports and import optimization

The standalone artifact uses `import Mathlib`. The direct Mathlib surface of this theorem is relatively small:

- natural-number divisibility
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

The surrounding `SignedGoldenRamifierStripped.lean` module additionally uses golden integers, norms, primality, and cast machinery, so the true minimal import set must be measured at module scope rather than from this theorem alone.

No Lean build is run in this museum pass, so the exact minimal import set is unverified and is recorded only as an optimization candidate.

## Comparator challenge suitability

Yes. Natural variants include:

- A: the current explicit divisibility witness plus modulo-25 contradiction
- B: a proof using factorization / valuation APIs
- C: a proof centered on `Nat.ModEq`
- D: a packet design storing `¬ 25 ∣ residual` directly

Useful comparison axes include proof size, import cost, visibility of the five-adic mechanism, generalizability, elaboration complexity, and tactic dependence.

The contrast between A and B is especially instructive: it compares elementary witness arithmetic with a valuation-level abstraction for FLT5 proof auditing.

## Relation to the PDFs and Lean source

The formal source of truth is the generated `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` section embedded in `Flt5DkMath/FLT5StandAlone.lean` on the `docs/flt5-theorem-museum-v2` branch.

In source order, this private theorem appears immediately after 0231 `SignedGoldenRamifierStrippedPacket`. The following constructor theorem `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` uses it to populate the packet's `five_not_dvd_b` field.

Japanese and English PDFs also exist on the target branch, but the exact page or section corresponding to this private theorem was not identified in this pass, so no page reference is inferred.

## Next declaration to read

The next declaration in dependency order is **0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`**:

```lean
private theorem nonempty_signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    Nonempty (SignedGoldenRamifierStrippedPacket u v w) := by
  ...
```

Declaration 0232 supplies the five-adic primitive certificate `5 ∤ b`. Declaration 0233 then constructs all remaining data required by the structure: the quotient witness `k`, the stripped element `beta`, its norm identity and second-coordinate formula, `5 ∤ N(beta)`, and finally `tau ∤ beta`.

It is therefore the main constructor theorem implementing the ramifier-stripping argument encoded by 0231.

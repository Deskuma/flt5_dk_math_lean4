# 0087 — `nonempty_signedFiveAdicPowerSplit_of_packet`

## Lean type

```lean
private theorem nonempty_signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nonempty (SignedFiveAdicPowerSplit u v w) := by
  ...
```

This declaration is a `private theorem`, so it is not part of the public module API. It serves as the internal existence proof used by the public `signedFiveAdicPowerSplit_of_packet` definition.

## Mathematical statement

Given `SignedFiveAdicPacket u v w`, there exist positive coprime natural numbers $a,b$ such that the packet's three principal quantities admit the exact power split

$$
\operatorname{carrier}=5^4a^5,
$$

$$
\operatorname{residual}=5b^5,
$$

$$
\operatorname{distinguished}=5ab.
$$

Lean does not return the witnesses as a bare `∃ a b, ...`. Instead it constructs the `SignedFiveAdicPowerSplit u v w` record introduced in 0083 and proves that this type is `Nonempty`.

## Role in the full proof

0082 established

$$
\gcd(\operatorname{carrier},\operatorname{residual})=5,
$$

and 0083 defined the desired normal form as a record type. Articles 0084–0086 then prepared auxiliary properties of that record for later use.

This theorem is the first declaration that actually constructs data of that record from a packet.

Conceptually, the flow is

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\text{strip the common factor }5
\Longrightarrow
\text{coprime fifth-power factor split}
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$

It is therefore the effective constructor theorem of the `SignedFiveAdicPowerSplit` layer.

## Direct dependencies

The main direct dependencies are:

- `SignedFiveAdicPacket`
- `SignedFiveAdicPowerSplit`
- `signedFiveAdicPacket_gcd_eq_five` (0082)
- `fifth_power_factor_split` (0027)
- packet fields
  - `p.five_dvd_carrier`
  - `p.five_dvd_distinguished`
  - `p.residual_shape`
  - `p.residual_mod_twentyFive`
  - `p.factor_eq`
  - `p.carrier_pos`
  - `p.residual_pos`
- `Nat.mul_div_cancel'`
- `Nat.coprime_div_gcd_div_gcd`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.Coprime.mul_left`
- `Nat.eq_of_mul_eq_mul_left`
- `Nat.pow_left_injective`
- `Nat.coprime_pow_left_iff`
- `Nat.coprime_pow_right_iff`
- `Nat.mod_eq_zero_of_dvd`
- tactics `ring`, `omega`, `norm_num`

## Proof flow

### 1. Strip one common factor 5

Set

```lean
let c := p.carrier / 5
let r := p.residual / 5
let d := p.distinguished / 5
```

The packet already contains divisibility by 5 for `carrier` and `distinguished`. For `residual`, the proof uses

```lean
p.residual_shape
```

to obtain

$$
\operatorname{residual}=5+25M=5(1+5M),
$$

hence $5\mid\operatorname{residual}$.

Therefore `Nat.mul_div_cancel'` gives

$$
\operatorname{carrier}=5c,
$$

$$
\operatorname{residual}=5r,
$$

$$
\operatorname{distinguished}=5d.
$$

### 2. Prove that the stripped factors $c,r$ are coprime

By 0082,

$$
\gcd(\operatorname{carrier},\operatorname{residual})=5.
$$

Using `Nat.coprime_div_gcd_div_gcd`, dividing both numbers by their gcd yields coprime quotients:

$$
\frac{\operatorname{carrier}}5=c,
\qquad
\frac{\operatorname{residual}}5=r.
$$

Lean obtains this as

```lean
have hcopcr : Nat.Coprime c r := by
  have h := Nat.coprime_div_gcd_div_gcd
    (show 0 < Nat.gcd p.carrier p.residual by rw [hgcd]; decide)
  simpa [c, r, hgcd] using h
```

### 3. Prove $5\nmid r$ modulo 25

If $5\mid r$, then from

$$
\operatorname{residual}=5r
$$

we get $25\mid\operatorname{residual}$. But the packet records

$$
\operatorname{residual}\bmod25=5,
$$

which is impossible.

This is essentially the same mod-25 no-extra-five argument used by 0084 `five_not_dvd_b`.

From this the proof obtains

$$
\gcd(5,r)=1
$$

and then

$$
\gcd(25,r)=1.
$$

### 4. Normalize the original fifth-power product

The packet contains

$$
\operatorname{carrier}\cdot\operatorname{residual}
  =\operatorname{distinguished}^5.
$$

Substituting

$$
\operatorname{carrier}=5c,
\quad
\operatorname{residual}=5r,
\quad
\operatorname{distinguished}=5d
$$

and rearranging gives

$$
(25c)r=(5d)^5.
$$

The proof also derives

$$
\gcd(25c,r)=1
$$

using `h25copr.mul_left hcopcr`.

### 5. Apply `fifth_power_factor_split`

Apply 0027 to

$$
(25c)r=(5d)^5,
\qquad
\gcd(25c,r)=1.
$$

It yields witnesses $A,b$ satisfying

$$
25c=A^5,
$$

$$
r=b^5.
$$

This is the central step of the theorem. Arithmetic specific to the five-adic packet is connected to the previously proved general factor-splitting result: when a product of coprime factors is a fifth power, each factor is itself a fifth power.

### 6. Strip one more factor 5 from $A$

Since $25c=A^5$, we have $5\mid A^5$. Because 5 is prime,

$$
5\mid A.
$$

Write $A=5a$. Then

$$
25c=(5a)^5.
$$

Cancelling 25 gives

$$
c=5^3a^5.
$$

Hence

$$
\operatorname{carrier}=5c=5^4a^5.
$$

Likewise, from $r=b^5$,

$$
\operatorname{residual}=5b^5.
$$

### 7. Recover the distinguished equation by injectivity of fifth powers

Using `p.factor_eq` and the two equations above,

$$
\operatorname{distinguished}^5=(5ab)^5.
$$

Fifth powers are injective on natural numbers, so

$$
\operatorname{distinguished}=5ab.
$$

Lean performs this with

```lean
apply Nat.pow_left_injective (by decide : 5 ≠ 0)
```

and reduces the goal to equality of fifth powers.

### 8. Prove $a,b>0$ and $\gcd(a,b)=1$

If $a=0$, then `carrier = 0`; if $b=0`, then `residual = 0`. Both contradict positivity fields already stored in the packet, so

$$
a>0,
\qquad
b>0.
$$

For coprimality, substitute

$$
c=5^3a^5,
\qquad
r=b^5
$$

into `Nat.Coprime c r`. Removing the left factor $5^3$ yields

$$
\gcd(a^5,b^5)=1.
$$

Then `Nat.coprime_pow_left_iff` and `Nat.coprime_pow_right_iff` return

$$
\gcd(a,b)=1.
$$

Finally all fields are assembled into a `SignedFiveAdicPowerSplit` record and wrapped as a `Nonempty` witness.

## Lean-specific processing

This theorem contains substantial Lean-specific bookkeeping beyond the mathematics itself, especially natural-number division, existential witnesses, and record construction.

The important points are:

1. Define `c := carrier / 5` and then recover exact equalities from divisibility.
2. Use `Nat.coprime_div_gcd_div_gcd` to obtain coprimality after gcd stripping.
3. In the proof of $5\nmid r$, destruct a divisibility witness with `rcases` and construct a witness for divisibility by 25 using `ring`.
4. Destructure the existential output of `fifth_power_factor_split` as

```lean
rcases ... with ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
```

5. Pull $5\mid A$ back from $5\mid A^5$ with `Nat.Prime.dvd_of_dvd_pow`.
6. Cancel 25 in an equality using `Nat.eq_of_mul_eq_mul_left`.
7. Use injectivity of fifth powers for the distinguished equation.
8. Establish positivity via `by_contra` + `omega` + `norm_num` by ruling out zero.
9. Return an anonymous structure literal wrapped as a `Nonempty` witness.

## Redundancy and duplication

The clearest duplication is the mod-25 proof of $5\nmid r$. It has essentially the same shape as 0084 `five_not_dvd_b`, but is reimplemented for the intermediate quotient `r`.

There may also be reusable patterns in:

- turning divisibility by 5 into an exact quotient equality,
- proving positivity by contradiction from a zero factor,
- descending coprimality from fifth powers to their bases.

However, this theorem is private constructor implementation code and several intermediate quantities are local to it. Splitting every such step into helpers could make the overall construction harder to read rather than easier.

## Optimization candidates

### Candidate A — shared mod-25 no-extra-five helper

A general lemma saying that

$$
x=5r,
\qquad
x\bmod25=5
$$

implies $5\nmid r$ would remove duplication between 0084 and this theorem.

### Candidate B — quotient-by-exact-gcd helper

A helper that packages

```lean
gcd carrier residual = 5
c := carrier / 5
r := residual / 5
Nat.Coprime c r
```

would make the gcd-stripping intention more explicit.

### Candidate C — valuation-based route

The packet also stores five-adic valuation information, so $5\nmid r$ could potentially be derived from valuation one rather than modulo 25. The current proof, however, is elementary and easy to audit.

### Candidate D — direct constructor API

The current design first proves

```lean
private theorem ... : Nonempty (SignedFiveAdicPowerSplit ...)
```

and then the following `noncomputable def` uses `Classical.choice` to select a witness. This cleanly separates specification from selection, but a direct constructive record-returning proof could potentially eliminate the classical choice layer.

Whether that is desirable depends on the witness interface of the factor-splitting theorem and on the module-wide API policy.

## Required Mathlib imports and import optimization

The generated standalone artifact on the target branch is built with `import Mathlib`. Its manifest identifies this declaration as belonging to `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean`.

The Mathlib functionality directly used here includes natural-number gcd/coprimality/divisibility, primes, powers, natural-number division, and the `ring`, `omega`, and `norm_num` tactics.

Thus `import Mathlib` is probably broader than necessary for this theorem alone. However, the exact import list of the split source module was not validated by a Lean build in this run, so no specific minimal module list is asserted.

A safe import-optimization process would enumerate the direct source dependencies and tactics of `SignedFiveAdicPowerSplit.lean`, narrow imports incrementally, and confirm each step with a Lean build. No build is performed in this task.

## Comparator challenge suitability

This theorem is very suitable for a Comparator challenge. It offers substantially richer alternatives than the preceding one-line adapters.

Possible comparisons include:

1. The current gcd stripping + mod 25 + `fifth_power_factor_split` route.
2. A route centered on five-adic valuation.
3. A route using a reusable quotient/gcd-stripping helper.
4. A direct constructive record-returning route instead of `Nonempty` + `Classical.choice`.

Useful evaluation criteria are:

- proof-term size,
- mathematical transparency,
- presence or absence of classical dependencies,
- reusability of helper lemmas,
- coupling to the packet API,
- robustness under Lean / Mathlib updates.

## Correspondence with the PDFs

The existing Japanese and English PDFs are treated as narrative background sources. In this run, GitHub code search returned a 502 upstream error, so a page or section corresponding one-to-one with this private constructor theorem could not be confirmed.

Accordingly, no PDF theorem number, page number, or wording is guessed. The formal final authority is the actual Lean declaration contained in `Flt5DkMath/FLT5StandAlone.lean` on the target branch.

## Next declaration to read

The next declaration in the source is

```lean
noncomputable def signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    SignedFiveAdicPowerSplit u v w :=
  Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

It selects one actual `SignedFiveAdicPowerSplit` witness from the `Nonempty` result proved here and exposes it as an API directly consumable by subsequent theorems.

Thus the next dependency step is

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit})
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}.
$$
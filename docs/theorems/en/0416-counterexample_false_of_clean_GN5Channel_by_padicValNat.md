# 0416 `counterexample_false_of_clean_GN5Channel_by_padicValNat`

## Declaration kind

`theorem`

## Lean type

```lean
theorem counterexample_false_of_clean_GN5Channel_by_padicValNat
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z := Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  have hBodyEq : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hBodyEq]
    exact hClean.dvd_body
  have hqDivX : q ∣ x := hClean.prime.dvd_of_dvd_pow hqDivPow
  have hlower : 5 ≤ padicValNat q (x ^ 5) :=
    padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
  have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
    simpa [Body5] using padicValNat_clean_body_eq_one hClean
  rw [hBodyEq] at hexact
  omega
```

This theorem proves, purely through `padicValNat`, that a primitive FLT5 candidate `CounterexamplePack x y z` cannot coexist with a clean prime channel for the natural gap `z - y`.

## Mathematical statement

From the Fermat-five equation

$$
x^5+y^5=z^5
$$

and $y\le z$, put

$$
g=z-y.
$$

The fifth-power body satisfies

$$
\operatorname{Body5}(g,y)=g\,GN_5(g,y)=x^5.
$$

On the other hand, `CleanGN5Channel g y q` says that the prime $q$ occurs cleanly in the body. By 0415,

$$
v_q(g\,GN_5(g,y))=1.
$$

But the body is exactly $x^5$. The clean channel gives $q\mid x^5$, primality gives $q\mid x$, and 0413 yields

$$
5\le v_q(x^5).
$$

Since the body identity identifies these as valuations of the same natural number, one gets

$$
5\le v_q(x^5)=1,
$$

which is impossible.

Thus

$$
\operatorname{CounterexamplePack}(x,y,z)
\land
\operatorname{CleanGN5Channel}(z-y,y,q)
\Longrightarrow \bot.
$$

## Role in the overall proof

This theorem is the endpoint of the independent proof route in `Valuation.lean`.

`CleanChannel.lean` already contains a direct divisibility proof that a clean channel prevents the full body from being a fifth power. `Valuation.lean` repackages the same obstruction as

```text
fifth power   -> q-adic valuation ≥ 5
clean channel -> q-adic valuation = 1
```

0413 `padicValNat_lower_bound_d5` supplies the fifth-power lower bound, 0414 supplies the clean-body upper bound, 0415 sharpens that bound to exact valuation one, and 0416 transports both statements through the Fermat body identity and closes the contradiction.

Therefore this theorem is not the only route required by the main FLT5 closure. It is an independent valuation proof of the clean-channel obstruction. The module comment in the canonical standalone source explicitly describes it as an independent `padicValNat` proof of the contradiction already available directly in `CleanChannel.lean`.

## Direct dependencies

### `CounterexamplePack`

From

```lean
hPack : CounterexamplePack x y z
```

the theorem directly uses at least

```lean
hPack.hx : 0 < x
hPack.hEq : Fermat5Equation x y z
```

`hPack.hx` supplies the positivity required by 0413, while `hPack.hEq` supplies the Fermat equation used by the gap/body identity.

### `CleanGN5Channel`

The hypothesis

```lean
hClean : CleanGN5Channel (z - y) y q
```

directly supplies

```lean
hClean.prime
hClean.dvd_body
```

and, through 0415, the exact valuation derived ultimately from `not_sq_dvd_body`.

### `right_lt_of_fermat5Equation`

```lean
right_lt_of_fermat5Equation hPack.hx hPack.hEq : y < z
```

is weakened with `Nat.le_of_lt` to obtain $y\le z$, allowing natural-number subtraction `z - y` to represent the intended gap.

### `body5_eq_fifth_power_of_fermat`

```lean
body5_eq_fifth_power_of_fermat hyz hPack.hEq :
  Body5 (z - y) y = x ^ 5
```

is the central bridge connecting the valuation route to the Fermat equation.

### `Nat.Prime.dvd_of_dvd_pow`

```lean
hClean.prime.dvd_of_dvd_pow hqDivPow
```

gives

$$
q\mid x^5 \Longrightarrow q\mid x.
$$

### `padicValNat_lower_bound_d5`

Declaration 0413.

```lean
padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
```

yields

```lean
5 ≤ padicValNat q (x ^ 5)
```

for the fifth-power side.

### `padicValNat_clean_body_eq_one`

Declaration 0415.

```lean
padicValNat_clean_body_eq_one hClean
```

yields

```lean
padicValNat q ((z - y) * GN5 (z - y) y) = 1
```

and unfolding `Body5` aligns this result with the abstraction used in 0416.

## Proof flow

### 1. Establish the gap order condition

```lean
have hyz : y ≤ z :=
  Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
```

A positive left term in a Fermat-five equation forces $y<z$, so the natural gap `z - y` behaves as the ordinary difference.

### 2. Identify the body with a fifth power

```lean
have hBodyEq : Body5 (z - y) y = x ^ 5 :=
  body5_eq_fifth_power_of_fermat hyz hPack.hEq
```

This equality is the transport path for the rest of the proof. The same number can now be viewed either as a clean body or as a fifth power.

### 3. Show that the clean prime divides $x^5$

```lean
have hqDivPow : q ∣ x ^ 5 := by
  rw [← hBodyEq]
  exact hClean.dvd_body
```

`hClean.dvd_body` is the existing API stating that the clean prime divides the full body.

### 4. Descend divisibility to the base

```lean
have hqDivX : q ∣ x :=
  hClean.prime.dvd_of_dvd_pow hqDivPow
```

Because $q$ is prime, divisibility of a fifth power forces divisibility of the base.

### 5. Obtain the fifth-power valuation lower bound

```lean
have hlower : 5 ≤ padicValNat q (x ^ 5) :=
  padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
```

This is a direct reuse of 0413.

### 6. Obtain exact valuation one on the clean body

```lean
have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
  simpa [Body5] using padicValNat_clean_body_eq_one hClean
```

0415 is stated for `(z-y) * GN5 (z-y) y`; unfolding `Body5` shows that this is definitionally the same body.

### 7. Transport the exact valuation through the body identity

```lean
rw [hBodyEq] at hexact
```

After rewriting,

```lean
hexact : padicValNat q (x ^ 5) = 1
```

has the same valuation target as `hlower`.

### 8. Close the arithmetic contradiction

```lean
omega
```

The facts `5 ≤ ...` and `... = 1` are incompatible, so the goal `False` is discharged.

## Lean-specific details

### `Nat.le_of_lt`

The body-identity API expects `y ≤ z`, whereas the previously proved theorem returns the stronger fact `y < z`. This step is only order weakening.

### `rw [← hBodyEq]`

The goal `q ∣ x ^ 5` is rewritten back to the body form understood directly by the clean-channel API. Mathematically this is only substitution of equals.

### `dvd_of_dvd_pow`

This is the prime-specific step. It would not hold for an arbitrary composite divisor; the field `hClean.prime` is essential here.

### `simpa [Body5]`

This removes the definitional difference between the statement of 0415 and the preferred `Body5` abstraction used by 0416. No new mathematical argument occurs at this step.

### `rw [hBodyEq] at hexact`

The rewrite is performed inside a local hypothesis rather than in the goal. It makes the `padicValNat` target in `hexact` syntactically identical to that in `hlower`.

### `omega`

Only elementary linear arithmetic remains at the end. All valuation theory has already been encapsulated in 0413 and 0415.

## Redundancy and duplication

### The mathematical obstruction duplicates the direct clean-channel route

`not_fifth_power_body_of_clean` in `CleanChannel.lean` already excludes a fifth-power body from square-divisibility considerations. 0416 proves the same obstruction again in valuation language.

This is intentional rather than accidental duplication: the canonical source explicitly labels the valuation module as an independent `padicValNat` proof.

### `hqDivPow` to `hqDivX` is preprocessing for the lower-bound theorem

0413 expects `q ∣ x`, so 0416 first recovers base divisibility from `q ∣ x^5`. One could define a variant of 0413 that starts directly from `q ∣ x^5`, but the current 0413 has a cleaner and more reusable statement.

### `Body5` and product form are converted back and forth

0415 uses the product explicitly, while 0416 uses the `Body5` abstraction. This creates the small `simpa [Body5]` adapter step.

## Optimization candidates

### 1. Extract a generic valuation-contradiction helper

A general helper could turn

```text
body = x^5
q ∣ body
v_q(body) = 1
```

into `False`. This would shorten 0416, although the present concrete proof makes the FLT5 transport structure very visible.

### 2. Provide a `Body5`-shaped exact-valuation wrapper

A theorem such as `padicValNat_clean_Body5_eq_one` could remove

```lean
simpa [Body5]
```

from 0416. Since the adaptation occurs only once here, adding another public theorem may not be worthwhile.

### 3. Separate common transport from the direct and valuation routes

The path from `hBodyEq` and `hClean.dvd_body` to `q ∣ x^5` is structurally reusable. If more clean-channel proof routes are added, this transport layer could become a small shared helper.

### 4. No strong reason to replace `omega`

The final contradiction is exactly the kind of elementary arithmetic `omega` handles well. One could expose an intermediate `5 ≤ 1`, but that would make the Lean script longer without adding mathematical content.

## Required Mathlib imports and import optimization

The canonical standalone file `Flt5DkMath/FLT5StandAlone.lean` uses

```lean
import Mathlib
```

The Mathlib functionality used directly or through immediate dependencies of 0416 includes at least:

- `padicValNat`
- `Nat.Prime.dvd_of_dvd_pow`
- natural-number order operations such as `Nat.le_of_lt`
- divisibility
- `omega`

The production module's individual imports cannot be determined from the generated standalone file alone, and no Lean build is performed in this run. Therefore the exact minimal import set is unverified. It is plausible that `import Mathlib` can be reduced to valuation-, prime-, and `omega`-related imports, but that requires build validation.

## Comparator challenge suitability

**Yes. It is especially suitable when 0413–0416 are bundled as one challenge.**

The challenge would test the following sequence:

1. derive the body identity from the Fermat equation;
2. transport clean-channel divisibility to the fifth power;
3. descend prime divisibility to the base;
4. obtain valuation $\ge5$ on the fifth-power side;
5. obtain exact valuation $=1$ on the clean-body side;
6. rewrite both onto the same quantity and close the contradiction.

This exercises `padicValNat`, rewrite orientation, unfolding of `Body5`, prime-power divisibility, and arithmetic closure. It therefore has more Lean-specific judgment points than a simple polynomial-normalization challenge.

It does not, however, test the research-heavy golden-integer, unit-class, or infinite-descent part of the FLT5 development. It is specifically a challenge for the local valuation obstruction.

## Next declaration to read

The next declaration is **0417 `FLT5Target`** in `Main.lean`:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

Its declaration kind is `abbrev`.

With 0416 the independent valuation route is complete. The development then enters its public endpoint layer. `FLT5Target` names the final exponent-five statement over positive natural numbers and becomes the codomain of the following conditional receivers and the unconditional theorem `flt5Target`.
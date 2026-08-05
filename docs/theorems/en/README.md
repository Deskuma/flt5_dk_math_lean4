# FLT5 Theorem Museum — English Translation

> This series is translated from the Japanese canonical edition.

## About this museum

This is a declaration-by-declaration reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five. It follows explanatory dependency order from the foundational interface toward the final theorem.

The Japanese edition is canonical. The English edition preserves the content, declaration names, formulas, and section structure. The Lean source in the repository remains the final mathematical and formal authority.

## Numbering

Each article uses a matching four-digit dependency-order number and declaration name in both languages.

Each article records the Lean type, mathematical statement, role in the complete proof, direct dependencies, proof flow, Lean-specific processing, redundancy, optimization candidates, Mathlib imports, Comparator challenge suitability, and the next declaration. Verified source facts are distinguished from unverified proposals.

## Catalogue

- [0001 — `Fermat5Equation`](./0001-Fermat5Equation.md) — The minimal proposition-valued interface for the exponent-five equation.
- [0002 — `CounterexamplePack`](./0002-CounterexamplePack.md) — Packages positivity, primitivity, and the equation as input data.
- [0003 — `fifth_sub_eq_of_add_eq`](./0003-fifth_sub_eq_of_add_eq.md) — Converts the additive equation into a difference-of-fifth-powers identity over natural numbers.
- [0004 — `right_lt_of_fermat5Equation`](./0004-right_lt_of_fermat5Equation.md) — Derives $y<z$ from a positive left term and passes order information to gap positivity.
- [0005 — `gap_pos_of_fermat5Equation`](./0005-gap_pos_of_fermat5Equation.md) — Converts $y<z$ into $0<z-y$ and establishes a positive gap coordinate.
- [0006 — `GN5`](./0006-GN5.md) — The homogeneous degree-four residual kernel obtained after extracting the gap from a fifth-power difference.
- [0007 — `GN5_eq_homogeneous_cyclotomic`](./0007-GN5_eq_homogeneous_cyclotomic.md) — Identifies `GN5` with the standard homogeneous fifth cyclotomic factor.
- [0008 — `GN5_eq_gap_mul_add_five_mul_y_pow_four`](./0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) — Decomposes `GN5` into a multiple of the gap and the remainder $5y^4$ for congruence analysis.
- [0009 — `GN5_eq_g_pow_four_add_five_mul`](./0009-GN5_eq_g_pow_four_add_five_mul.md) — Decomposes `GN5` into $g^4$ and a multiple of $5$ for five-adic analysis.
- [0010 — `add_pow_five_eq_add_mul_GN5`](./0010-add_pow_five_eq_add_mul_GN5.md) — Splits the fifth power into the base term $y^5$ and a `GN5` body carrying the gap as a factor.
- [0011 — `add_pow_five_sub_eq_mul_GN5`](./0011-add_pow_five_sub_eq_mul_GN5.md) — Converts the additive form into the direct factorization API connecting the fifth-power difference with the gap and `GN5`.
- [0012 — `pow_five_sub_pow_five_eq_gap_mul_GN5`](./0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) — Connects the abstract gap to the concrete natural-number difference $z-y$.
- [0013 — `GN5_one_one`](./0013-GN5_one_one.md) — Establishes $GN5(1,1)=31$ and passes a concrete value to the finite-prime escape no-lift demonstration.
- [0014 — `GN5_two_one`](./0014-GN5_two_one.md) — Establishes $GN5(2,1)=121$ as a second concrete smoke test.
- [0015 — `CleanGN5Channel`](./0015-CleanGN5Channel.md) — An auditable `Prop` structure packaging a prime with local exponent one in `GN5` and exponent zero in the gap.
- [0016 — `CleanGN5Channel.dvd_body`](./0016-CleanGN5Channel.dvd_body.md) — The first consumer API lifting the local divisor of `GN5` to the full body $g\,GN5(g,y)$.
- [0017 — `CleanGN5Channel.not_sq_dvd_body`](./0017-CleanGN5Channel.not_sq_dvd_body.md) — The local exponent bound showing that the square of a clean prime coprime to the gap cannot enter the full body.
- [0018 — `not_fifth_power_GN5_of_clean`](./0018-not_fifth_power_GN5_of_clean.md) — Converts a clean prime of local exponent one in `GN5` into the first completed proof that `GN5(g,y)` is not a perfect fifth power.
- [0019 — `not_fifth_power_body_of_clean`](./0019-not_fifth_power_body_of_clean.md) — Lifts the clean prime's local exponent-one obstruction to exclusion of a perfect fifth power for the full body $g\,GN5(g,y)$.
- [0020 — `cleanGN5Channel_one_one_31`](./0020-cleanGN5Channel_one_one_31.md) — Constructs a concrete clean-channel certificate for the prime $31$ using $GN5(1,1)=31$.
- [0021 — `GN5_one_one_not_fifth_power`](./0021-GN5_one_one_not_fifth_power.md) — Connects the concrete provider to the general consumer in one line and excludes a perfect fifth power for $GN5(1,1)$.
- [0022 — `coprime_y_z_of_counterexamplePack`](./0022-coprime_y_z_of_counterexamplePack.md) — Uses primitivity and the fifth-power equation to derive $\gcd(y,z)=1$ in the first prime-divisor contradiction of the Reduction layer.
- [0023 — `coprime_gap_y_of_counterexamplePack`](./0023-coprime_gap_y_of_counterexamplePack.md) — Transfers $\gcd(y,z)=1$ across natural-number subtraction and establishes $\gcd(z-y,y)=1$ in local gap coordinates.
- [0024 — `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`](./0024-dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5.md) — Routes any common divisor of the gap and `GN5` through the gap decomposition into the exceptional term $5y^4$.
- [0025 — `coprime_gap_GN5_of_coprime_of_five_not_dvd`](./0025-coprime_gap_GN5_of_coprime_of_five_not_dvd.md) — Eliminates both possible sources of a common prime divisor under $\gcd(g,y)=1$ and $5\nmid g$, giving the Branch B factor-separation theorem.
- [0026 — `branchB_coprime_gap_GN5`](./0026-branchB_coprime_gap_GN5.md) — Connects `CounterexamplePack` and the Branch B condition to the general separation theorem, establishing $\gcd(z-y,GN5(z-y,y))=1$.
- [0027 — `fifth_power_factor_split`](./0027-fifth_power_factor_split.md) — Splits a coprime product that is a fifth power into two factors that are individually fifth powers.
- [0028 — `branchB_fifth_power_factor_split`](./0028-branchB_fifth_power_factor_split.md) — Splits the coprime Branch B fifth-power body and converts the gap and `GN5` into separate perfect fifth powers, yielding the exact elementary normal form.
- [0029 — `branchB_false_of_GN5_not_fifth_power`](./0029-branchB_false_of_GN5_not_fifth_power.md) — Collides the perfect-fifth-power conclusion forced for `GN5` in Branch B with an external non-fifth-power proof, returning `False` as the final consumer interface.

The next article will cover `DkMath.FLT.Five.coprime_GN5_y_of_coprime`.

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

The next article will cover `DkMath.FLT.Five.GN5_one_one`.

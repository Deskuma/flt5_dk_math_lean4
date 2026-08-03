# FLT5 Theorem Museum — English Translation

> This series is translated from the Japanese canonical edition.

## About this museum

This is a declaration-by-declaration reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five. It follows explanatory dependency order from the foundational interface toward the final contradiction.

The Japanese edition is canonical. The English edition preserves the content, declaration names, formulas, and section structure. The Lean source in the repository remains the final mathematical and formal authority.

## Numbering

Each article uses a matching four-digit dependency-order number and declaration name in both languages.

```text
0001-DeclarationName.md
0002-NextDeclaration.md
...
```

Each article records the Lean type, mathematical statement, role in the complete proof, direct dependencies, proof flow, Lean-specific processing, redundancy, optimization candidates, Mathlib imports, Comparator challenge suitability, and the next declaration. Verified source facts are distinguished from unverified proposals.

## Catalogue

- [0001 — `Fermat5Equation`](./0001-Fermat5Equation.md) — The minimal proposition-valued interface for the exponent-five equation.
- [0002 — `CounterexamplePack`](./0002-CounterexamplePack.md) — Packages positivity, primitivity, and the equation as input data.
- [0003 — `fifth_sub_eq_of_add_eq`](./0003-fifth_sub_eq_of_add_eq.md) — Converts the additive equation into a difference-of-fifth-powers identity over natural numbers.
- [0004 — `right_lt_of_fermat5Equation`](./0004-right_lt_of_fermat5Equation.md) — Derives $y<z$ from a positive left term and passes order information to gap positivity.
- [0005 — `gap_pos_of_fermat5Equation`](./0005-gap_pos_of_fermat5Equation.md) — Converts $y<z$ into $0<z-y$ and establishes a positive gap coordinate.

The next article will cover `DkMath.FLT.Five.GN5`.

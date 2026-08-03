# FLT5 Theorem Museum

A theorem-by-theorem reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five.

- [日本語正本](./ja/README.md)
- [English translation](./en/README.md)

## Purpose

This museum follows the formal proof from its smallest foundational declarations to the final contradiction. Each article isolates one definition, structure, lemma, or theorem and records both its mathematical role and its Lean-specific implementation.

The collection is intended to serve simultaneously as:

- a guided reading path through the FLT5 formalization;
- a dependency-aware theorem catalogue;
- an optimization and import-audit notebook;
- source material for small proof-comparison and Comparator challenges.

## Editorial policy

The Japanese edition is canonical. The English edition is a corresponding translation and uses the same article number and declaration name.

Articles are numbered with four digits in explanatory dependency order:

```text
0001-DeclarationName.md
0002-NextDeclaration.md
...
```

The numbering records the order in which the declarations are best understood as parts of the complete proof.

## Standard article contents

Each article records the Lean declaration, mathematical statement, role in the proof, direct dependencies, proof flow, Lean-specific processing, redundancy, optimization candidates, Mathlib imports, Comparator suitability, and the next declaration.

Claims taken directly from the repository are distinguished from interpretation, inference, and unverified optimization proposals.

## Source of truth

The Lean source in this repository is the primary source of truth. The existing Japanese and English explanatory PDFs provide narrative context, but they do not override the declarations checked by Lean's kernel.

## Catalogue

| No. | Declaration | 日本語 | English |
|---:|---|---|---|
| 0001 | `DkMath.FLT.Five.Fermat5Equation` | [日本語正本](./ja/0001-Fermat5Equation.md) | [English](./en/0001-Fermat5Equation.md) |
| 0002 | `DkMath.FLT.Five.CounterexamplePack` | [日本語正本](./ja/0002-CounterexamplePack.md) | [English](./en/0002-CounterexamplePack.md) |
| 0003 | `DkMath.FLT.Five.fifth_sub_eq_of_add_eq` | [日本語正本](./ja/0003-fifth_sub_eq_of_add_eq.md) | [English](./en/0003-fifth_sub_eq_of_add_eq.md) |
| 0004 | `DkMath.FLT.Five.right_lt_of_fermat5Equation` | [日本語正本](./ja/0004-right_lt_of_fermat5Equation.md) | [English](./en/0004-right_lt_of_fermat5Equation.md) |
| 0005 | `DkMath.FLT.Five.gap_pos_of_fermat5Equation` | [日本語正本](./ja/0005-gap_pos_of_fermat5Equation.md) | [English](./en/0005-gap_pos_of_fermat5Equation.md) |
| 0006 | `DkMath.FLT.Five.GN5` | [日本語正本](./ja/0006-GN5.md) | [English](./en/0006-GN5.md) |
| 0007 | `DkMath.FLT.Five.GN5_eq_homogeneous_cyclotomic` | [日本語正本](./ja/0007-GN5_eq_homogeneous_cyclotomic.md) | [English](./en/0007-GN5_eq_homogeneous_cyclotomic.md) |

Next in dependency order: `DkMath.FLT.Five.GN5_eq_gap_mul_add_five_mul_y_pow_four`.

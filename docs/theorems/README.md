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

The numbering does not merely reproduce textual order. It records the order in which the declarations are best understood as parts of the complete proof.

## Standard article contents

Each article records:

1. the Lean declaration and fully qualified name;
2. the mathematical statement;
3. its role in the complete FLT5 proof;
4. direct definitions and lemmas on which it depends;
5. the proof or construction flow;
6. Lean-specific transformations and tactics;
7. possible redundancy or duplication;
8. refactoring and optimization candidates;
9. Mathlib import requirements and import-minimization candidates;
10. suitability for a Comparator challenge;
11. the next declaration to study.

Claims taken directly from the repository are distinguished from interpretation, inference, and unverified optimization proposals.

## Source of truth

The Lean source in this repository is the primary source of truth. The existing Japanese and English explanatory PDFs provide narrative context, but they do not override the declarations checked by Lean's kernel.

## Catalogue

| No. | Declaration | 日本語 | English |
|---:|---|---|---|
| 0001 | `DkMath.FLT.Five.Fermat5Equation` | [日本語正本](./ja/0001-Fermat5Equation.md) | [English](./en/0001-Fermat5Equation.md) |
| 0002 | `DkMath.FLT.Five.CounterexamplePack` | [日本語正本](./ja/0002-CounterexamplePack.md) | [English](./en/0002-CounterexamplePack.md) |
| 0003 | `DkMath.FLT.Five.fifth_sub_eq_of_add_eq` | [日本語正本](./ja/0003-fifth_sub_eq_of_add_eq.md) | [English](./en/0003-fifth_sub_eq_of_add_eq.md) |

Next in dependency order: `DkMath.FLT.Five.right_lt_of_fermat5Equation`.

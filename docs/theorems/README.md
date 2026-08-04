# FLT5 Theorem Museum

A theorem-by-theorem reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five.

- [日本語正本](./ja/README.md)
- [English translation](./en/README.md)

## Purpose

This museum follows the formal proof from its smallest foundational declarations to the final theorem. Each article isolates one definition, structure, lemma, or theorem and records both its mathematical role and its Lean-specific implementation.

The collection serves as a guided reading path, dependency-aware catalogue, optimization and import-audit notebook, and source for small Comparator challenges.

## Editorial policy

The Japanese edition is canonical. The English edition is a corresponding translation using the same article number and declaration name. Articles use four-digit numbers in explanatory dependency order.

## Standard article contents

Each article records the Lean declaration, mathematical statement, role in the proof, direct dependencies, proof flow, Lean-specific processing, redundancy, optimization candidates, Mathlib imports, Comparator suitability, and the next declaration. Repository facts are distinguished from interpretation and unverified proposals.

## Source of truth

The Lean source is primary. Existing Japanese and English explanatory PDFs provide narrative context but do not override kernel-checked declarations.

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
| 0008 | `DkMath.FLT.Five.GN5_eq_gap_mul_add_five_mul_y_pow_four` | [日本語正本](./ja/0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) | [English](./en/0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) |
| 0009 | `DkMath.FLT.Five.GN5_eq_g_pow_four_add_five_mul` | [日本語正本](./ja/0009-GN5_eq_g_pow_four_add_five_mul.md) | [English](./en/0009-GN5_eq_g_pow_four_add_five_mul.md) |
| 0010 | `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5` | [日本語正本](./ja/0010-add_pow_five_eq_add_mul_GN5.md) | [English](./en/0010-add_pow_five_eq_add_mul_GN5.md) |
| 0011 | `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5` | [日本語正本](./ja/0011-add_pow_five_sub_eq_mul_GN5.md) | [English](./en/0011-add_pow_five_sub_eq_mul_GN5.md) |
| 0012 | `DkMath.FLT.Five.pow_five_sub_pow_five_eq_gap_mul_GN5` | [日本語正本](./ja/0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) | [English](./en/0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) |
| 0013 | `DkMath.FLT.Five.GN5_one_one` | [日本語正本](./ja/0013-GN5_one_one.md) | [English](./en/0013-GN5_one_one.md) |
| 0014 | `DkMath.FLT.Five.GN5_two_one` | [日本語正本](./ja/0014-GN5_two_one.md) | [English](./en/0014-GN5_two_one.md) |
| 0015 | `DkMath.FLT.Five.CleanGN5Channel` | [日本語正本](./ja/0015-CleanGN5Channel.md) | [English](./en/0015-CleanGN5Channel.md) |
| 0016 | `DkMath.FLT.Five.CleanGN5Channel.dvd_body` | [日本語正本](./ja/0016-CleanGN5Channel.dvd_body.md) | [English](./en/0016-CleanGN5Channel.dvd_body.md) |
| 0017 | `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body` | [日本語正本](./ja/0017-CleanGN5Channel.not_sq_dvd_body.md) | [English](./en/0017-CleanGN5Channel.not_sq_dvd_body.md) |
| 0018 | `DkMath.FLT.Five.not_fifth_power_GN5_of_clean` | [日本語正本](./ja/0018-not_fifth_power_GN5_of_clean.md) | [English](./en/0018-not_fifth_power_GN5_of_clean.md) |

Next in dependency order: `DkMath.FLT.Five.not_fifth_power_body_of_clean`.

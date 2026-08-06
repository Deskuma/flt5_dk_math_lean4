# FLT5 Theorem Museum

A theorem-by-theorem reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five.

- [日本語正本](./ja/README.md)
- [English translation](./en/README.md)

## Purpose

This museum follows the formal proof from its smallest foundational declarations to the final theorem. Each article isolates one definition, structure, lemma, or theorem and records both its mathematical role and Lean-specific implementation.

The Japanese edition is canonical. The English edition preserves the same article number, declaration name, formulas, and section structure. Four-digit article numbers follow explanatory dependency order. The Lean source is primary; existing Japanese and English PDFs provide narrative context but do not override kernel-checked declarations.

## Catalogue

| No. | Declaration | 日本語 | English |
|---:|---|---|---|
| 0001 | `Fermat5Equation` | [日本語](./ja/0001-Fermat5Equation.md) | [English](./en/0001-Fermat5Equation.md) |
| 0002 | `CounterexamplePack` | [日本語](./ja/0002-CounterexamplePack.md) | [English](./en/0002-CounterexamplePack.md) |
| 0003 | `fifth_sub_eq_of_add_eq` | [日本語](./ja/0003-fifth_sub_eq_of_add_eq.md) | [English](./en/0003-fifth_sub_eq_of_add_eq.md) |
| 0004 | `right_lt_of_fermat5Equation` | [日本語](./ja/0004-right_lt_of_fermat5Equation.md) | [English](./en/0004-right_lt_of_fermat5Equation.md) |
| 0005 | `gap_pos_of_fermat5Equation` | [日本語](./ja/0005-gap_pos_of_fermat5Equation.md) | [English](./en/0005-gap_pos_of_fermat5Equation.md) |
| 0006 | `GN5` | [日本語](./ja/0006-GN5.md) | [English](./en/0006-GN5.md) |
| 0007 | `GN5_eq_homogeneous_cyclotomic` | [日本語](./ja/0007-GN5_eq_homogeneous_cyclotomic.md) | [English](./en/0007-GN5_eq_homogeneous_cyclotomic.md) |
| 0008 | `GN5_eq_gap_mul_add_five_mul_y_pow_four` | [日本語](./ja/0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) | [English](./en/0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) |
| 0009 | `GN5_eq_g_pow_four_add_five_mul` | [日本語](./ja/0009-GN5_eq_g_pow_four_add_five_mul.md) | [English](./en/0009-GN5_eq_g_pow_four_add_five_mul.md) |
| 0010 | `add_pow_five_eq_add_mul_GN5` | [日本語](./ja/0010-add_pow_five_eq_add_mul_GN5.md) | [English](./en/0010-add_pow_five_eq_add_mul_GN5.md) |
| 0011 | `add_pow_five_sub_eq_mul_GN5` | [日本語](./ja/0011-add_pow_five_sub_eq_mul_GN5.md) | [English](./en/0011-add_pow_five_sub_eq_mul_GN5.md) |
| 0012 | `pow_five_sub_pow_five_eq_gap_mul_GN5` | [日本語](./ja/0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) | [English](./en/0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) |
| 0013 | `GN5_one_one` | [日本語](./ja/0013-GN5_one_one.md) | [English](./en/0013-GN5_one_one.md) |
| 0014 | `GN5_two_one` | [日本語](./ja/0014-GN5_two_one.md) | [English](./en/0014-GN5_two_one.md) |
| 0015 | `CleanGN5Channel` | [日本語](./ja/0015-CleanGN5Channel.md) | [English](./en/0015-CleanGN5Channel.md) |
| 0016 | `CleanGN5Channel.dvd_body` | [日本語](./ja/0016-CleanGN5Channel.dvd_body.md) | [English](./en/0016-CleanGN5Channel.dvd_body.md) |
| 0017 | `CleanGN5Channel.not_sq_dvd_body` | [日本語](./ja/0017-CleanGN5Channel.not_sq_dvd_body.md) | [English](./en/0017-CleanGN5Channel.not_sq_dvd_body.md) |
| 0018 | `not_fifth_power_GN5_of_clean` | [日本語](./ja/0018-not_fifth_power_GN5_of_clean.md) | [English](./en/0018-not_fifth_power_GN5_of_clean.md) |
| 0019 | `not_fifth_power_body_of_clean` | [日本語](./ja/0019-not_fifth_power_body_of_clean.md) | [English](./en/0019-not_fifth_power_body_of_clean.md) |
| 0020 | `cleanGN5Channel_one_one_31` | [日本語](./ja/0020-cleanGN5Channel_one_one_31.md) | [English](./en/0020-cleanGN5Channel_one_one_31.md) |
| 0021 | `GN5_one_one_not_fifth_power` | [日本語](./ja/0021-GN5_one_one_not_fifth_power.md) | [English](./en/0021-GN5_one_one_not_fifth_power.md) |
| 0022 | `coprime_y_z_of_counterexamplePack` | [日本語](./ja/0022-coprime_y_z_of_counterexamplePack.md) | [English](./en/0022-coprime_y_z_of_counterexamplePack.md) |
| 0023 | `coprime_gap_y_of_counterexamplePack` | [日本語](./ja/0023-coprime_gap_y_of_counterexamplePack.md) | [English](./en/0023-coprime_gap_y_of_counterexamplePack.md) |
| 0024 | `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5` | [日本語](./ja/0024-dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5.md) | [English](./en/0024-dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5.md) |
| 0025 | `coprime_gap_GN5_of_coprime_of_five_not_dvd` | [日本語](./ja/0025-coprime_gap_GN5_of_coprime_of_five_not_dvd.md) | [English](./en/0025-coprime_gap_GN5_of_coprime_of_five_not_dvd.md) |
| 0026 | `branchB_coprime_gap_GN5` | [日本語](./ja/0026-branchB_coprime_gap_GN5.md) | [English](./en/0026-branchB_coprime_gap_GN5.md) |
| 0027 | `fifth_power_factor_split` | [日本語](./ja/0027-fifth_power_factor_split.md) | [English](./en/0027-fifth_power_factor_split.md) |
| 0028 | `branchB_fifth_power_factor_split` | [日本語](./ja/0028-branchB_fifth_power_factor_split.md) | [English](./en/0028-branchB_fifth_power_factor_split.md) |
| 0029 | `branchB_false_of_GN5_not_fifth_power` | [日本語](./ja/0029-branchB_false_of_GN5_not_fifth_power.md) | [English](./en/0029-branchB_false_of_GN5_not_fifth_power.md) |
| 0030 | `coprime_GN5_y_of_coprime` | [日本語](./ja/0030-coprime_GN5_y_of_coprime.md) | [English](./en/0030-coprime_GN5_y_of_coprime.md) |
| 0031 | `BranchBFifthPowerNormalForm` | [日本語](./ja/0031-BranchBFifthPowerNormalForm.md) | [English](./en/0031-BranchBFifthPowerNormalForm.md) |
| 0032 | `exists_branchB_fifthPowerNormalForm` | [日本語](./ja/0032-exists_branchB_fifthPowerNormalForm.md) | [English](./en/0032-exists_branchB_fifthPowerNormalForm.md) |
| 0033 | `BranchBFifthPowerCore` | [日本語](./ja/0033-BranchBFifthPowerCore.md) | [English](./en/0033-BranchBFifthPowerCore.md) |
| 0034 | `branchB_false_of_fifthPowerCore` | [日本語](./ja/0034-branchB_false_of_fifthPowerCore.md) | [English](./en/0034-branchB_false_of_fifthPowerCore.md) |
| 0035 | `Body5` | [日本語](./ja/0035-Body5.md) | [English](./en/0035-Body5.md) |
| 0036 | `body5_eq_add_pow_sub` | [日本語](./ja/0036-body5_eq_add_pow_sub.md) | [English](./en/0036-body5_eq_add_pow_sub.md) |
| 0037 | `body5_eq_fifth_power_of_fermat` | [日本語](./ja/0037-body5_eq_fifth_power_of_fermat.md) | [English](./en/0037-body5_eq_fifth_power_of_fermat.md) |
| 0038 | `counterexample_false_of_clean_GN5Channel_by_dvd` | [日本語](./ja/0038-counterexample_false_of_clean_GN5Channel_by_dvd.md) | [English](./en/0038-counterexample_false_of_clean_GN5Channel_by_dvd.md) |
| 0039 | `BranchBCleanGN5ChannelProvider` | [日本語](./ja/0039-BranchBCleanGN5ChannelProvider.md) | [English](./en/0039-BranchBCleanGN5ChannelProvider.md) |
| 0040 | `BranchBNoLiftEscape` | [日本語](./ja/0040-BranchBNoLiftEscape.md) | [English](./en/0040-BranchBNoLiftEscape.md) |
| 0041 | `branchBCleanGN5ChannelProvider_of_noLiftEscape` | [日本語](./ja/0041-branchBCleanGN5ChannelProvider_of_noLiftEscape.md) | [English](./en/0041-branchBCleanGN5ChannelProvider_of_noLiftEscape.md) |
| 0042 | `branchB_false_of_clean_provider_by_dvd` | [日本語](./ja/0042-branchB_false_of_clean_provider_by_dvd.md) | [English](./en/0042-branchB_false_of_clean_provider_by_dvd.md) |
| 0043 | `branchB_false_of_noLiftEscape_by_dvd` | [日本語](./ja/0043-branchB_false_of_noLiftEscape_by_dvd.md) | [English](./en/0043-branchB_false_of_noLiftEscape_by_dvd.md) |

Next in dependency order: `DkMath.FLT.Five.BranchACondition`.

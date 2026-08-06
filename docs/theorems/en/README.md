# FLT5 Theorem Museum — English Translation

> This series is translated from the Japanese canonical edition.

## About this museum

This is a declaration-by-declaration reading guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five. It follows explanatory dependency order from the foundational interface toward the final theorem. The Japanese edition is canonical. The English edition preserves the content, declaration names, formulas, and section structure. Matching four-digit numbers are used in both languages. Each article records the Lean type, mathematical statement, role in the proof, direct dependencies, proof flow, Lean-specific processing, redundancy, optimization candidates, Mathlib imports, Comparator challenge suitability, and the next declaration. The Lean source is the final authority.

## Catalogue

- [0001 — `Fermat5Equation`](./0001-Fermat5Equation.md)
- [0002 — `CounterexamplePack`](./0002-CounterexamplePack.md)
- [0003 — `fifth_sub_eq_of_add_eq`](./0003-fifth_sub_eq_of_add_eq.md)
- [0004 — `right_lt_of_fermat5Equation`](./0004-right_lt_of_fermat5Equation.md)
- [0005 — `gap_pos_of_fermat5Equation`](./0005-gap_pos_of_fermat5Equation.md)
- [0006 — `GN5`](./0006-GN5.md)
- [0007 — `GN5_eq_homogeneous_cyclotomic`](./0007-GN5_eq_homogeneous_cyclotomic.md)
- [0008 — `GN5_eq_gap_mul_add_five_mul_y_pow_four`](./0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md)
- [0009 — `GN5_eq_g_pow_four_add_five_mul`](./0009-GN5_eq_g_pow_four_add_five_mul.md)
- [0010 — `add_pow_five_eq_add_mul_GN5`](./0010-add_pow_five_eq_add_mul_GN5.md)
- [0011 — `add_pow_five_sub_eq_mul_GN5`](./0011-add_pow_five_sub_eq_mul_GN5.md)
- [0012 — `pow_five_sub_pow_five_eq_gap_mul_GN5`](./0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md)
- [0013 — `GN5_one_one`](./0013-GN5_one_one.md)
- [0014 — `GN5_two_one`](./0014-GN5_two_one.md)
- [0015 — `CleanGN5Channel`](./0015-CleanGN5Channel.md)
- [0016 — `CleanGN5Channel.dvd_body`](./0016-CleanGN5Channel.dvd_body.md)
- [0017 — `CleanGN5Channel.not_sq_dvd_body`](./0017-CleanGN5Channel.not_sq_dvd_body.md)
- [0018 — `not_fifth_power_GN5_of_clean`](./0018-not_fifth_power_GN5_of_clean.md)
- [0019 — `not_fifth_power_body_of_clean`](./0019-not_fifth_power_body_of_clean.md)
- [0020 — `cleanGN5Channel_one_one_31`](./0020-cleanGN5Channel_one_one_31.md)
- [0021 — `GN5_one_one_not_fifth_power`](./0021-GN5_one_one_not_fifth_power.md)
- [0022 — `coprime_y_z_of_counterexamplePack`](./0022-coprime_y_z_of_counterexamplePack.md)
- [0023 — `coprime_gap_y_of_counterexamplePack`](./0023-coprime_gap_y_of_counterexamplePack.md)
- [0024 — `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`](./0024-dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5.md)
- [0025 — `coprime_gap_GN5_of_coprime_of_five_not_dvd`](./0025-coprime_gap_GN5_of_coprime_of_five_not_dvd.md)
- [0026 — `branchB_coprime_gap_GN5`](./0026-branchB_coprime_gap_GN5.md)
- [0027 — `fifth_power_factor_split`](./0027-fifth_power_factor_split.md)
- [0028 — `branchB_fifth_power_factor_split`](./0028-branchB_fifth_power_factor_split.md)
- [0029 — `branchB_false_of_GN5_not_fifth_power`](./0029-branchB_false_of_GN5_not_fifth_power.md)
- [0030 — `coprime_GN5_y_of_coprime`](./0030-coprime_GN5_y_of_coprime.md)
- [0031 — `BranchBFifthPowerNormalForm`](./0031-BranchBFifthPowerNormalForm.md)
- [0032 — `exists_branchB_fifthPowerNormalForm`](./0032-exists_branchB_fifthPowerNormalForm.md)
- [0033 — `BranchBFifthPowerCore`](./0033-BranchBFifthPowerCore.md)
- [0034 — `branchB_false_of_fifthPowerCore`](./0034-branchB_false_of_fifthPowerCore.md) — Projects only the five facts required by the core from the complete normal form and refutes Branch B.
- [0035 — `Body5`](./0035-Body5.md) — Names the product of the gap and `GN5` as the body of the complete fifth-power difference.
- [0036 — `body5_eq_add_pow_sub`](./0036-body5_eq_add_pow_sub.md) — Connects `Body5` to the general fifth-power difference `(g+y)^5-y^5`.
- [0037 — `body5_eq_fifth_power_of_fermat`](./0037-body5_eq_fifth_power_of_fermat.md) — Connects the gap-coordinate `Body5` to the perfect fifth power `x^5` forced by the Fermat equation.
- [0038 — `counterexample_false_of_clean_GN5Channel_by_dvd`](./0038-counterexample_false_of_clean_GN5Channel_by_dvd.md) — Contradicts the perfect-fifth-power body forced by the Fermat equation with the clean channel's non-fifth-power obstruction.
- [0039 — `BranchBCleanGN5ChannelProvider`](./0039-BranchBCleanGN5ChannelProvider.md) — Conditional provider interface supplying an existential clean channel to every Branch B counterexample candidate.
- [0040 — `BranchBNoLiftEscape`](./0040-BranchBNoLiftEscape.md) — Unbundled no-lift kernel returning primality and three divisibility conditions for a clean channel.
- [0041 — `branchBCleanGN5ChannelProvider_of_noLiftEscape`](./0041-branchBCleanGN5ChannelProvider_of_noLiftEscape.md) — Adapter repackaging the unbundled no-lift kernel as a bundled clean-channel provider.
- [0042 — `branchB_false_of_clean_provider_by_dvd`](./0042-branchB_false_of_clean_provider_by_dvd.md) — Consumer extracting a clean-channel witness from the bundled provider and passing it to the local refuter to close Branch B.
- [0043 — `branchB_false_of_noLiftEscape_by_dvd`](./0043-branchB_false_of_noLiftEscape_by_dvd.md) — Façade theorem sending the unbundled no-lift kernel directly to the Branch B contradiction by composing the adapter and bundled consumer.
- [0044 — `BranchACondition`](./0044-BranchACondition.md) — Branch predicate naming the exceptional case where the gap `z-y` is divisible by five and routing it toward the signed five-adic and golden-descent layers.

The next article will cover `DkMath.FLT.Five.BranchARefuter`.

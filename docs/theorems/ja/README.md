# FLT5 定理博物館 — 日本語正本

> 本文書群は日本語正本です。英語版は本正本からの対応翻訳として刊行します。

## この博物館について

Lean 4 による指数5の場合のフェルマーの最終定理の形式化を、入口から依存順に一宣言ずつ読む定理解説集です。日本語版を正本とし、英語版は内容・宣言名・数式・節構成を保った対応翻訳とします。各記事は依存順の4桁番号を共有し、Lean の型、数学的主張、証明全体での役割、直接依存、証明の流れ、Lean 固有処理、冗長性、最適化候補、Mathlib import、Comparator challenge 化、次に読む宣言を収録します。数学的・形式的な最終根拠はリポジトリ内の Lean ソースです。

## 目録

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
- [0034 — `branchB_false_of_fifthPowerCore`](./0034-branchB_false_of_fifthPowerCore.md) — 完全標準形から core に必要な五項だけを射影し、Branch B を反証する adapter。
- [0035 — `Body5`](./0035-Body5.md) — gap と `GN5` の積を第五冪差全体の body として命名する定義。
- [0036 — `body5_eq_add_pow_sub`](./0036-body5_eq_add_pow_sub.md) — `Body5` を一般の第五冪差 `(g+y)^5-y^5` へ接続する bridge。
- [0037 — `body5_eq_fifth_power_of_fermat`](./0037-body5_eq_fifth_power_of_fermat.md) — gap 座標の `Body5` を Fermat 方程式が強制する完全第五冪 `x^5` へ接続する bridge。
- [0038 — `counterexample_false_of_clean_GN5Channel_by_dvd`](./0038-counterexample_false_of_clean_GN5Channel_by_dvd.md) — Fermat 方程式が与える完全第五冪 body と clean channel の非第五冪性を衝突させる局所 refuter。
- [0039 — `BranchBCleanGN5ChannelProvider`](./0039-BranchBCleanGN5ChannelProvider.md) — 任意の Branch B 反例候補へ existential clean channel を供給する条件付き provider interface。
- [0040 — `BranchBNoLiftEscape`](./0040-BranchBNoLiftEscape.md) — clean channel の素数性と三つの整除条件を連言で返す unbundled no-lift kernel。
- [0041 — `branchBCleanGN5ChannelProvider_of_noLiftEscape`](./0041-branchBCleanGN5ChannelProvider_of_noLiftEscape.md) — unbundled no-lift kernel を bundled clean-channel provider へ再梱包する adapter。
- [0042 — `branchB_false_of_clean_provider_by_dvd`](./0042-branchB_false_of_clean_provider_by_dvd.md) — bundled provider から clean channel の存在証人を取り出し、局所 refuter へ渡して Branch B を閉じる consumer。
- [0043 — `branchB_false_of_noLiftEscape_by_dvd`](./0043-branchB_false_of_noLiftEscape_by_dvd.md) — unbundled no-lift kernel を adapter と bundled consumer の合成により Branch B の矛盾へ直接送る façade theorem。

次号は `DkMath.FLT.Five.BranchACondition` を扱います。

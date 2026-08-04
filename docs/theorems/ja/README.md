# FLT5 定理博物館 — 日本語正本

> 本文書群は日本語正本です。英語版は本正本からの対応翻訳として刊行します。

## この博物館について

Lean 4 による指数5の場合のフェルマーの最終定理の形式化を、入口から依存順に一宣言ずつ読む定理解説集です。定義・構造体・補題・定理を個別の展示物として分離し、それぞれが受け取る事実と次へ渡す事実を記録します。

日本語版を正本とし、英語版は内容・宣言名・数式・節構成を保った対応翻訳とします。数学的・形式的な最終根拠はリポジトリ内の Lean ソースです。

## 番号規則

各記事は依存順の4桁番号と宣言名を共有します。

各号には Lean の型、数学的主張、証明全体での役割、直接依存、証明の流れ、Lean 固有処理、冗長性、最適化候補、Mathlib import、Comparator challenge 化、次に読む宣言を収録します。確認事実と未検証の提案は区別して記します。

## 目録

- [0001 — `Fermat5Equation`](./0001-Fermat5Equation.md) — 指数5方程式の最小命題インターフェース。
- [0002 — `CounterexamplePack`](./0002-CounterexamplePack.md) — 正値性・原始性・方程式を束ねる入力構造体。
- [0003 — `fifth_sub_eq_of_add_eq`](./0003-fifth_sub_eq_of_add_eq.md) — 加法形を自然数上の第五冪差分形へ移す補題。
- [0004 — `right_lt_of_fermat5Equation`](./0004-right_lt_of_fermat5Equation.md) — 正の左項から $y<z$ を導き、gap の正値化へ渡す順序橋。
- [0005 — `gap_pos_of_fermat5Equation`](./0005-gap_pos_of_fermat5Equation.md) — $y<z$ を $0<z-y$ へ変換し、正の gap 座標を確立する橋。
- [0006 — `GN5`](./0006-GN5.md) — 第五冪差から gap を取り出した次数4の斉次残余核。
- [0007 — `GN5_eq_homogeneous_cyclotomic`](./0007-GN5_eq_homogeneous_cyclotomic.md) — `GN5` を標準的な斉次第五巡回因子と同一視する多項式恒等式。
- [0008 — `GN5_eq_gap_mul_add_five_mul_y_pow_four`](./0008-GN5_eq_gap_mul_add_five_mul_y_pow_four.md) — `GN5` を gap の倍数部分と $5y^4$ に分ける合同解析用の恒等式。
- [0009 — `GN5_eq_g_pow_four_add_five_mul`](./0009-GN5_eq_g_pow_four_add_five_mul.md) — `GN5` を $g^4$ と $5$ の倍数部分に分ける five-adic 分解。
- [0010 — `add_pow_five_eq_add_mul_GN5`](./0010-add_pow_five_eq_add_mul_GN5.md) — 第五冪を基準項 $y^5$ と gap を因子にもつ `GN5` body に分解する加法形。
- [0011 — `add_pow_five_sub_eq_mul_GN5`](./0011-add_pow_five_sub_eq_mul_GN5.md) — 加法形を第五冪差と gap・`GN5` の積を結ぶ直接因数分解 API へ変換する補題。
- [0012 — `pow_five_sub_pow_five_eq_gap_mul_GN5`](./0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) — 抽象 gap を実際の自然数差 $z-y$ へ接続する第五冪差の因数分解橋。
- [0013 — `GN5_one_one`](./0013-GN5_one_one.md) — $GN5(1,1)=31$ を確定し、有限素数 escape の no-lift 実演へ渡す具体値評価。
- [0014 — `GN5_two_one`](./0014-GN5_two_one.md) — $GN5(2,1)=121$ を確定する第二の具体値 smoke test。
- [0015 — `CleanGN5Channel`](./0015-CleanGN5Channel.md) — gap 外で `GN5` に局所指数1をもつ素数を束ねる監査可能な `Prop` 構造体。
- [0016 — `CleanGN5Channel.dvd_body`](./0016-CleanGN5Channel.dvd_body.md) — `GN5` の局所素因子を full body $g\,GN5(g,y)$ へ持ち上げる最初の消費 API。
- [0017 — `CleanGN5Channel.not_sq_dvd_body`](./0017-CleanGN5Channel.not_sq_dvd_body.md) — gap と互いに素な clean prime の平方が full body に混入しないことを示す局所指数上限。
- [0018 — `not_fifth_power_GN5_of_clean`](./0018-not_fifth_power_GN5_of_clean.md) — `GN5` に局所指数1をもつ clean prime から、`GN5(g,y)` が完全第五冪でないことを導く最初の完成形。
- [0019 — `not_fifth_power_body_of_clean`](./0019-not_fifth_power_body_of_clean.md) — clean prime の局所指数1を full body $g\,GN5(g,y)$ の完全第五冪排除へ持ち上げる主要消費定理。
- [0020 — `cleanGN5Channel_one_one_31`](./0020-cleanGN5Channel_one_one_31.md) — $GN5(1,1)=31$ を使い、素数 $31$ の具体的な clean-channel 証明書を構成する provider。
- [0021 — `GN5_one_one_not_fifth_power`](./0021-GN5_one_one_not_fifth_power.md) — 具体 provider と一般 consumer を一行で接続し、$GN5(1,1)$ の完全第五冪性を排除する完成デモ。
- [0022 — `coprime_y_z_of_counterexamplePack`](./0022-coprime_y_z_of_counterexamplePack.md) — 原始性と第五冪方程式から $\gcd(y,z)=1$ を導く Reduction 層の最初の素因子反証。

次号は `DkMath.FLT.Five.coprime_gap_y_of_counterexamplePack` を扱います。

# 0013 — `GN5_one_one`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem GN5_one_one : GN5 1 1 = 31 := by
  norm_num [GN5]
```

完全修飾名は `DkMath.FLT.Five.GN5_one_one` です。

## 数学的主張

`GN5` を gap $g=1$、基準座標 $y=1$ で評価すると $31$ になります。

$$
GN5(1,1)=1^4+5\cdot1^3\cdot1+10\cdot1^2\cdot1^2+10\cdot1\cdot1^3+5\cdot1^4=31
$$

これは同じ値を標準巡回因子表示から

$$
GN5(1,1)=2^4+2^3+2^2+2+1=31
$$

と読むことにも対応します。

## 証明全体での役割

本定理は一般的な第五巡回因子を、有限素数 escape の具体例へ落とす評価補題です。後続の `cleanGN5Channel_one_one_31` では、$31$ が素数で `GN5 1 1` を割り、その平方 $31^2$ は割らないことを具体的に検査します。その結果、`GN5 1 1` が第五冪ではないことを示す小さな実演へ接続されます。

この補題自体は FLT5 の一般証明を担う主要縮約ではなく、局所 no-lift 機構を監査可能な有限計算で示す smoke test 兼デモです。

## 直接依存する定義・補題

- `DkMath.FLT.Five.GN5`
- `norm_num` tactic

数学的には `GN5_eq_homogeneous_cyclotomic` からも計算できますが、現行証明はその定理へ直接依存せず、定義を展開して評価します。

## 証明の流れ

1. `norm_num [GN5]` が `GN5` の定義を展開する。
2. $g=y=1$ を各単項式へ代入する。
3. 自然数の冪・乗法・加法を正規化する。
4. 両辺が $31$ で一致することを閉じる。

`ring`、`omega`、素数判定、整除性推論は使用しません。

## Lean 固有の処理

`norm_num [GN5]` の角括弧内は、数値正規化の前に展開してよい定義を指定しています。`rfl` だけでは、`GN5` の展開後に残る冪・乗法・加法の計算が期待する形まで自動で正規化されるとは限らないため、数値命題専用の `norm_num` が明確です。

本定理は閉じた命題で変数や仮定を持たず、カーネルが確認する証明項は具体的な自然数等式だけです。

## 冗長・重複箇所

値 $31$ は後続の `cleanGN5Channel_one_one_31` 内でも `norm_num [GN5]` によって再計算されます。そのため計算の重複はあります。

一方、本定理を独立 API として残すことで、値の意味を命名し、記事・テスト・後続証明から再利用できます。後続がこの補題を利用していない点は最適化候補です。

## 最適化候補

`cleanGN5Channel_one_one_31` の `dvd_GN5` と `noLift` の証明で `GN5_one_one` を `rw` または `simp` に使い、同じ多項式評価を繰り返さない構成が考えられます。ただし現行の閉じた `norm_num [GN5]` も局所的で堅牢です。

別案として `GN5_eq_homogeneous_cyclotomic 1 1` を経由できますが、単純な数値評価に一般恒等式への依存を追加するため、短縮や保守性の改善になるとは限りません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理に直接必要なのは自然数、冪・加減乗算、および `norm_num` tactic です。候補として `Mathlib.Tactic.NormNum` と基礎的な自然数代数 import まで絞れる可能性がありますが、正確な最小 import は Lean ビルドを行っていないため未確定です。

## Comparator challenge 化の可否

適しています。小さく、結果が明確で、証明方式の差を比較しやすい課題です。

1. 現行の `norm_num [GN5]`。
2. `unfold GN5; norm_num`。
3. `GN5_eq_homogeneous_cyclotomic` で書き換えてから `norm_num`。
4. `decide` または `native_decide` が適用可能かを検証する方式。

比較軸は証明項の透明性、一般補題の再利用、実行性能、必要 import、定義変更への耐性です。`native_decide` の採用可否と信頼境界は実ビルドで検証すべき提案です。

## 次に読むべき定理

次は `DkMath.FLT.Five.GN5_two_one` です。

$$
GN5(2,1)=121
$$

同じ核の第二の小評価であり、定義と数値正規化の smoke test を補強します。その後、`CleanGN5Channel` 構造と有限素数 $31$ の no-lift 実演へ進みます。

## 根拠と推論の区別

型、証明、宣言順、値 $31$、および後続宣言は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GN5.lean` と `CleanChannel.lean` の生成ソースで確認した事実です。証明全体での位置づけ、重複評価の整理、import 最小化、Comparator 案は解説上の分析または未検証の提案を含みます。既存 PDF の物語的説明より Lean ソースを形式的根拠として優先し、本号では PDF に固有の追加主張を行っていません。Lean ビルドは行っていません。

---

[prev](./0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md) < 0013 > [next](./0014-GN5_two_one.md)

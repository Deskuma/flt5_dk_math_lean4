# 0021 — `GN5_one_one_not_fifth_power`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem GN5_one_one_not_fifth_power :
    ¬ ∃ x : ℕ, GN5 1 1 = x ^ 5 := by
  exact not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

完全修飾名は `DkMath.FLT.Five.GN5_one_one_not_fifth_power` です。

## 数学的主張

この定理は、具体値 `GN5 1 1` が自然数の完全第五冪ではないことを主張します。

$$
¬\exists x\in\mathbb{N},\ GN5(1,1)=x^5
$$

既出の評価 $GN5(1,1)=31$ を代入すれば、これは $31$ が自然数の第五冪ではないという命題です。ただし現行証明は `GN5_one_one` を直接展開して数値比較するのではなく、素数 $31$ が `GN5(1,1)` に局所指数ちょうど $1$ で現れるという clean-channel 証明書を一般定理へ渡します。

## 証明全体での役割

本定理は、抽象 consumer

```lean
not_fifth_power_GN5_of_clean
```

と具体 provider

```lean
cleanGN5Channel_one_one_31
```

を一行で接続する最初の完成デモです。これにより、局所 no-lift obstruction の API が実際の具体入力で作動することを確認します。

一般の FLT5 反例排除を直接進める主要ルートではなく、有限素数 escape の executable example です。しかし provider と consumer を分離した設計、局所指数 $1$ と第五冪指数の衝突、証明再利用の形を最小例で示す重要な検査点です。

## 直接依存する定義・補題

- `DkMath.FLT.Five.GN5`
- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.cleanGN5Channel_one_one_31`
- `DkMath.FLT.Five.not_fifth_power_GN5_of_clean`

数学的には `GN5_one_one : GN5 1 1 = 31` も背景にありますが、本定理の proof term はそれを直接参照しません。具体値計算は provider 側へ封じ込められています。

## 証明の流れ

1. `cleanGN5Channel_one_one_31` により、$g=1$、$y=1$、$q=31$ の clean-channel 証明書を得る。
2. その証明書を一般定理 `not_fifth_power_GN5_of_clean` へ渡す。
3. 一般定理が、$31$ の局所指数 $1$ と完全第五冪に必要な指数の倍数性を衝突させる。
4. 結果として `¬ ∃ x : ℕ, GN5 1 1 = x ^ 5` を得る。

本定理自身は矛盾の内部計算を繰り返さず、既証明の API を合成するだけです。

## Lean 固有の処理

```lean
exact not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

では、Lean が暗黙引数 `{g y q : ℕ}` を目標型と provider の型から推論します。具体的には `cleanGN5Channel_one_one_31 : CleanGN5Channel 1 1 31` により、一般定理の `g=1`、`y=1`、`q=31` が決まります。

`tactic` による算術処理、`rw`、`simp`、`norm_num`、`ring` は本定理には現れません。計算と局所整除性は依存定理へ完全に委譲されています。この薄さは、証明の意味的な境界が良好に設計されていることを示します。

## 冗長・重複箇所

証明本文に実質的な重複はありません。`not_fifth_power_GN5_of_clean` の一般論と `cleanGN5Channel_one_one_31` の具体計算を再利用しています。

ただし同じ数学的結論は、`GN5_one_one` で $GN5(1,1)=31$ に書き換えた後、閉じた数値命題として直接処理することも可能と思われます。その直接証明は短くなる可能性がありますが、clean-channel API の統合試験という本定理の役割を失います。

## 最適化候補

1. 現行の一行証明を維持する。API 境界と再利用性の点で既に最小に近い形です。
2. `exact` を省略した term proof

```lean
theorem GN5_one_one_not_fifth_power :
    ¬ ∃ x : ℕ, GN5 1 1 = x ^ 5 :=
  not_fifth_power_GN5_of_clean cleanGN5Channel_one_one_31
```

と比較する。
3. `simpa` を用いる形を試す余地はありますが、現行では型が直接一致するため不要です。
4. `GN5_one_one` と `norm_num` による直接数値証明と比較し、proof term、依存関係、エラー局所性、API 回帰検査としての価値を測る。
5. smoke-test 宣言として `example` にする案もありますが、公開 theorem として保持すれば後続利用と文書参照が容易です。

以上の変更案は未検証です。Lean ビルドは行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理そのものは既存定理の適用だけであり、直接 tactic や数値計算機能を必要としません。

必要な環境は実質的に次の宣言が利用可能であることです。

- `GN5`
- `CleanGN5Channel`
- `cleanGN5Channel_one_one_31`
- `not_fifth_power_GN5_of_clean`

したがって本定理単独の追加 import は不要で、`CleanChannel.lean` 内の先行宣言があれば十分です。ただしファイル全体では `Nat.Prime`、整除性、互いに素性、`norm_num`、`ring` などを使うため、ファイル単位の最小 import は別途監査が必要です。import 最小化は未検証です。

## Comparator challenge 化の可否

非常に小さな API 合成 challenge として適しています。

比較候補は次の通りです。

- 現行の provider-consumer 合成。
- term proof と tactic proof の比較。
- `GN5_one_one` を使った直接数値証明。
- `simpa using` による型推論の明示度比較。
- provider を局所 `have` で構築する自己完結証明。

比較軸は行数だけでなく、抽象化境界、依存の透明性、再計算の有無、一般 API の回帰試験として機能するか、エラー時に原因を provider と consumer のどちらへ局所化できるかです。

## 次に読むべき定理

次は `DkMath.FLT.Five.coprime_y_z_of_counterexamplePack` です。

これは `CleanChannel.lean` の有限例を終え、`Reduction.lean` の一般 FLT5 縮約へ進む最初の定理です。反例候補の原始性と方程式から、

$$
\gcd(y,z)=1
$$

を導き、gap と座標の互いに素性、さらに gap と `GN5` の因子分離へ進む基礎を作ります。

## 根拠と推論の区別

定理の型、証明、直接依存、宣言順、次の定理は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` および直後の `Reduction.lean` 生成ソースで確認しました。証明全体での位置付け、直接数値証明との比較、import 最小化、Comparator 案は解説上の分析または未検証の提案です。既存 PDF は補助的文脈資料として扱い、Lean ソースを優先しました。
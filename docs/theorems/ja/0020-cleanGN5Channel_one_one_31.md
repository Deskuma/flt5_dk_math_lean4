# 0020 — `cleanGN5Channel_one_one_31`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem cleanGN5Channel_one_one_31 : CleanGN5Channel 1 1 31 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · norm_num [GN5]
  · norm_num
  · norm_num [GN5]
```

完全修飾名は `DkMath.FLT.Five.cleanGN5Channel_one_one_31` です。

## 数学的主張

この定理は、$g=1$、$y=1$、$q=31$ に対して `CleanGN5Channel` が成立することを具体的に証明します。

$$
CleanGN5Channel(1,1,31)
$$

構造体の四つの条件へ展開すると、次を同時に主張しています。

1. $31$ は素数である。
2. $31∣GN5(1,1)$ である。
3. $31∤1$ である。
4. $31^2∤GN5(1,1)$ である。

既出の具体値

$$
GN5(1,1)=31
$$

を使えば、第二条件は $31∣31$、第四条件は $31^2∤31$ へ帰着します。したがって $31$ は `GN5(1,1)` にちょうど一度だけ現れ、gap $1$ には現れません。

## 証明全体での役割

これまでの `CleanGN5Channel` 系定理は、clean prime が与えられたときに何が導けるかを記述する consumer API でした。本定理は初めて、具体的な入力に対する clean channel を実際に構成する provider です。

この provider を直後の `GN5_one_one_not_fifth_power` へ渡すと、一般定理

```lean
not_fifth_power_GN5_of_clean
```

を具体化して、`GN5 1 1` が完全第五冪ではないことを一行で得られます。

本定理は一般の FLT5 反例排除を単独で完成させるものではありません。$g=y=1$ という有限例で、有限素数 escape と局所 no-lift 証明書の全経路が作動することを示す executable example です。

## 直接依存する定義・補題

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.GN5`
- `DkMath.FLT.Five.GN5_one_one` と同じ具体値計算
- `Nat.Prime 31` の数値判定
- tactic `refine`
- tactic `norm_num`

証明本文は `GN5_one_one` を名前で再利用せず、`norm_num [GN5]` により `GN5` を二度直接展開・評価しています。

## 証明の流れ

1. `refine ⟨by norm_num, ?_, ?_, ?_⟩` により、`CleanGN5Channel 1 1 31` の四フィールドを構築する。
2. 第一フィールド `prime` を `norm_num` で閉じ、$31$ の素数性を確認する。
3. 第二フィールド `dvd_GN5` を `norm_num [GN5]` で閉じる。`GN5(1,1)` を $31$ に評価し、$31∣31$ を示す。
4. 第三フィールド `not_dvd_gap` を `norm_num` で閉じ、$31∤1$ を示す。
5. 第四フィールド `noLift` を `norm_num [GN5]` で閉じる。$31^2∤31$ を数値的に確認する。

## Lean 固有の処理

```lean
refine ⟨by norm_num, ?_, ?_, ?_⟩
```

は構造体コンストラクタを用い、最初のフィールドをその場で解決し、残り三つを順番付きのゴールとして残します。フィールド名を明記する record syntax ではなく、宣言順に依存する positional syntax です。

```lean
norm_num [GN5]
```

は `GN5` の定義を展開し、自然数の冪・乗法・加法・整除性・非整除性を具体的な数値命題へ正規化します。ここで `ring` は不要です。変数を含む多項式恒等式ではなく、完全に閉じた数値計算だからです。

第四ゴールでは `¬31^2 ∣ GN5 1 1` を直接処理します。valuation や `Nat.factorization` は導入されず、有限算術だけで no-lift 条件を認証します。

## 冗長・重複箇所

`GN5 1 1` の計算は既出の `GN5_one_one` と重複します。また本定理内でも、第二フィールドと第四フィールドで `norm_num [GN5]` が二度実行されます。

現行形の利点は、四フィールドがそれぞれ独立した閉じた数値ゴールとなり、provider の監査が容易なことです。一方、`GN5` の定義変更時には同じ展開計算が複数箇所に現れます。

## 最適化候補

1. `rw [GN5_one_one]` または `simpa [GN5_one_one]` を使い、`GN5` の具体値計算を再利用する。
2. `have hGN : GN5 1 1 = 31 := GN5_one_one` を一度作り、`dvd_GN5` と `noLift` の双方で共有する。
3. positional syntax を record syntax

```lean
refine {
  prime := by norm_num
  dvd_GN5 := ?_
  not_dvd_gap := by norm_num
  noLift := ?_
}
```

へ変え、フィールド追加・並べ替えへの耐性を高める。
4. 一般の具体値 provider を作る場合、`GN5 g y = q` と `Nat.Prime q` から `CleanGN5Channel g y q` を得る補助定理を設計する。ただし `q∤g` は別途必要です。
5. `norm_num [GN5]` と `rw [GN5_one_one]; norm_num` の proof term、実行時間、エラー局所性を比較する。

以上は未検証の提案です。Lean ビルドは行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接必要とする機能は次の範囲です。

- 自然数の素数判定
- 自然数の整除性と非整除性
- 自然数の冪と具体的算術
- tactic `refine`
- tactic `norm_num`

`ring`、`omega`、valuation、`Nat.factorization` は本定理では使用しません。定理単独では import をかなり縮小できる可能性がありますが、同じ `CleanChannel.lean` には互いに素性、素数の冪整除、`ring` を使う定理も含まれるため、ファイル全体の最小 import は別問題です。import 最小化は未検証です。

## Comparator challenge 化の可否

小規模で明確な Comparator challenge に適しています。

比較候補は次の通りです。

- 現行の `norm_num [GN5]` による完全自動計算。
- `GN5_one_one` を書き換え補題として再利用する証明。
- positional constructor と record syntax の比較。
- `decide` による閉じた命題の判定可能部分と `norm_num` の比較。
- 四フィールドを個別補題として分離する方法。

比較軸は proof term の大きさ、定義変更への追従性、計算の重複、エラー位置の明瞭さ、provider の監査容易性です。数学的難度は低い一方、具体的証明書をどの粒度で再利用するかという Lean API 設計の教材になります。

## 次に読むべき定理

次は `DkMath.FLT.Five.GN5_one_one_not_fifth_power` です。

これは本定理を一般 consumer `not_fifth_power_GN5_of_clean` へ渡し、

$$
¬\exists x\in\mathbb{N},\ GN5(1,1)=x^5
$$

を得ます。具体 provider と抽象 consumer が一行で接続される最初の完成デモです。

## 根拠と推論の区別

定理の型、証明、宣言順、直接後続する定理は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認しました。証明全体での位置付け、重複評価、一般化、import 最小化、Comparator 案には解説上の分析または未検証の提案が含まれます。既存 PDF は補助的文脈資料として扱い、Lean ソースを優先しました。

---

[prev](./0019-not_fifth_power_body_of_clean.md) < 0020 > [next](./0021-GN5_one_one_not_fifth_power.md)

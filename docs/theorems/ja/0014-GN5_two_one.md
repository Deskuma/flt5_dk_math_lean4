# 0014 — `GN5_two_one`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem GN5_two_one : GN5 2 1 = 121 := by
  norm_num [GN5]
```

完全修飾名は `DkMath.FLT.Five.GN5_two_one` です。

## 数学的主張

`GN5` を gap $g=2$、基準座標 $y=1$ で評価すると $121=11^2$ になります。

$$
GN5(2,1)=2^4+5\cdot2^3+10\cdot2^2+10\cdot2+5=121
$$

標準巡回因子表示では $g+y=3$ なので、同じ値を

$$
GN5(2,1)=3^4+3^3+3^2+3+1=121
$$

と読めます。

## 証明全体での役割

本定理は `GN5_one_one` に続く第二の閉じた具体値評価であり、`GN5` の定義と数値正規化が別の入力でも期待どおり動くことを確認する smoke test です。

$121=11^2$ であるため、前号の $31$ とは局所素因子構造が異なります。ただし現行の直後の `CleanGN5Channel` 実演は `(g,y,q)=(1,1,31)` を使用しており、本定理は一般 FLT5 縮約の直接依存ではありません。

## 直接依存する定義・補題

- `DkMath.FLT.Five.GN5`
- `norm_num` tactic

数学的には `GN5_eq_homogeneous_cyclotomic 2 1` からも導けますが、現行証明は定義を直接展開します。

## 証明の流れ

1. `norm_num [GN5]` が `GN5` を展開する。
2. $g=2$、$y=1$ を代入する。
3. 自然数の冪・乗法・加法を正規化する。
4. 左辺が $121$ になることを確定する。

## Lean 固有の処理

`norm_num` は閉じた自然数等式を反射的に正規化します。`[GN5]` は評価前に展開する定義を明示します。変数・仮定・場合分けはなく、`ring` や `omega`、素数判定、整除性推論も不要です。

## 冗長・重複箇所

証明形は `GN5_one_one` と完全に同型です。この重複は意図的な smoke test と読めますが、一般証明では参照されないため、公開 API として残す価値は主に回帰検査と例示にあります。

## 最適化候補

複数の具体値を継続的に追加するなら、`example` 群または表形式テストへ整理する案があります。一方、名前付き theorem は外部文書や後続証明から再利用しやすいため、現状にも利点があります。

`GN5_eq_homogeneous_cyclotomic` を経由する証明は意味を可視化しますが、単純な閉計算に依存を増やすため必ずしも最適化ではありません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理に直接必要なのは自然数の冪・加減乗算と `norm_num` tactic です。`Mathlib.Tactic.NormNum` と基礎的な自然数代数 import まで絞れる可能性がありますが、Lean ビルドを行っていないため最小集合は未確定です。

## Comparator challenge 化の可否

適しています。候補は次のとおりです。

1. `norm_num [GN5]`
2. `unfold GN5; norm_num`
3. `rw [GN5_eq_homogeneous_cyclotomic]; norm_num`
4. `decide` または `native_decide` の適用可能性を検証する

比較軸は短さ、証明項の透明性、一般補題の再利用、必要 import、定義変更への耐性です。

## 次に読むべき定理

次は `DkMath.FLT.Five.CleanGN5Channel` です。これは定理ではなく `Prop` 値の構造体ですが、依存順では次の主要宣言です。

素数 $q$ が `GN5 g y` を割り、gap $g$ を割らず、さらに $q^2$ が `GN5 g y` を割らないという局所 valuation-one 条件を一つの監査可能な入力へ束ねます。

## 根拠と推論の区別

型、証明、宣言順、値 $121$、および次の主要宣言は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GN5.lean` と `CleanChannel.lean` の生成ソースで確認した事実です。$121=11^2$ という算術的観察、証明全体での位置づけ、import 最小化、Comparator 案は解説上の分析または未検証の提案を含みます。Lean ビルドは行っていません。

---

[prev](./0013-GN5_one_one.md) < 0014 > [next](./0015-CleanGN5Channel.md)

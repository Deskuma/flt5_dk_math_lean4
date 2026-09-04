# 0009 — `GN5_eq_g_pow_four_add_five_mul`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem GN5_eq_g_pow_four_add_five_mul (g y : ℕ) :
    GN5 g y =
      g ^ 4 + 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 +
        2 * g * y ^ 3 + y ^ 4) := by
  unfold GN5
  ring
```

完全修飾名は `DkMath.FLT.Five.GN5_eq_g_pow_four_add_five_mul` です。

## 数学的主張

`GN5` を $5$ の倍数部分と先頭項 $g^4$ に分けます。

$$
GN5(g,y)=g^4+5\bigl(g^3y+2g^2y^2+2gy^3+y^4\bigr)
$$

したがって、

$$
GN5(g,y)\equiv g^4\pmod 5
$$

と読めます。

## 証明全体での役割

直前の `GN5_eq_gap_mul_add_five_mul_y_pow_four` は gap $g$ を法とする分解でした。本定理は素数 $5$ を法とする分解であり、`GN5 g y` の five-adic 挙動を読む入口です。

特に $5\mid GN5(g,y)$ なら $5\mid g^4$ となり、冪の整除性補題と組み合わせて $5\mid g$ へ進めます。この後半は本定理単独の結論ではありません。

## 直接依存する定義・補題

プロジェクト固有の直接依存は `DkMath.FLT.Five.GN5` です。証明は Mathlib の `ring` tactic を使います。直前の gap 分解定理とは論理的に独立で、同じ `GN5` の別表示として並列に置かれています。

## 証明の流れ

1. `unfold GN5` で定義を展開する。
2. `ring` で両辺を可換半環上の多項式正規形へ変換する。

展開後の係数 $10$ は、右辺では $5\cdot2$ として現れます。

## Lean 固有の処理

`ring` は $g,y$ の具体値を計算せず、多項式恒等式を正規化します。自然数減算を使わないため、切り捨て減算の条件は不要です。また、本定理は整除性を直接証明するのではなく、後続で整除性や合同を読み出す等式 API を提供します。

## 冗長・重複箇所

証明スクリプトは直前の多項式恒等式と同じ `unfold GN5; ring` です。しかし用途は異なります。

- `GN5_eq_homogeneous_cyclotomic` は標準巡回因子との対応。
- gap 分解は $g$ を法とする合同解析。
- 本定理は $5$ を法とする five-adic 解析。

したがって、結論を異なる方向へ公開する API 群であり、単純な重複ではありません。

## 最適化候補

証明本体はすでに最小に近いです。改善候補は、後続で頻出するなら合同式や整除性を薄い補題として公開することです。例えば `GN5 g y % 5 = g ^ 4 % 5` や、適切な冪整除性補題を用いた `5 ∣ GN5 g y ↔ 5 ∣ g` が候補です。これらは未検証の提案です。

## 必要 Mathlib import と import 最適化候補

standalone は `import Mathlib` を使用しています。この定理の主要要件は自然数の半環演算、冪、`ring` tactic です。厳密な最小 import は資料から確定できません。`Mathlib.Tactic.Ring` と自然数の基本代数 import へ縮小できる可能性がありますが、clean build による確認が必要です。本作業では Lean ビルドを行っていません。

## Comparator challenge 化の可否

適しています。最短の `unfold GN5; ring`、`ring_nf`、手動係数整理を比較できます。さらに、等式から合同式や整除性へ進む二段課題にすると実践的です。

## 次に読むべき定理

次は `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5` です。

$$
(g+y)^5=y^5+g\,GN5(g,y)
$$

を固定し、`GN5` を第五冪差の実際の因数分解へ接続します。

## 根拠と推論の区別

定理本体、証明、宣言順、$GN5(g,y)\equiv g^4\pmod5$ という読みは Lean ソースに基づきます。補助 API、最小 import、Comparator 設計は分析・提案であり、追加の Lean 検証は行っていません。

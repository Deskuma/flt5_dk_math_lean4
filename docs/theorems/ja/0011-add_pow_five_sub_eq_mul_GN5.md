# 0011 — `add_pow_five_sub_eq_mul_GN5`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y := by
  rw [add_pow_five_eq_add_mul_GN5]
  omega
```

完全修飾名は `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5` です。

## 数学的主張

第五冪差は gap $g$ と斉次残余核 `GN5 g y` の積です。

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

これは第五冪差の標準因数分解を、$z=g+y$ という gap 座標で表したものです。

## 証明全体での役割

直前の `add_pow_five_eq_add_mul_GN5` は減算を含まない安全な加法形

$$
(g+y)^5=y^5+g\,GN5(g,y)
$$

を固定しました。本定理はそれを、後続の整除性・因子分離で直接利用しやすい差分形へ変換する API です。

次の `pow_five_sub_pow_five_eq_gap_mul_GN5` では $g=z-y$ を代入し、一般の $z^5-y^5$ を自然数 gap と `GN5` の積へ移します。

## 直接依存する定義・補題

プロジェクト固有の直接依存は次の一つです。

- `DkMath.FLT.Five.add_pow_five_eq_add_mul_GN5`

間接的には `GN5` の定義へ依存します。証明処理には Mathlib の `rw` と `omega` tactic を用います。

## 証明の流れ

1. `rw [add_pow_five_eq_add_mul_GN5]` により左辺を
   `(y ^ 5 + g * GN5 g y) - y ^ 5` へ書き換える。
2. `omega` が自然数の加法・減法関係を処理する。
3. 加えた `y ^ 5` を差し引いた結果が `g * GN5 g y` となり、目標を閉じる。

多項式展開は直前の定理で完了しており、本定理では再実行しません。

## Lean 固有の処理

`ℕ` の減算は切り捨て減算なので、整数の形式的移項として無条件に扱うべきではありません。ただし書き換え後の左辺は明示的に

$$
(y^5+g\,GN5(g,y))-y^5
$$

となるため、引かれる項が加法の一部として存在します。`omega` はこの自然数算術を処理しており、第五冪や `GN5` の多項式構造を解析しているわけではありません。

## 冗長・重複箇所

数学的には直前の加法形とほぼ同じ内容です。しかし API としては役割が異なります。

- 加法形は減算を避けた半環上の基礎恒等式。
- 本定理は差分・整除性・gap 因数分解へ接続する利用形。

したがって薄いラッパーではありますが、後続証明の可読性と書き換えの安定性を高める有用な宣言です。

## 最適化候補

`omega` を使わず、自然数の加算後の減算に関する標準補題で閉じる明示的証明が候補です。たとえば書き換え後に `Nat.add_sub_cancel_left` 系または項順に応じた対応補題を使える可能性があります。ただし補題名と向きは Lean ビルドで未検証です。

現在の二行証明は短く、前提も追加しないため、実用上は十分に最適化されています。

## 必要 Mathlib import と import 最適化候補

standalone は `import Mathlib` を使用しています。本定理自体の主要要件は自然数の加減算、書き換え、`omega` tactic です。

より狭い import として自然数算術と `Mathlib.Tactic.Omega` の組合せが候補ですが、正確な最小集合は Lean ビルドなしでは確定できません。本記事では import を変更していません。

## Comparator challenge 化の可否

適しています。比較候補は次の通りです。

1. 現行の `rw` と `omega`。
2. `rw` 後に自然数減算の標準補題を明示適用する証明。
3. `unfold GN5; ring` を再実行して直接証明する方法。

比較軸は依存 tactic、証明時間、自然数減算の意図の明瞭さ、上流定理の再利用度です。通常は 1 または 2 が 3 より構造的です。

## 次に読むべき定理

次は `DkMath.FLT.Five.pow_five_sub_pow_five_eq_gap_mul_GN5` です。

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

仮定 $y\le z$ のもとで `Nat.sub_add_cancel` を使い、抽象 gap $g$ から実際の自然数差 $z-y$ へ進みます。

## 根拠と推論の区別

定理の型、証明、直接依存、宣言順、次の定理は `Flt5DkMath/FLT5StandAlone.lean` 内の生成元 `DkMath/FLT/Five/GN5.lean` 部分から確認した事実です。最小 import、標準減算補題による代替証明、Comparator 評価は未検証の提案です。既存 PDF は証明全体の文脈資料であり、本記事の形式的根拠は Lean ソースです。Lean ビルドは行っていません。

---

[prev](./0010-add_pow_five_eq_add_mul_GN5.md) < 0011 > [next](./0012-pow_five_sub_pow_five_eq_gap_mul_GN5.md)

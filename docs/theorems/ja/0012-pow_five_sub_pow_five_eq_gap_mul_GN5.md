# 0012 — `pow_five_sub_pow_five_eq_gap_mul_GN5`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem pow_five_sub_pow_five_eq_gap_mul_GN5
    {y z : ℕ}
    (hyz : y ≤ z) :
    z ^ 5 - y ^ 5 = (z - y) * GN5 (z - y) y := by
  simpa [Nat.sub_add_cancel hyz] using
    (add_pow_five_sub_eq_mul_GN5 (z - y) y)
```

完全修飾名は `DkMath.FLT.Five.pow_five_sub_pow_five_eq_gap_mul_GN5` です。

## 数学的主張

$y\le z$ のとき、第五冪差は実際の gap $z-y$ と `GN5` の積です。

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

抽象恒等式 $(g+y)^5-y^5=g\,GN5(g,y)$ へ $g=z-y$ を代入した形です。

## 証明全体での役割

直前の抽象 gap 版を、FLT5 方程式から現れる自然数差 $z-y$ へ接続します。`fifth_sub_eq_of_add_eq` と組み合わせると、後続で

$$
x^5=(z-y)\,GN5(z-y,y)
$$

を得るための因数分解インターフェースになります。

## 直接依存する定義・補題

- `DkMath.FLT.Five.add_pow_five_sub_eq_mul_GN5`
- `Nat.sub_add_cancel`
- `simpa`

`GN5` には間接的に依存します。

## 証明の流れ

1. 上流定理へ $g=z-y$ を代入する。
2. 左辺は `((z - y) + y) ^ 5 - y ^ 5` となる。
3. `Nat.sub_add_cancel hyz` で `(z-y)+y=z` と書き換える。
4. `simpa` が目的の式へ正規化する。

本証明では多項式展開、`ring`、`omega` を再実行しません。

## Lean 固有の処理

`ℕ` の減算は切り捨て減算なので、`(z-y)+y=z` には `hyz : y ≤ z` が必要です。`Nat.sub_add_cancel hyz` が切り捨ての不発生を保証します。

## 冗長・重複箇所

数学的には直前の定理の特殊化です。しかし、実際の gap $z-y$ を直接扱う API として、後続で同じ減算処理を繰り返すのを防ぎます。

## 最適化候補

現行証明は非常に小さいです。代案は `rw [← Nat.sub_add_cancel hyz]` と `exact` を分ける形ですが、現在の `simpa using` の方が簡潔です。`GN5` を展開して直接証明する案は依存構造上の後退です。

## 必要 Mathlib import と import 最適化候補

standalone は `import Mathlib` です。本定理自身は自然数減算、冪・乗法、`simpa` を必要とし、`ring` や `omega` は直接不要です。正確な最小 import は Lean ビルドなしでは未確定です。

## Comparator challenge 化の可否

適しています。

1. 現行の `simpa [Nat.sub_add_cancel hyz] using ...`。
2. `rw` と `exact` を分離する証明。
3. `GN5` 展開からの直接証明。

比較軸は証明長、上流 API の再利用、減算条件の可視性、保守性です。

## 次に読むべき定理

次は `DkMath.FLT.Five.GN5_one_one` です。

$$
GN5(1,1)=31
$$

一般恒等式から有限素数 escape の具体例へ移る評価補題です。

## 根拠と推論の区別

型、証明、宣言順、直接依存は `Flt5DkMath/FLT5StandAlone.lean` の `DkMath/FLT/Five/GN5.lean` 部分で確認した事実です。役割分析、最小 import、Comparator 評価は未検証の提案を含みます。形式的根拠は Lean ソースです。Lean ビルドは行っていません。

---

[prev](./0011-add_pow_five_sub_eq_mul_GN5.md) < 0012 > [next](./0013-GN5_one_one.md)

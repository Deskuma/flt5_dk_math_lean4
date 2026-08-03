# 0004 — `right_lt_of_fermat5Equation`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem right_lt_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    y < z := by
  unfold Fermat5Equation at hEq
  have hx5 : 0 < x ^ 5 := pow_pos hx 5
  have hy5z5 : y ^ 5 < z ^ 5 := by
    omega
  exact (Nat.pow_lt_pow_iff_left (by decide : 5 ≠ 0)).mp hy5z5
```

完全修飾名は `DkMath.FLT.Five.right_lt_of_fermat5Equation` です。

## 数学的主張

自然数 $x,y,z$ が指数5のフェルマー方程式

$$
x^5+y^5=z^5
$$

を満たし、さらに $0<x$ ならば、$y<z$ です。

正の量 $x^5$ を $y^5$ に加えたものが $z^5$ なので、第五冪の段階で $y^5<z^5$ となります。自然数上で正の指数による冪は底の大小を反映するため、最後に $y<z$ が得られます。

## 証明全体での役割

この補題は、フェルマー方程式を **順序情報** へ変換する最初の橋です。

直前の `fifth_sub_eq_of_add_eq` は

$$
z^5-y^5=x^5
$$

という差分恒等式を与えました。しかし自然数の減算は切り捨て減算であるため、後続で gap `z-y` を本当に正の差として扱うには、先に $y<z$ を確立する必要があります。

本補題の直接の利用先は `gap_pos_of_fermat5Equation` です。そこで `Nat.sub_pos_of_lt` を適用し、

$$
0<z-y
$$

を得ます。この正の gap が、後続の `GN5 (z-y) y` による第五冪差分の因数分解へ入るための座標になります。

## 直接依存する定義・補題

### プロジェクト内依存

- `DkMath.FLT.Five.Fermat5Equation`

### Lean・Mathlib 側の主要依存

- `pow_pos`
- `Nat.pow_lt_pow_iff_left`
- `omega`
- `by decide : 5 ≠ 0`

`fifth_sub_eq_of_add_eq` は数学的に近い前号ですが、この証明から直接呼ばれてはいません。本補題は元の加法方程式を直接展開して順序を導きます。

## 証明の流れ

1. `unfold Fermat5Equation at hEq` により、仮定を生の等式 $x^5+y^5=z^5$ へ戻します。
2. `pow_pos hx 5` により $0<x^5$ を得て、`hx5` と名付けます。
3. `omega` に `hEq` と `hx5` を使わせ、$y^5<z^5$ を導きます。
4. `Nat.pow_lt_pow_iff_left` の逆向き `mp` により、第五冪の比較から底の比較 $y<z$ へ戻します。
5. 指数が非零であることは `(by decide : 5 ≠ 0)` で閉じます。

証明の本質は「正の項を加えた等式」から「冪の厳密不等式」を得て、その冪写像の単調性を逆向きに読む二段階です。

## Lean 固有の処理

### `omega` が扱っているもの

`omega` は第五冪を展開していません。`x ^ 5`、`y ^ 5`、`z ^ 5` を自然数の項として扱い、

- `0 < x ^ 5`
- `x ^ 5 + y ^ 5 = z ^ 5`

から線形算術として `y ^ 5 < z ^ 5` を導いています。

### `Nat.pow_lt_pow_iff_left`

ここでは冪の不等式を底の不等式へ戻すために使われます。指数 $5$ が非零であることを明示する必要があるため、有限決定可能な命題を `by decide` で証明しています。

### 暗黙引数

`x y z` は `{x y z : ℕ}` と暗黙引数になっています。通常は `hx` と `hEq` から Lean が三変数を推論します。

## 冗長・重複箇所

`hx5` は一度しか使われませんが、数学的な中間事実を明示する有益な名前です。インライン化は可能でも、可読性は下がる可能性があります。

また、直前の `fifth_sub_eq_of_add_eq` を用いれば別証明を構成できる可能性がありますが、自然数減算から正の順序を逆算するには追加の注意が必要です。現在の加法方程式から直接進む証明は、切り捨て減算を回避しており堅牢です。

## 最適化候補

候補は次の三つです。ただし、いずれも Lean ビルドで未検証です。

1. `hx5` を `omega` 呼出し内へインライン化する。
2. `Nat.pow_lt_pow_iff_left` 以外の単調性補題を使い、証明の向きをより明示する。
3. `Fermat5Equation` から第五冪不等式を得る小補題を独立させ、左右対称版でも再利用する。

現在の証明は短く、順序橋として十分明快なので、最適化の利益は限定的です。

## 必要 Mathlib import と import 最適化候補

standalone は `import Mathlib` を使用しており、この環境での成立がリポジトリに記録されています。

本補題が必要とする機能は概ね次です。

- 自然数の冪と順序
- `pow_pos`
- `Nat.pow_lt_pow_iff_left`
- `omega` tactic
- `decide`

厳密な最小 import は確認できていません。候補探索では `#min_imports` を利用できますが、tactic import と定理 import の双方を含めて clean build で検証する必要があります。具体的 import 名をここで断定しないのは、未検証のためです。

## Comparator challenge 化

適しています。小さいながら、次の異なる証明戦略を比較できます。

- 現行の `pow_pos` + `omega` + `Nat.pow_lt_pow_iff_left`
- 冪の厳密単調性を前面に出した構造的証明
- `fifth_sub_eq_of_add_eq` を経由する差分ベースの証明

特に、自然数減算を経由する証明が余分な順序仮定を必要とするかを比較すると、Lean における `Nat.sub` の扱いを学ぶ良い課題になります。

## 次に読む定理

次は `DkMath.FLT.Five.gap_pos_of_fermat5Equation` です。

本補題で得た $y<z$ を `Nat.sub_pos_of_lt` に渡し、後続の局所座標となる gap `z-y` の正値性を確定します。

## 根拠と推論の区別

定理の型、証明項、直接利用する補題、直後に `gap_pos_of_fermat5Equation` が置かれていることは Lean ソースに基づく確認事実です。

import 最小化、代替証明、左右対称補題への抽出、Comparator 課題としての評価は本稿の分析・提案です。今回は Lean ビルドを実行していません。

---

[prev](./0003-fifth_sub_eq_of_add_eq.md) < 0004 > [next](./0005-gap_pos_of_fermat5Equation.md)

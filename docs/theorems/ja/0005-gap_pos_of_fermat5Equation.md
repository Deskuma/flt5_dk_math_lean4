# 0005 — `gap_pos_of_fermat5Equation`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem gap_pos_of_fermat5Equation
    {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    0 < z - y := by
  exact Nat.sub_pos_of_lt (right_lt_of_fermat5Equation hx hEq)
```

完全修飾名は `DkMath.FLT.Five.gap_pos_of_fermat5Equation` です。

## 数学的主張

自然数 $x,y,z$ が指数5のフェルマー方程式

$$
x^5+y^5=z^5
$$

を満たし、さらに $0<x$ ならば、右辺の底 $z$ と第二項の底 $y$ の差は正です。

$$
0<z-y
$$

自然数上では、この主張は単に「差が存在する」という意味以上のものを持ちます。Lean の自然数減算は切り捨て減算なので、`0 < z - y` は実質的に `y < z` を記録しており、後続の gap 座標が退化していないことを保証します。

## 証明全体での役割

この定理は、方程式の大域的な三変数表示から、局所 gap 座標

$$
g=z-y
$$

へ移るための正値性証明です。

直前の `right_lt_of_fermat5Equation` が $y<z$ を導き、本定理がそれを $0<z-y$ へ変換します。この正の gap は、後続で `GN5 (z-y) y` を用いる因数分解、原始性、五進的分岐を扱う際の基本入力になります。

重要なのは、本定理が新しい代数恒等式を証明しているのではなく、すでに得られた順序情報を「差そのものの正値性」という後続 API に適した形へ再符号化している点です。

## 直接依存する定義・補題

プロジェクト内の直接依存は次の二つです。

- `DkMath.FLT.Five.Fermat5Equation`
- `DkMath.FLT.Five.right_lt_of_fermat5Equation`

Mathlib 側では次を直接使用します。

- `Nat.sub_pos_of_lt`

`right_lt_of_fermat5Equation hx hEq` が `y < z` を返し、`Nat.sub_pos_of_lt` がそれを `0 < z - y` へ変換します。

## 証明の流れ

証明は一段だけです。

1. `hx` と `hEq` を `right_lt_of_fermat5Equation` に渡し、`y < z` を得る。
2. `Nat.sub_pos_of_lt` を適用し、`0 < z - y` を得る。

Lean コード上でも、この数学的構造がそのまま一行に表れています。

```lean
exact Nat.sub_pos_of_lt (right_lt_of_fermat5Equation hx hEq)
```

途中の算術 tactic、冪の単調性、等式変形はすべて前定理へ封じ込められています。

## Lean 固有の処理

Lean の `ℕ` における減算は整数の減算とは異なり、負の結果を $0$ に切り詰めます。したがって `z - y` を後続で正の gap として扱うには、先に `y < z` を証明する必要があります。

`Nat.sub_pos_of_lt` はこの境界を明示する標準補題です。

```lean
Nat.sub_pos_of_lt : y < z → 0 < z - y
```

本定理は `omega` や `ring` を使用せず、前段で得た順序証明を標準 API へ接続するだけです。そのため、証明依存の境界が明瞭です。

なお、逆向きには `Nat.lt_of_sub_pos` が利用できるため、自然数上では次の二つは相互変換できます。

$$
y<z \quad\Longleftrightarrow\quad 0<z-y
$$

この同値性自体は本定理では証明していません。

## 冗長・重複箇所

`right_lt_of_fermat5Equation` と本定理は、数学的には非常に近い情報を保持しています。その意味では API 上の重複候補に見えます。

しかし用途は異なります。

- `right_lt_of_fermat5Equation` は底の順序比較を提供する。
- `gap_pos_of_fermat5Equation` は具体的な差 `z-y` の正値性を提供する。

後続コードが gap を変数として扱うなら、本定理を独立した名前で保持することには意味があります。したがって、これは不要な重複というより、同じ事実の異なる利用形を公開する薄い橋と評価するのが妥当です。

## 最適化候補

証明はすでに最小に近く、演算コスト上の最適化余地はほぼありません。

候補があるとすれば API 整理です。

- 順序形と gap 正値形のどちらを標準入口にするかを後続モジュールで統一する。
- `CounterexamplePack` から直接 gap 正値性を取り出す補助補題が頻出するなら、構造体版ラッパーを追加する。
- `right_lt_of_fermat5Equation` と本定理の双方が頻繁に必要なら、局所で一度だけ順序証明を構築し再利用する。

ただし現状の一行証明をインライン化して削除すると、後続コードから「正の gap を得る」という意図が見えにくくなる可能性があります。

## 必要 Mathlib import と import 最適化候補

standalone は `import Mathlib` を使用しているため、現在の環境で本定理が利用可能であることはリポジトリから確認できます。

本定理固有の Mathlib 依存は主に自然数減算の順序補題 `Nat.sub_pos_of_lt` です。ただし、前提となる `right_lt_of_fermat5Equation` が `pow_pos`、`Nat.pow_lt_pow_iff_left`、`omega` を利用するため、モジュール全体の最小 import は本定理一行だけからは決まりません。

import 最適化を行う場合は、`Basic.lean` 全体を対象に `#min_imports` などで候補を調べ、clean build で確認すべきです。具体的な最小 import 名は本稿では未検証です。

## Comparator challenge 化の可否

単独では初級 challenge に適しています。課題は次の形にできます。

```lean
example {x y z : ℕ}
    (hx : 0 < x)
    (hEq : Fermat5Equation x y z) :
    0 < z - y := by
  -- fill here
```

比較候補は次の三方式です。

1. 既存の `right_lt_of_fermat5Equation` と `Nat.sub_pos_of_lt` を使う一行証明。
2. 中間事実 `have hyz : y < z := ...` を明示する可読性重視の証明。
3. `Fermat5Equation` を展開して直接算術処理する証明。

第3方式は依存の再実装となるため、通常は第1または第2方式が望ましいという比較教材になります。

## 次に読むべき定理

次は `DkMath.FLT.Five.GN5` を読むのが自然です。

ここまでで正の gap `g=z-y` を利用できる状態になりました。次の定義 `GN5 g y` は、第五冪差

$$
(g+y)^5-y^5
$$

から gap `g` を取り出した残余因子を、局所座標で固定します。これは FLT5 証明の主要な因数分解核への入口です。

## 根拠と推論の区別

定理の型、証明本体、直接依存、`Nat.sub_pos_of_lt` の使用、後続の `GN5` 定義へのソース順は Lean ソースに直接基づきます。

本定理を「API 再符号化の橋」と見る評価、構造体版ラッパーの提案、Comparator の比較設計、最小 import に関する見通しは分析または未検証の提案です。今回は Lean ビルドを実行していません。

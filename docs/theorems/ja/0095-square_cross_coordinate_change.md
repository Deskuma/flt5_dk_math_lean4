# 0095 — `square_cross_coordinate_change`

## Lean の型

```lean
theorem square_cross_coordinate_change (g y : ℕ) :
    g ^ 2 + 2 * (y * (g + y)) = (g + y) ^ 2 + y ^ 2 := by
  ring
```

## 数学的主張

本定理は、自然数 $g,y$ に対して

$$
g^2+2y(g+y)=(g+y)^2+y^2
$$

が成り立つことを主張する。

左辺は前号 0094 `GN5_eq_square_cross_form` で現れた square/cross 座標

$$
A=g^2,\qquad B=y(g+y)
$$

を使えば

$$
A+2B
$$

であり、右辺は二つの endpoint square の和

$$
(g+y)^2+y^2
$$

である。

したがって本定理は、単なる二次式恒等式というより、`GN5` を黄金比型二次形式へ送る際に使う座標変換

$$
(g^2,\,y(g+y))
\longrightarrow
((g+y)^2+y^2,\,(g+y)y)
$$

の第一成分を保証する補題と読める。

## 証明全体での役割

0094 では

$$
\mathrm{GN5}(g,y)
=(g^2)^2+5g^2y(g+y)+5\bigl(y(g+y)\bigr)^2
$$

という square/cross form を得た。

次の `GN5_eq_goldenNorm_squareLink` は、この式を 0093 `GoldenNorm`

$$
\mathrm{GoldenNorm}(m,n)=m^2+mn-n^2
$$

へ一致させる。その際の座標は

$$
m=(g+y)^2+y^2,
\qquad
n=(g+y)y
$$

である。

本定理は、この $m$ が前段の square/cross 座標から

$$
m=g^2+2y(g+y)
$$

とも書けることを保証する。つまり proof graph 上では

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross form}
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}
$$

の中央の座標変換に当たる。

この補題自体は後続 theorem の証明本文で名前を直接呼ばず、`ring` により同じ恒等変形を一括処理できる場合がある。しかし、数学的な橋の意味を独立した theorem 名として残すことで、なぜ endpoint-square coordinates が自然に現れるかを可視化している。

## 直接依存する定義・補題

project-local な定義・補題への直接依存はない。

直接必要なのは次の要素である。

1. 自然数 `ℕ` の加法・乗法・冪。
2. 可換半環上の多項式恒等式を処理する `ring` tactic。

0094 `GN5_eq_square_cross_form` と 0093 `GoldenNorm` は証明本文から直接参照されないが、証明全体での意味論的な前後関係として重要である。

## 証明の流れ

証明は

```lean
ring
```

のみで閉じる。

手計算では右辺を展開して

$$
(g+y)^2+y^2
=g^2+2gy+y^2+y^2
$$

となり、左辺は

$$
g^2+2y(g+y)
=g^2+2gy+2y^2
$$

なので一致する。

減法や除法は一切なく、自然数上の可換半環恒等式だけであるため、`ring` が最適な証明手段の一つである。

## Lean 固有の処理

### 1. `ring` による半環正規化

Lean は結合則・交換則・分配則だけから、この二つの式が同じとは自動では判断しない。`ring` が両辺を正規形へ落とし、同一の多項式であることを確認する。

### 2. `ℕ` 上で完結する

本 theorem は `ℕ` だけを使い、整数への coercion はまだ導入しない。次の `GN5_eq_goldenNorm_squareLink` では `GoldenNorm : ℤ → ℤ → ℤ` に接続するため `ℕ → ℤ` cast が現れるが、本補題はその直前まで自然数世界に留まる。

### 3. coercion 補題を不要にする設計

座標恒等式を `ℕ` 上で独立させているため、`norm_cast`、`push_cast`、`Int.ofNat` に関する処理を混ぜずに純粋な多項式恒等式として検証できる。この分離は後続 bridge の複雑さを局所化する。

## 冗長・重複箇所

証明技術だけを見れば、本定理は後続 `GN5_eq_goldenNorm_squareLink` の `ring` 証明へ完全に inline できる種類の補題である。

また数学的にも

$$
(a-b)^2+2b a=a^2+b^2
$$

を $a=g+y$, $b=y$ とした特殊形と見ることができ、一般恒等式の一例に過ぎない。

しかし本 theorem の名前は `square_cross_coordinate_change` であり、目的は一般代数補題を増やすことではなく、proof architecture 上の座標変更を明示することにある。したがって、式としての重複はあるが、説明用 interface としては有益である。

## 最適化候補

### 候補 A — 現状維持

最も説明力が高い。短い theorem で座標変換の意味を固定でき、次の golden bridge を読む際の中間地点になる。

### 候補 B — 後続 theorem へ inline

`GN5_eq_goldenNorm_squareLink` 内で `unfold GN5 GoldenNorm; push_cast; ring` のように一括処理すれば、本 theorem を削除できる可能性がある。

コード量は減るが、square/cross から endpoint-square への変換が proof graph から見えにくくなる。

### 候補 C — 一般恒等式へ抽象化

例えば可換半環上で

$$
x^2+2y(x+y)=(x+y)^2+y^2
$$

を一般 theorem として定義する案がある。

ただし現時点で他の利用箇所がなければ、抽象化コストが利益を上回る可能性が高い。

### 候補 D — 座標構造を定義する

今後 square/cross coordinates が複数箇所で再利用されるなら、

```lean
A := g ^ 2
B := y * (g + y)
M := (g + y) ^ 2 + y ^ 2
N := (g + y) * y
```

を named structure または helper definitions にまとめ、`M = A + 2 * B` のような形で API 化する余地がある。

現状では一回限りの bridge に見えるため、やや過剰設計である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` を使用している。

本 theorem 単体に必要なのは自然数の基本的な半環構造と `ring` tactic である。したがって umbrella `Mathlib` は単独 theorem に対しては過大であり、import 最適化を行う場合は `ring` tactic を提供する Mathlib module と自然数の基本代数だけに縮小できる可能性が高い。

ただし、対象ブランチでは分割元 `SquareGoldenBridge.lean` の実ファイルを取得できず、generated standalone から構成を確認している。そのため具体的な最小 import module 名は build 検証なしに断定しない。

`SquareGoldenBridge.lean` 全体では次の theorem から整数 coercion と `GoldenNorm` が関与するため、module 全体の import 最適化は本補題だけで決めるべきではない。

## Comparator challenge 化の可否

適している。ただし challenge は難しい数学ではなく、proof engineering と説明力の比較になる。

比較候補は次の通り。

1. 現行の `ring` 一行証明。
2. `ring_nf` による証明。
3. `simp [pow_two, mul_add, add_mul]` などの rewrite 中心の証明。
4. 本 theorem を削除して `GN5_eq_goldenNorm_squareLink` に inline する設計。
5. 一般可換半環恒等式として抽象化したうえで specialization する設計。

評価軸は、proof term の短さ、読みやすさ、import の軽さ、座標変換の意味が名前として残るか、後続 theorem の監査性が上がるか、である。

現行 `ring` は局所証明としてほぼ最短であり、Comparator の主な論点は「この theorem を独立して残す価値」にある。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。そこでは 0094 `GN5_eq_square_cross_form` の直後に本 theorem が置かれ、その次に `GN5_eq_goldenNorm_squareLink` が続くことを確認した。

standalone の manifest コメントでは、この区間が `DkMath/FLT/Five/SquareGoldenBridge.lean` に由来すると記録されている。

既存日本語・英語 PDF の具体的対応箇所を GitHub code search で検索したが、この回も upstream 502 となり、ページ・節番号は検証できなかった。したがって PDF 固有の説明は推測で補っていない。

なお、分割元と推定される repository path を直接取得する試みは 404 だったため、分割元ファイルの import header についても推測で断定していない。

## 次に読むべき宣言

source 上の直後は

```lean
theorem GN5_eq_goldenNorm_squareLink (g y : ℕ) :
    (GN5 g y : ℤ) =
      GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) := by
  unfold GN5 GoldenNorm
  ...
```

である。

ここで初めて

$$
\mathrm{GN5}(g,y)
$$

と

$$
\mathrm{GoldenNorm}\bigl((g+y)^2+y^2,\,(g+y)y\bigr)
$$

が直接等置される。

0094 が `GN5` を square/cross form へ圧縮し、0095 が endpoint-square coordinates を明示した。次の 0096 は、その二段階を黄金比型二次形式へ結実させる bridge 本体である。
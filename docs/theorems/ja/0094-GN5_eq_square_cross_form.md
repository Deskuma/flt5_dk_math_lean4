# 0094 — `GN5_eq_square_cross_form`

## Lean の型

```lean
theorem GN5_eq_square_cross_form (g y : ℕ) :
    GN5 g y =
      (g ^ 2) ^ 2 +
        5 * (g ^ 2) * (y * (g + y)) +
        5 * (y * (g + y)) ^ 2 := by
  unfold GN5
  ring
```

## 数学的主張

`GN5` を

$$
\mathrm{GN5}(g,y)
=g^4+5g^3y+10g^2y^2+10gy^3+5y^4
$$

とすると、本定理はこれを

$$
\mathrm{GN5}(g,y)
=(g^2)^2+5g^2\,y(g+y)+5\bigl(y(g+y)\bigr)^2
$$

と書き換える。

ここで

$$
A=g^2,\qquad B=y(g+y)
$$

と置けば、右辺は

$$
A^2+5AB+5B^2
$$

という二変数二次形式になる。

これは単なる展開公式ではなく、五次円分因子 `GN5` を「次数4の多項式」から「二つの次数2座標に関する二次形式」へ圧縮する座標変換である。

## 証明全体での役割

0093 `GoldenNorm` では黄金比型二次形式

$$
N(m,n)=m^2+mn-n^2
$$

を受け皿として導入した。本定理 0094 は、その受け皿へ接続する前段として `GN5` を square/cross coordinates に整形する。

proof graph 上では

$$
\mathrm{GN5}(g,y)
\longrightarrow
A^2+5AB+5B^2
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}
$$

という橋の最初の実計算に当たる。

特に次の `square_cross_coordinate_change` が

$$
g^2+2y(g+y)=(g+y)^2+y^2
$$

を与えるため、$A=g^2$ と $B=y(g+y)$ の組から

$$
m=(g+y)^2+y^2,
\qquad
n=(g+y)y
$$

へ移る準備が整う。

## 直接依存する定義・補題

直接依存は少ない。

1. `GN5`
2. 自然数上の加法・乗法・冪
3. `ring` tactic

project-local な直接依存は `GN5` のみである。

`GoldenNorm` は意味論的には直後の流れに関係するが、本定理の型・証明本文からは直接参照されない。

## 証明の流れ

証明は二段階だけである。

```lean
unfold GN5
```

で `GN5` の定義

$$
g^4+5g^3y+10g^2y^2+10gy^3+5y^4
$$

を露出する。

次に

```lean
ring
```

で両辺を可換半環上の正規形へ展開し、多項式恒等式として一致させる。

右辺を手で展開すると

$$
(g^2)^2=g^4,
$$

$$
5g^2y(g+y)=5g^3y+5g^2y^2,
$$

$$
5\bigl(y(g+y)\bigr)^2
=5g^2y^2+10gy^3+5y^4,
$$

したがって合計は

$$
g^4+5g^3y+10g^2y^2+10gy^3+5y^4
$$

となる。

## Lean 固有の処理

### 1. `unfold GN5`

`GN5` は通常の `def` なので、`ring` に渡す前に定義を明示的に展開している。これにより theorem statement では抽象名 `GN5` を保ち、証明内部だけで多項式へ降りる。

### 2. `ring`

自然数 `ℕ` は可換半環なので、この恒等式には減法がなく `ring` がそのまま適用できる。個別の distributivity や associativity を手で並べる必要はない。

### 3. 型注釈が不要

全項が `ℕ` 上で統一されているため、0093 以降に現れる `ℕ → ℤ` coercion はまだ不要である。これは bridge のうち「自然数側で完結する最終区間」の一つでもある。

## 冗長・重複箇所

数学的には `GN5` の別表示なので、0079以前の `GN5_eq_*` 系補題と同種の rewrite theorem である。

特に既存の

- `GN5_eq_gap_mul_add_five_mul_y_pow_four`
- `GN5_eq_g_pow_four_add_five_mul`

も同じ `GN5` を異なる目的に合わせて再配置している。

したがって式変形という意味では重複しているが、用途は異なる。以前の補題は divisibility / five-adic 分離のため、本定理は quadratic-coordinate bridge のための形である。これは意図的な normal-form duplication と見るべきである。

## 最適化候補

### 候補 A — 現行 theorem を維持

最も読みやすい。後続の golden bridge が必要とする形を theorem 名で明示できる。

### 候補 B — 一般恒等式へ抽象化

例えば

$$
X^2+5XY+5Y^2
$$

型の helper を一般化し、`X=g^2`, `Y=y(g+y)` を代入する設計も可能である。

ただし本 theorem は一行 `ring` で閉じており、抽象化の利益は小さい。

### 候補 C — `GN5_eq_goldenNorm_squareLink` に inline

後続 theorem 内で直接 `unfold GN5 GoldenNorm; ring` とすれば、本 theorem を削除すること自体は可能である。

しかし square/cross 座標という中間構造が proof graph から消えるため、監査性と数学的説明力は低下する。

### 候補 D — `ring_nf` による正規形固定

証明 tactic を `ring_nf` に置き換える案もあるが、goal を閉じるだけなら `ring` の方が意図が明快である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` で構築されている。

本定理単体に必要なのは、`GN5` の定義に加えて自然数の基本環構造と `ring` tactic である。したがって umbrella `Mathlib` は theorem 単体としては過大である。

一方 `SquareGoldenBridge.lean` 全体では、後続 theorem が整数 coercion、`push_cast`、`norm_num` なども利用するため、module 全体の最小 import は本 theorem だけからは決められない。

分割元 module の import header と build をこの回では検証していないため、具体的な最小 module 名は推測で断定しない。import 最適化を行うなら `ring` と必要 coercion tactics を個別に残しながら build で削るのが安全である。

## Comparator challenge 化の可否

適している。

比較候補は次の通り。

1. 現行の `unfold GN5; ring`。
2. 既存 `GN5_eq_*` 補題を組み合わせる rewrite 証明。
3. `ring_nf` を使う証明。
4. 本 theorem を削除し `GN5_eq_goldenNorm_squareLink` に inline する設計。

評価軸は proof term の短さだけでなく、中間座標の意味が theorem 名として残るか、後続の golden bridge が読みやすいか、import が軽いか、変更耐性があるか、である。

現行証明は tactic としてほぼ最短であり、challenge の主眼は「この中間 theorem を残す設計価値」にある。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。そこでは `GoldenNorm` の直後に本 theorem が置かれ、証明が `unfold GN5; ring` であることを確認した。

既存日本語・英語 PDF の具体的対応箇所を GitHub code search で確認しようとしたが、今回も upstream 502 となりページ・節番号までは検証できなかった。したがって PDF 固有の記述は推測で補っていない。

## 次に読むべき宣言

source 上の直後は

```lean
theorem square_cross_coordinate_change (g y : ℕ) :
    g ^ 2 + 2 * (y * (g + y)) = (g + y) ^ 2 + y ^ 2 := by
  ring
```

である。

これは square/cross 座標の一次結合

$$
g^2+2y(g+y)
$$

を endpoint square sum

$$
(g+y)^2+y^2
$$

へ変換する。

0094 が `GN5` を $(A,B)$ 二次形式へ圧縮する回なら、0095 はその座標を黄金ノルムに適した endpoint coordinates へ読み替える回となる。
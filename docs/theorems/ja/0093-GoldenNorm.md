# 0093 — `GoldenNorm`

## Lean の型

```lean
def GoldenNorm (m n : ℤ) : ℤ :=
  m ^ 2 + m * n - n ^ 2
```

本宣言は `DkMath/FLT/Five/SquareGoldenBridge.lean` の最初の定義であり、five-adic exact power-split 層を閉じた 0092 の直後から始まる新しい algebraic bridge の入口である。

型は単純で、二つの整数座標 `m n : ℤ` を受け取り整数を返す。

## 数学的主張

`GoldenNorm` は二変数二次形式

$$
N(m,n)=m^2+mn-n^2
$$

を名前付き定義として導入する。

これは黄金比 $\varphi$ が

$$
\varphi^2=\varphi+1
$$

を満たすとき、形式的な元 $m+n\varphi$ の共役積

$$
(m+n\varphi)(m+n\varphi')
$$

に現れるノルム形である。ここで $\varphi'$ はもう一方の根で、

$$
\varphi+\varphi'=1,\qquad \varphi\varphi'=-1
$$

だから、展開すると

$$
m^2+mn-n^2
$$

を得る。

ただし、この定義そのものは数体、代数的整数、共役写像を導入していない。source comment も「later realized as the norm」としており、この段階では純粋な整数二次形式として扱うのが正確である。

## 証明全体での役割

0092 までの流れでは、FLT5 の Branch-B candidate を five-adic に正規化し、最終的に exact fifth-power split を得る層を構築した。

0093 からは観点が変わる。`SquareGoldenBridge.lean` は `GN5` を endpoint-square coordinates によって黄金比型二次形式へ書き換える。

source の module comment は座標を

$$
m=(g+y)^2+y^2,
$$

$$
n=(g+y)y
$$

と置き、`GN5 g y` を

$$
N(m,n)=m^2+mn-n^2
$$

として読むことを目的としている。

したがって `GoldenNorm` は、これまで自然数上の五次円分因子として扱われていた `GN5` を、後続の golden-order arithmetic が扱える二次形式へ移すための名前付き受け皿である。

proof graph 上では、おおまかに

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross coordinates}
\longrightarrow
\mathrm{GoldenNorm}
\longrightarrow
\text{discriminant-5 form}
\longrightarrow
\text{golden arithmetic}
$$

という新しい章の入口に位置する。

## 直接依存する定義・補題

本定義自身の直接依存は極めて少ない。

1. `ℤ`
2. 整数の加法 `+`
3. 整数の乗法 `*`
4. 整数の減法 `-`
5. 冪 `^ 2`

project-local theorem や prior FLT5 declaration を定義本文から直接参照しない。

ただし意味論的には、直後の `GN5_eq_goldenNorm_squareLink` が `GN5` と本定義を接続するため、`GoldenNorm` は `GN5` bridge の target vocabulary として導入されている。

## 証明の流れ

定義なので証明本文はない。

Lean は

```lean
GoldenNorm m n
```

を必要に応じて

```lean
m ^ 2 + m * n - n ^ 2
```

へ展開する。

後続 theorem では `unfold GoldenNorm` によってこの二次形式を露出し、`ring` による多項式恒等式の正規化へ渡している。

特に source 直後の `GN5_eq_goldenNorm_squareLink` と `four_mul_goldenNorm_eq_discriminant_five` は、いずれも `GoldenNorm` を unfold したあと環計算で閉じる構造を持つ。

## Lean 固有の処理

### 1. `def` として抽象化境界を作る

単なる式

```lean
m ^ 2 + m * n - n ^ 2
```

を各 theorem に直接書かず `GoldenNorm` と命名することで、後続の型と theorem 名に数学的意味を持たせている。

### 2. domain を `ℤ` に固定

`GN5` は上流では `ℕ` 上の量として現れるが、黄金比ノルムでは負値・共役・差の計算が自然に現れるため、bridge の target は `ℤ` に置かれている。

この選択により、後続の

$$
4N(m,n)=(2m+n)^2-5n^2
$$

のような差を自然な環演算として扱える。

### 3. reducible な数式名ではなく通常の `def`

`abbrev` ではなく `def` なので、simp が無条件に内部式へ潰す設計ではない。必要な場所で `unfold GoldenNorm` を明示し、抽象名を保つ場所と多項式計算へ降りる場所を分離できる。

## 冗長・重複箇所

定義本体には実質的な冗長性はない。

考えられる重複は、後続の golden-order 実装でもノルム式が別の形で再登場する場合である。ただし、この段階の `GoldenNorm : ℤ → ℤ → ℤ` は「座標二次形式」であり、後続の actual golden integer / order の norm API と役割が異なる可能性が高い。

したがって将来、同じ式が複数箇所に現れたとしても、型・層・目的が違えば意図的な bridge duplication と評価すべきである。

## 最適化候補

### 候補 A — 現行定義を維持

最も明快である。`GN5` と golden arithmetic の間に、数体を導入しない軽量な algebraic interface を置ける。

### 候補 B — 一般二次形式へ抽象化

一般に

$$
Q_{a,b,c}(m,n)=am^2+bmn+cn^2
$$

を定義し、`GoldenNorm` を係数 $(1,1,-1)$ の instance として表すことはできる。

しかし FLT5 proof で必要なのがこの一形式だけなら、抽象化コストの方が大きい。

### 候補 C — golden-order norm と早期統合

後続で algebraic structure が確立されたあと、`GoldenNorm m n` と golden integer norm の一致 theorem を設けることは有益である。

ただしこの module の目的は「number-field identification を必要とせず」bridge を作ることなので、0093 の時点で統合すると依存方向を重くする。

### 候補 D — notation の導入

局所 notation で $N(m,n)$ を短く書く案もあるが、Lean source の grepability と theorem 名の明確さでは `GoldenNorm` の方が優れている。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は全体として `Mathlib` に依存し、manifest 上で `DkMath/FLT/Five/SquareGoldenBridge.lean` が `SignedFiveAdicPowerSplit.lean` の直後に並んでいることを確認した。

本定義単体が必要とするものは整数型と基本環演算、自然数冪だけであり、umbrella `Mathlib` は明らかに過大である。

一方、同じ `SquareGoldenBridge.lean` の直後の theorem 群は `ring`、`push_cast`、`norm_num` を使用している。したがって module 全体としては polynomial normalization と coercion support が必要になる。

最小 import の具体的 module 名は、分割元 `SquareGoldenBridge.lean` の import header をこの回では直接確認できず、Lean build も指示により実行していないため断定しない。最適化するなら、元 module の direct imports を確認し、`ring` / cast tactic に必要な module を一つずつ build で検証するのが安全である。

## Comparator challenge 化の可否

適している。ただし theorem proving というより表現設計の challenge になる。

比較候補は次の通り。

1. 現行の専用 `GoldenNorm` 定義。
2. 一般 binary quadratic form の special case とする方式。
3. golden integer structure を先に導入し、その norm projection として定義する方式。
4. 式を名前付けせず `GN5_eq_goldenNorm_squareLink` 側へ直接展開する方式。

評価軸は依存の軽さ、数学的意味の可視性、後続 golden arithmetic との接続性、`ring` 証明の簡潔さ、namespace pollution、proof graph の監査容易性である。

現行方式は、後続の algebraic-number infrastructure に依存せず、二次形式だけを先に固定できる点で非常に強い。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。そこでは 0092 `branchB_false_of_powerSplitCore` の直後で `SignedFiveAdicPowerSplit.lean` が終了し、`SquareGoldenBridge.lean` が開始して、その最初の宣言として `GoldenNorm` が置かれていることを確認した。

同 source の module comment には、endpoint-square coordinates

$$
m=(g+y)^2+y^2,\qquad n=(g+y)y
$$

によって `GN5 g y` を `m^2 + m*n - n^2` へ書き換え、さらに discriminant-five identity へ進む設計意図が記されている。

既存の日本語・英語 PDF は叙述的背景資料として扱うべきだが、今回 GitHub code search は upstream 502 を返し、PDF の具体的ファイル・ページと本定義の一対一対応を検証できなかった。したがって PDF 固有のページ番号・節番号・引用は推測で補っていない。

## 次に読むべき宣言

source 上で `GoldenNorm` の直後に置かれているのは

```lean
theorem GN5_eq_square_cross_form (g y : ℕ) :
    GN5 g y =
      (g ^ 2) ^ 2 +
        5 * (g ^ 2) * (y * (g + y)) +
        5 * (y * (g + y)) ^ 2 := by
  unfold GN5
  ring
```

である。

この theorem は `GN5` をまず

$$
g^4+5g^2\,y(g+y)+5\bigl(y(g+y)\bigr)^2
$$

という square/cross 二次形式へ変形する。

0093 が target vocabulary `GoldenNorm` を導入する回なら、0094 は自然数上の `GN5` をその座標変換へ乗せる最初の実計算である。
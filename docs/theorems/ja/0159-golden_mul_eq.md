# 0159 — `golden_mul_eq`

## Lean の型

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

これは `theorem` であり、raw operation `goldenMul` と、`Mul GoldenInt` instance を通した標準乗法 `x * y` が定義的に同一であることを公開する `@[simp]` 補題である。

## 数学的主張・宣言の意味

`GoldenInt` を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読む。raw multiplication `goldenMul` は、生成元の関係

$$
\varphi^2=\varphi+1
$$

を座標計算へ組み込んだ

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

という演算である。したがって

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

を表す。

一方、標準記法 `x * y` は既に登録された

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

を通して同じ演算を参照する。本 theorem は新しい乗法則を証明するのではなく、

$$
\texttt{goldenMul x y}=x*y
$$

という raw API と標準 algebra API の一致を simp rule として公開する。

## 証明全体での役割

0155 で `GoldenInt` は `IsDomain` まで Mathlib の algebra hierarchy に入り、0156 以降では raw coordinate API を標準 notation へ正規化する bridge theorem 群が並ぶ。

```lean
@[simp] theorem golden_add_eq ...
@[simp] theorem golden_neg_eq ...
@[simp] theorem golden_sub_eq ...
@[simp] theorem golden_mul_eq ...
@[simp] theorem golden_pow_eq ...
```

0159 はこの block の乗法担当である。

これは下流で特に重要である。後続の `GoldenDivisibility`、`GoldenEuclidean` などでは、raw な `goldenMul` を使って構築された定義と、Mathlib 標準の `*` を使う一般 algebra theorem の間を往復する必要がある。実際、standalone source の後段では `golden_mul_eq` が Euclidean-domain 構築や共役の冪に関する証明の rewrite として使われている。

したがって本 theorem は、黄金整数固有の座標乗法を Mathlib の一般環論へ接続する小さいが load-bearing な API bridge である。

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- `goldenMul`
- `instance : Mul GoldenInt := ⟨goldenMul⟩`
- Lean 標準の `Mul` notation
- `rfl`
- `@[simp]`

概念的な依存関係は

$$
\texttt{GoldenInt}
\longrightarrow
\texttt{goldenMul}
\longrightarrow
\texttt{Mul GoldenInt}
\longrightarrow
\texttt{golden_mul_eq}
$$

である。

なお、0143 `golden_fst_mul` と 0144 `golden_snd_mul` は `x * y` の各座標を公開する projection theorem であり、本 theorem はそれらとは別に「raw 関数名そのもの」と標準 `*` notation の一致を公開する。

## 証明・構築の流れ

証明は `rfl` 一行である。

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

右辺 `x * y` は typeclass resolution により `Mul GoldenInt` instance を参照する。その instance が保持する演算は `goldenMul` なので、右辺を定義展開すると左辺と同一になる。

したがって ring 計算や座標展開は必要なく、両辺は theorem rewrite より前に definitionally equal である。

## Lean 固有の処理

重要なのは typeclass resolution、definitional equality、`@[simp]` の三点である。

`x * y` は `Mul GoldenInt` instance によって elaboration される。登録済み instance が `⟨goldenMul⟩` なので、`goldenMul x y` と `x * y` は定義的に同じ式である。

それでも本 theorem を `@[simp]` として明示することで、simp engine に

```lean
goldenMul x y
```

から

```lean
x * y
```

への正規化方向を与える。これにより raw implementation syntax を標準 algebra notation へ寄せ、下流で `mul_assoc`、`mul_comm`、整除、Euclidean-domain API など Mathlib の一般 theorem を利用しやすくなる。

## 冗長・重複箇所

論理的には本 theorem は冗長である。`Mul` instance を unfold すれば同じ等式は `rfl` で得られる。また 0143–0144 により `x * y` の座標式も既に公開されている。

しかし API 上の役割は異なる。

- 0143–0144 は標準乗法の座標 projection を公開する。
- 0159 は raw operation 名 `goldenMul` を標準 `*` へ正規化する。
- raw layer を監査可能なまま残しつつ、downstream proof surface を標準 notation に統一できる。

このため、数学的重複ではなく interface layering と見るのが自然である。

## 最適化候補

候補は次の通りである。

1. 現行の `@[simp] theorem ... := rfl` を維持する。
2. theorem を削除し、必要箇所で `Mul` instance を unfold する。
3. algebra structure 完成後に `goldenMul` を非公開化し、標準 `*` のみを downstream API にする。
4. 0156–0160 を明示的な raw-to-standard bridge section としてまとめる。
5. `AdjoinRoot` や一般 quadratic algebra を使う実装と、現行の explicit coordinate multiplication を比較する。

FLT5 の監査可能性を重視する現在の設計では、raw operation を残しつつ bridge theorem で標準 notation へ寄せる現行方式がわかりやすい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独では高度な Mathlib theorem を直接使わず、必要なのは `GoldenInt`、`goldenMul`、`Mul GoldenInt` instance、基本 equality machinery、`@[simp]` である。

したがって 0159 単独のために `Mathlib` 全体は不要と考えられる。ただし `GoldenOrder` module 全体では `CommRing`、`IsDomain`、`Zsqrtd`、`ring`、`omega`、`norm_num` などを使用しているため、実際の最小 import は module 全体の依存で決まる。

今回は Lean build を行わないため、細粒度な最小 import 集合は未検証であり、import 最適化候補としての推測に留める。

## Comparator challenge 化の可否

適している。比較対象として次の方式が考えられる。

- explicit `goldenMul` + `Mul` instance + 本 bridge theorem。
- `Mul` instance に座標式を直接 inline する方式。
- raw operation を隠し、標準 `*` のみを公開する方式。
- 一般 quadratic-order / `AdjoinRoot` ベース実装。

比較軸は、`rfl` で閉じる補題数、simp の安定性、downstream proof の長さ、定義変更への耐性、raw coordinate layer の監査可能性、Mathlib 一般環論との相互運用性である。

特に、専用座標実装の definitional transparency と、一般 algebra infrastructure の再利用性との trade-off を測る課題になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` generated section である。source では `golden_add_eq`、`golden_neg_eq`、`golden_sub_eq`、本 theorem、`golden_pow_eq` がこの順で並び、その直後から `goldenPhi`、`goldenConj`、`goldenNorm` など黄金整数固有の数論 API へ進む。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、この小さな API bridge theorem に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

である。

0159 までで加法・否定・減算・乗法の raw API が標準 notation へ接続された。次の 0160 では recursive raw power `goldenPow` と、`CommRing GoldenInt` が提供する標準冪 `x ^ n` の定義的一致を公開し、raw-operation bridge block を閉じる。
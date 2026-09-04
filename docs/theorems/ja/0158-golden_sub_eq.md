# 0158 — `golden_sub_eq`

## Lean の型

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

これは `theorem` であり、raw operation `goldenSub` と、`Sub GoldenInt` instance を通した標準減算 `x - y` が定義的に同一であることを公開する `@[simp]` 補題である。

## 数学的主張・宣言の意味

`GoldenInt` を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読む。上流の raw subtraction は

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

と定義されているので、数学的には

$$
goldenSub(x,y)=x+(-y)=(a-c)+(b-d)\varphi
$$

である。一方、標準記法 `x - y` は既に登録された

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

を通して同じ関数を参照する。

したがって本 theorem は新しい減算法則を証明するものではない。raw API と標準 algebra API の一致

$$
\texttt{goldenSub x y}=x-y
$$

を、名前付きの simp rewrite rule として公開する。

## 証明全体での役割

0155 で `GoldenInt` は `IsDomain` まで Mathlib の標準 algebra hierarchy に入り、0156 以降では raw coordinate API を標準 notation へ正規化する bridge theorem 群が続く。0156 `golden_add_eq` が加法、0157 `golden_neg_eq` が否定を担当し、本 theorem はそれらから構成される減算を担当する。

これにより、bootstrap 段階で明示的に用いた `goldenSub` を監査可能な raw operation として残しつつ、下流の証明では一般的な環・加法群 API の `x - y` に統一できる。

source 上では

```lean
@[simp] theorem golden_add_eq ...
@[simp] theorem golden_neg_eq ...
@[simp] theorem golden_sub_eq ...
@[simp] theorem golden_mul_eq ...
@[simp] theorem golden_pow_eq ...
```

と連続しており、本 theorem は raw-operation bridge block の減算担当である。

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- `goldenAdd`
- `goldenNeg`
- `goldenSub`
- `instance : Sub GoldenInt := ⟨goldenSub⟩`
- Lean 標準の `Sub` notation
- 反射律 `rfl`

概念的な依存関係は

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}
\longrightarrow
\texttt{golden_sub_eq}
$$

である。

0156 `golden_add_eq` と 0157 `golden_neg_eq` は意味上は近いが、本 theorem の proof term 自体はそれらを rewrite に使わない。`Sub` instance が `goldenSub` を直接保持しているため `rfl` だけで閉じる。

## 証明・構築の流れ

証明は一段で終わる。

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

Lean は右辺 `x - y` を `Sub GoldenInt` instance により elaboration する。その instance の演算が `goldenSub` なので、右辺を定義展開すると左辺と同じ `goldenSub x y` になる。

したがって theorem rewrite や環計算を使う前に両辺は definitionally equal であり、`rfl` が成立する。

概念的には

$$
\text{raw subtraction}
\longrightarrow
\text{standard subtraction notation}
$$

という API 正規化である。

## Lean 固有の処理

重要なのは typeclass resolution、definitional equality、`@[simp]` の三点である。

`x - y` は単なる表示上の記号ではなく、型 `GoldenInt` に対する `Sub` instance を探索して解釈される。登録済み instance が `⟨goldenSub⟩` なので、`goldenSub x y` と `x - y` は theorem を使わなくても定義的に一致する。

それでも `@[simp]` theorem を置くことで、simp engine に

```lean
goldenSub x y
```

から

```lean
x - y
```

への正規化方向を明示できる。これは raw implementation syntax を Mathlib の標準 algebra notation へ寄せる 0156–0160 の設計方針と一致する。

また `goldenSub` 自体が `goldenAdd x (goldenNeg y)` として定義されているので、必要ならさらに加法と否定へ unfold できる一方、通常の downstream proof ではこの bridge によりその内部構造を意識せず標準減算を使える。

## 冗長・重複箇所

論理的情報だけを見れば、本 theorem は instance を unfold すれば `rfl` で得られるため冗長である。また 0156 と 0157 が既に raw 加法・否定を標準 notation へ接続しているので、`goldenSub = goldenAdd + goldenNeg` を展開して同じ意味を再構成することもできる。

しかし API 設計としては独立した bridge theorem を置く利点がある。

- `goldenSub` という raw operation 名を監査可能な形で残せる。
- downstream の simp 正規形を `x - y` 側へ統一できる。
- 利用側が `Sub` instance や `goldenSub` の内部定義を unfold する必要を減らせる。
- 0156–0160 の加法・否定・減算・乗法・冪に一貫した bridge API を与えられる。

したがって「数学的には自明だが、interface theorem として有用」という位置づけである。

## 最適化候補

候補は次の通りである。

1. 現行どおり `@[simp] theorem ... := rfl` を維持する。
2. theorem を削除し、必要箇所で `goldenSub` または `Sub` instance を unfold する。
3. `goldenSub` を構造完成後に非公開化し、下流では `x - y` だけを公開 API とする。
4. `golden_add_eq` から `golden_pow_eq` までを明示的な API bridge section としてまとめ、正規化方向を source comment で固定する。
5. `goldenSub` 自体を標準記法 `x + (-y)` から定義する設計と、現行の raw-operation-first 設計を比較する。

この formalization は raw coordinate layer の可視性を重視しているため、1 または 4 が自然である。数行の削減より、bootstrap layer と標準 algebra layer の境界を読み取りやすくする価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として `import Mathlib` を利用している。本 theorem 単独では高度な Mathlib theorem を直接使用せず、必要なのは `GoldenInt`、`goldenSub`、`Sub GoldenInt` instance、標準 equality machinery、`@[simp]` 属性である。

したがって 0158 のためだけに `Mathlib` 全体を import する必要はないと考えられる。ただし `GoldenOrder` module 全体では `CommRing`、`IsDomain`、`Zsqrtd`、`ring`、`omega`、`norm_num` なども利用しているため、実際の最小 import は module 全体の依存で決まる。

今回は Lean build を行わないため、より細粒度な最小 import 集合は未検証であり、ここは import 最適化候補としての推測である。

## Comparator challenge 化の可否

適している。数学的な難易度ではなく、Lean API normalization strategy を比較する課題になる。

比較対象として、次の方式を用意できる。

- 現行の `@[simp]` bridge theorem を維持する方式。
- raw definition / instance を必要箇所で unfold する方式。
- raw subtraction を隠して標準 `x - y` のみを公開する方式。
- `goldenSub := goldenAdd x (goldenNeg y)` と raw subtraction を直接座標差で定義する方式。

比較軸は、simp の安定性、downstream proof の長さ、定義変更への耐性、error message に raw implementation が漏れる頻度、座標層の監査可能性、標準 algebra theorem との相互運用性である。

特に `rfl` で証明できる API theorem を明示的に残す価値と、subtraction を derived operation としてどこまで表面化するかを測れる小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` generated section である。そこで `goldenSub` は `goldenAdd x (goldenNeg y)` と定義され、`Sub GoldenInt` instance は `⟨goldenSub⟩` を登録し、`golden_add_eq`、`golden_neg_eq`、本 theorem、`golden_mul_eq`、`golden_pow_eq` がこの順で並んでいる。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、この小さな API bridge theorem に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

である。

0158 までで加法・否定・減算の raw API が標準 notation へ接続された。次の 0159 では、`\varphi^2=\varphi+1` の還元を組み込んだ raw multiplication `goldenMul` と標準乗法 `x * y` の定義的一致を同じ方針で公開する。
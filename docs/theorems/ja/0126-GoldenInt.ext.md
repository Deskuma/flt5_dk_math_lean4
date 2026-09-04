# 0126 — `GoldenInt.ext`

## Lean の型

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all
```

`GoldenInt.ext` は、二つの `GoldenInt` が `fst` と `snd` の両座標で一致すれば、構造体そのものとして等しいことを与える外延性定理である。

## 数学的主張

`GoldenInt` は整数対

$$
x=a+b\varphi
$$

を `fst = a`、`snd = b` として表す。したがって

$$
a=c
$$

かつ

$$
b=d
$$

ならば

$$
a+b\varphi=c+d\varphi
$$

である、という座標表示の一意性を Lean の構造体 equality として表したものが本定理である。

ただし、この時点で必要なのは $1,\varphi$ の線形独立性を別途証明することではない。`GoldenInt` 自体が二つの整数 field からなる構造体として定義されているため、二座標の一致から構造体 equality が従う。

## 証明全体での役割

0125 `goldenPow` までで `GoldenInt` の carrier と raw arithmetic が揃った。本定理からは、それらの演算についての equality を「二つの整数座標の equality」に落として証明する段階へ入る。

後続では `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` の instance が登録され、さらに加法群・環法則、整数埋め込み、共役、ノルムなどの equality proof が続く。`@[ext]` が付いているため、`ext` tactic は `GoldenInt` の equality goal を `fst` と `snd` の二つの goal に分解できる。

したがって本定理は、黄金整数環の代数法則を座標計算へ還元するための proof interface である。

## 直接依存する定義・補題

直接依存する数学的宣言は `GoldenInt` だけである。

証明中では Lean の構造体場合分けと simplifier を使う。

1. `GoldenInt`
2. `cases`
3. `simp_all`
4. `@[ext]` 属性

0120–0125 の `goldenOne`、`goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` には直接依存しない。依存順としてそれらの後ろに置かれているが、本 theorem の論理内容は carrier `GoldenInt` の structure だけから成立する。

## 証明の流れ

証明は三段階である。

1. `cases x` により `x` を二つの整数 field へ展開する。
2. `cases y` により `y` も同様に展開する。
3. `simp_all` が `hfst` と `hsnd` を使い、残った structure equality を閉じる。

概念的には、structure constructor の単射性を使って

$$
(x.fst=x'.fst)\land(x.snd=x'.snd)\Longrightarrow x=x'
$$

を示しているだけである。

## Lean 固有の処理

### 1. `@[ext]` 属性

`@[ext]` は本 theorem を extensionality theorem として登録する。これにより、後続で

```lean
ext <;> simp [goldenAdd, goldenMul]
```

のような証明スタイルを採用できる。

つまり本 theorem は単なる補題ではなく、`ext` tactic が利用する型固有の equality decomposition rule でもある。

### 2. structure の `cases`

`cases x` と `cases y` により、抽象的な `GoldenInt` を constructor 形へ戻す。`GoldenInt` は field が二つしかないため、場合分けによる分岐は発生せず、座標だけが局所 context に露出する。

### 3. `simp_all`

`hfst` と `hsnd` は structure を分解した後、整数 equality に変換される。`simp_all` は context 中の等式を使って goal と仮定を同時に簡約し、最終的な reflexive equality を閉じる。

この proof は代数 tactic を全く使わない。`ring`、`omega`、`norm_num`、cast 処理は不要である。

### 4. implicit arguments

`x y` は `{x y : GoldenInt}` と implicit binder になっている。そのため通常の利用では対象は equality hypotheses から推論され、明示的に渡す必要がない。

## 冗長・重複箇所

Lean は structure に対して extensionality theorem を自動生成・導出できる場合があり、`GoldenInt.ext` の内容自体は非常に標準的である。

また proof script

```lean
cases x
cases y
simp_all
```

は、より直接的な constructor injectivity や `cases hfst; cases hsnd; rfl` に置換できる可能性がある。

しかし明示的に `GoldenInt.ext` を置き `@[ext]` 登録することには、後続証明の API を安定させる利点がある。`GoldenInt` の内部表現を読まずとも `ext` を利用できるため、単なる重複とは言い切れない。

## 最適化候補

### 候補 A — 現状維持

最も読みやすい。二 field structure の extensionality を明示し、後続の `ext` tactic 利用を保証する。

### 候補 B — generated ext theorem を利用

Lean / Mathlib が生成可能な extensionality rule に委ね、手書き theorem を削減する案である。

利点は boilerplate 削減、欠点は生成名・属性登録・将来の structure 変更時の挙動が手書き API より見えにくくなる点である。

### 候補 C — proof を `cases hfst; cases hsnd; rfl` 型へ寄せる

`simp_all` への依存を減らし、kernel reduction に近い proof にできる可能性がある。ただし実際の最短形は Lean build で検証していない。

### 候補 D — `ext` を早期の共通 proof style として徹底する

後続の環法則をすべて

```lean
apply GoldenInt.ext <;> simp [goldenAdd, goldenMul, goldenNeg]
```

のような座標 proof に統一する案である。証明の均質性は増すが、展開量が多い theorem では `ring` と組み合わせた方が読みやすい場合もある。

## 必要 Mathlib import と import 最適化候補

対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本 theorem 単独の数学的依存は `GoldenInt` の structure equality だけである。一方、実装では `@[ext]` 属性と `simp_all` tactic を使うため、それらを供給する Lean / Mathlib 側の import が必要になる。

最小化候補としては `ext` infrastructure と基本 tactic のみを import する構成が考えられるが、具体的な最小 module 名はこの回では Lean build を行っていないため未検証である。したがって `Mathlib` 全体が必要とは断定せず、逆に特定の細分化 import だけで十分とも断定しない。

## Comparator challenge 化の可否

 **適している。** 題材は小さいが、Lean における structure equality の複数の証明様式を比較する良い challenge になる。

比較候補は次の通りである。

1. 現行の `cases` + `simp_all`
2. constructor injectivity / equality elimination
3. generated extensionality theorem
4. `rfl` に近い明示的 field rewriting

評価軸は proof term の単純さ、`simp` 依存度、structure field 追加時の保守性、`@[ext]` API としての再利用性、後続 algebra proofs との統一感である。

## 既存資料との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。

この回では PDF 本文中の `GoldenInt.ext` に対応する具体的なページ・節を直接解析していないため、ページ番号や PDF 固有の説明は推測しない。

形式的内容の最終根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とする。

## 次に読むべき宣言

本 theorem の直後では typeclass instance の登録が始まる。

最初は

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

である。

0126 までで raw carrier / raw arithmetic / equality interface が揃った。次は raw definition `goldenZero` を標準 `Zero GoldenInt` API に接続する段階へ進む。
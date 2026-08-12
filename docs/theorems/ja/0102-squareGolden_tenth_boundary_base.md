# 0102 — `squareGolden_tenth_boundary_base`

## Lean の型

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

## 数学的主張

0100 `SquareGoldenM` と 0101 `SquareGoldenN` を

$$
M=z^2+y^2,\qquad N=zy
$$

と書けば、本定理は

$$
M-2N=(z-y)^2
$$

を主張する。

定義を展開すれば

$$
z^2+y^2-2zy=(z-y)^2
$$

という平方完成そのものである。

この等式の重要点は、square/golden 座標 $(M,N)$ の線形結合 $M-2N$ が常に完全平方になることにある。したがって $(M,N)$ は黄金ノルム側の情報だけでなく、元の endpoint 差 $z-y$ の平方情報も保持している。

## 証明全体での役割

`SquareGoldenNormalForm.lean` は Branch-B の fifth-power normal form を、平方世界と黄金ノルム世界の情報を同時に保持する packet へ持ち上げる。その最初の保存則が本定理である。

後続 `exists_branchB_squareGoldenNormalForm` では fifth-power normal form の

$$
z=y+a^5
$$

を整数へ cast し、本定理と組み合わせて

$$
M-2N=(z-y)^2=(a^5)^2=a^{10}
$$

を得る。Lean source でも `squareGolden_tenth_boundary_base z y` が `tenth_boundary` フィールドの証明に直接使われている。

つまり本定理は

$$
\text{endpoint difference}
\longrightarrow
\text{square boundary}
\longrightarrow
\text{tenth-power boundary}
$$

という橋の第一段である。

0098 `endpoint_square_discriminant` が

$$
M^2-4N^2=(z^2-y^2)^2
$$

という二次の判別式を保持するのに対し、本定理はより低次数の線形 combination

$$
M-2N=(z-y)^2
$$

を保持する。後続 packet はこの二種類の平方情報を両方保存する。

## 直接依存する定義・補題

project-local な直接依存は二つである。

1. 0100 `SquareGoldenM`
2. 0101 `SquareGoldenN`

それぞれ

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2

def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

である。

証明 tactic としては `ring` を用いる。別の project-local theorem は呼び出していない。

## 証明の流れ

証明は二段だけである。

### 1. 座標定義を展開する

```lean
unfold SquareGoldenM SquareGoldenN
```

によって goal は概ね

```lean
(z : ℤ) ^ 2 + (y : ℤ) ^ 2 - 2 * ((z : ℤ) * (y : ℤ)) =
  ((z : ℤ) - (y : ℤ)) ^ 2
```

となる。

### 2. 多項式恒等式として正規化する

```lean
ring
```

で両辺を整数環上の標準多項式形へ正規化し、恒等式を閉じる。

数学的には平方完成であり、Lean では `ring` が展開・結合・係数整理を一括して担当する。

## Lean 固有の処理

### 1. `ℕ` 入力を `ℤ` 座標へ持ち上げ済み

`SquareGoldenM` と `SquareGoldenN` の戻り値が最初から `ℤ` なので、本定理では `Nat.sub` の切り捨てを避けつつ

```lean
(z : ℤ) - (y : ℤ)
```

をそのまま扱える。

もし右辺が `((z - y : ℕ) : ℤ)^2` なら $y\le z$ の条件が必要になるが、整数差を採用しているため恒等式は無条件で成立する。

### 2. cast 正規化 tactic が不要

本 theorem 内では座標定義を unfold した時点で全項がすでに `ℤ` にいるため、`push_cast` や `norm_cast` は不要である。

### 3. `ring` が subtraction を含む式を処理する

整数環は subtraction を持つため、`ring` は

$$
(z-y)^2=z^2-2zy+y^2
$$

を通常の環恒等式として処理できる。ここでも `Nat` の順序条件は必要ない。

## 冗長・重複箇所

数学的内容は古典恒等式

$$
a^2+b^2-2ab=(a-b)^2
$$

の特殊例であり、一般補題があればそれを `simpa` で適用できる。

また 0098 `endpoint_square_discriminant` は

$$
(z^2+y^2)^2-4(z y)^2=(z^2-y^2)^2
$$

を証明しており、同じ endpoint-square 座標の別の完全平方化である。二定理は計算上近いが、保持する invariant が異なるため役割上は重複していない。

さらに後続 `exists_branchB_squareGoldenNormalForm` では本定理の結果を一度使ったあと `z-y=a^5` を代入して $a^{10}$ へ変換する。これを一つの theorem にまとめることも可能だが、現在の分割は「純粋な座標恒等式」と「FLT5 provenance」を明確に分離しており、監査性が高い。

## 最適化候補

### 候補 A — 一般平方完成補題へ抽象化する

例えば整数一般に

```lean
theorem sq_add_sq_sub_two_mul_eq_sq_sub (a b : ℤ) :
    a ^ 2 + b ^ 2 - 2 * (a * b) = (a - b) ^ 2 := by
  ring
```

を用意し、本 theorem を `simpa [SquareGoldenM, SquareGoldenN]` で導く設計が考えられる。

ただし本 theorem は十分短く、一般補題を追加すると declaration 数が増えるため、再利用先がなければ過剰抽象化になりうる。

### 候補 B — `ring_nf` との比較

`unfold ...; ring` は意図が明快である。`ring_nf` で goal と hypotheses を正規化する方式も考えられるが、本 theorem では `ring` のほうが「恒等式を閉じる」意図が直接的である。

### 候補 C — 現状維持

二座標 API の最初の theorem として、座標を unfold し一行の `ring` で閉じる現在形は非常に監査しやすい。証明短縮の余地はほぼない。

## 必要 Mathlib import と import 最適化候補

standalone artifact 全体は

```lean
import Mathlib
```

を使用している。

本 theorem 単独で必要なのは、おおむね次の要素である。

1. `ℕ`、`ℤ` と coercion。
2. `SquareGoldenM` / `SquareGoldenN` の定義。
3. `ring` tactic。

したがって本 theorem の tactic 依存として中心になるのは `Mathlib.Tactic.Ring` 系であると考えられる。ただし実際の `SquareGoldenNormalForm.lean` module は後続で `exact_mod_cast` と project-local FLT5 theorem 群も使用するため、module 全体の最小 import 集合は Lean build なしには断定しない。

import 最適化を行うなら、umbrella `Mathlib` を一気に外すのではなく、project-local import と tactic import を分離しながら段階的に build 検証するのが安全である。本回では Lean build は行っていない。

## Comparator challenge 化の可否

適している。小さく閉じた多項式恒等式なので、proof style 比較がしやすい。

比較候補は例えば次である。

1. 現行の `unfold ...; ring`。
2. 一般平方完成 lemma を先に証明して `simpa`。
3. `ring_nf` を使う方式。
4. `nlinarith` で閉じる方式が成立するかを比較する。

評価軸は proof term の単純さ、読みやすさ、replay 安定性、import の軽さ、一般化可能性である。

Comparator challenge としては、「最短」だけでなく、座標定義を保持したまま theorem の数学的意味が最も読みやすい proof を比較対象にするとよい。

## 次に読むべき定理

Lean source で直後に置かれているのは

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

である。

本 theorem が

$$
M-2N=(z-y)^2
$$

という一次 combination の平方境界を保存するのに対し、次 theorem は

$$
M^2-4N^2=(z^2-y^2)^2
$$

という独立な square discriminant を保存する。

したがって次号は `squareGolden_square_discriminant` を読むのが依存順として自然である。

## 根拠と注記

形式的根拠は `docs/flt5-theorem-museum` ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` に含まれる `SquareGoldenNormalForm.lean` 区間である。そこでは本 theorem が `SquareGoldenM`、`SquareGoldenN` の直後にあり、後続 `exists_branchB_squareGoldenNormalForm` の `tenth_boundary` 構築で直接利用されている。

既存日本語・英語 PDF の本 theorem に対する具体的なページ対応は本回では確認できなかった。GitHub code search も upstream error となったため、PDF の節番号・ページ番号・叙述対応を推測で補ってはいない。

また standalone が記録する split source 名は `DkMath/FLT/Five/SquareGoldenNormalForm.lean` であるが、本記事の一次的な形式根拠は対象ブランチ上で取得できた generated standalone の現在内容としている。
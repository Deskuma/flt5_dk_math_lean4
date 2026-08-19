# 0157 — `golden_neg_eq`

## Lean の型

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

これは `theorem` であり、raw operation `goldenNeg` と、`Neg GoldenInt` instance を通した標準単項マイナス `-x` が定義的に同一であることを公開する `@[simp]` 補題である。

## 数学的主張・宣言の意味

`GoldenInt` を

$$
x=a+b\varphi
$$

と読むと、上流の `goldenNeg` は座標ごとの加法逆元

$$
goldenNeg(x)=(-a)+(-b)\varphi
$$

を実装する。一方、標準記法 `-x` も既に登録された

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

を通して同じ関数を参照する。

したがって本 theorem は新しい代数法則を証明するものではない。raw API と標準 algebra API の一致

$$
\texttt{goldenNeg x}=-x
$$

を、名前付きの simp rewrite rule として公開する宣言である。

## 証明全体での役割

0155 で `GoldenInt` は `IsDomain` まで Mathlib の標準 algebra hierarchy に入り、0156 から raw coordinate API と標準 notation の境界を整理する equivalence 群に入った。本 theorem は 0156 `golden_add_eq` に続く第二項で、raw negation を標準の `Neg.neg` notation へ正規化する。

この橋があることで、初期構築で明示的に用いた `goldenNeg` を残したまま、下流の証明では `-x` を中心とする一般的な加法群・環 API に寄せられる。特に `goldenSub` が `goldenAdd x (goldenNeg y)` として定義されているため、次の `golden_sub_eq` へ自然に接続する。

source 上では `golden_add_eq`、`golden_neg_eq`、`golden_sub_eq`、`golden_mul_eq`、`golden_pow_eq` が連続しており、本 theorem はその raw-operation bridge block の否定担当である。

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- Lean 標準の `Neg` notation
- 反射律 `rfl`

`goldenNeg` 自体は `GoldenInt` の二座標をそれぞれ整数上で否定する raw definition である。本 theorem の proof term は `rfl` だけであり、`neg_add_cancel` や `add_left_neg` などの加法群 theorem は直接必要としない。

## 証明・構築の流れ

証明は一段で閉じる。

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

Lean は右辺 `-x` を `Neg GoldenInt` instance によって解釈する。その instance が保持する演算は `goldenNeg` なので、右辺を定義展開すると左辺と同じ `goldenNeg x` になる。したがって定義的等価性だけで `rfl` が成立する。

概念的には

$$
\text{raw coordinate negation}
\longrightarrow
\text{standard unary minus}
$$

という API 正規化である。

## Lean 固有の処理

重要なのは typeclass resolution、definitional equality、`@[simp]` の三者である。

`-x` は単なる構文糖ではなく、型 `GoldenInt` に対する `Neg` instance の探索を経て elaboration される。登録済み instance が `⟨goldenNeg⟩` なので、`goldenNeg x` と `-x` は theorem rewrite を使う前から definitionally equal である。

それでも `@[simp]` theorem を置くことで、simp engine に

```lean
goldenNeg x
```

から

```lean
-x
```

への明示的な正規化方向を与えられる。raw implementation syntax を標準 algebra notation へ寄せるという 0156 と同じ方針である。

## 冗長・重複箇所

論理的情報だけを見れば、本 theorem は instance を unfold すれば `rfl` で得られるため冗長である。しかし API 設計としては有用である。

- raw operation 名を監査可能な形で残せる。
- downstream の simp 正規形を標準 notation 側へ統一できる。
- 利用側が `Neg` instance の内部実装を直接 unfold する必要を減らせる。
- 0156–0160 の bridge theorem 群に一貫した API を与えられる。

したがって「数学的には自明、interface としては意味がある」タイプの theorem である。

## 最適化候補

候補は次の通りである。

1. 現行どおり `@[simp] theorem ... := rfl` を維持する。
2. theorem を削除し、必要箇所で `goldenNeg` または `Neg` instance を unfold する。
3. algebra structure 完成後に raw operation を非公開化し、標準 notation だけを公開 API とする。
4. `golden_add_eq` から `golden_pow_eq` までを明示的な API bridge section としてまとめ、設計意図を source comment で固定する。

この formalization は raw coordinate layer の可視性を重視しているため、1 または 4 が最も自然である。数行の削減より、bootstrap layer と標準 algebra layer の境界を読み取れることの方が監査上の価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として `import Mathlib` を利用している。本 theorem 単独で高度な Mathlib lemma は使わず、直接必要なのは `GoldenInt`、`goldenNeg`、`Neg GoldenInt` instance、標準 equality machinery、`@[simp]` 属性である。

したがって 0157 のためだけに `Mathlib` 全体が必要とは考えにくい。ただし実際の `GoldenOrder` module は `CommRing` 構築、`ring`、`omega`、`norm_num`、`Zsqrtd` などを同一 module 内で利用するため、正確な最小 import は module 全体の依存で決まる。

今回は Lean build を行わないため、粒度を下げた最小 import 集合は未検証であり、ここは import 最適化候補としての推測である。

## Comparator challenge 化の可否

適している。数学内容ではなく、Lean API normalization strategy の比較課題になる。

比較対象として、現行の `@[simp]` bridge theorem、毎回 raw definition / instance を unfold する方式、raw API を構造完成後に隠して標準 notation のみにする方式を用意できる。

比較軸は、simp の安定性、downstream proof の短さ、定義変更への耐性、error message に raw implementation が漏れる頻度、座標層の監査可能性、標準 algebra theorem との相互運用性である。

特に「`rfl` で証明できる theorem を API として残す価値」を小さな実験で測れるため、Comparator challenge として明瞭である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` generated section と、直前の 0156 文書が示す source dependency order である。0156 の source 読取結果では、本 theorem の後に `golden_sub_eq`、`golden_mul_eq`、`golden_pow_eq` が続くことが確認されている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、この小さな API bridge theorem に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_sub_eq (x y : GoldenInt) :
    goldenSub x y = x - y := rfl
```

である。

0156 が加法、0157 が否定を raw API から標準 notation へ接続したので、次の 0158 ではそれらを組み合わせて定義された raw subtraction `goldenSub` と標準減算 `x - y` の一致を同じ方針で公開する。
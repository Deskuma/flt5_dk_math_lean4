# 0421 `fermatFive_no_positive_solution`

## 宣言種別

`theorem`

## Lean の型

```lean
/--
Ordinary-argument wrapper around `flt5Target`: for positive natural numbers
`x`, `y`, and `z`, it proves the negation of `Fermat5Equation x y z`, i.e.
`x^5 + y^5 = z^5`. It does not expose a general-exponent theorem or a theorem
about arbitrary signed integers.
-/
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz
```

## 数学的主張・宣言の意味

この theorem は、指数 5 の Fermat 方程式に対する無条件結果を、利用者が最も直接適用しやすい通常引数形式で公開する。

結論の `Fermat5Equation x y z` は

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

を表すので、型全体は数学的には

$$
\forall x,y,z\in\mathbb N,
\qquad
x>0\to y>0\to z>0\to x^5+y^5\ne z^5
$$

である。

0420 `flt5Target` が

```lean
FLT5Target
```

という一つの proposition 全体の proof を返していたのに対し、0421 は `x`, `y`, `z` と三つの正値仮定を明示的な引数として取り、その場で

```lean
¬ Fermat5Equation x y z
```

を返す。

数学的内容は 0420 と同じであり、新たな数論的補題を追加するものではない。役割は **無条件 closure を外部利用向け API へ展開すること** にある。

正本の docstring が明示する通り、対象は正の自然数と指数 5 に限定される。一般指数版の Fermat 最終定理や任意の符号付き整数に対する theorem を主張するものではない。

## 証明全体での役割

0421 は FLT5 証明の public wrapper である。

0420 までで、証明依存鎖は

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

を無条件に閉じ、最終的に

```lean
flt5Target : FLT5Target
```

が得られている。

0417 `FLT5Target` の定義は

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

なので、`flt5Target` は実際には六つの引数

```lean
x y z hx hy hz
```

を順に適用できる関数型 proof term として扱える。

0421 はその適用を名前付き theorem にしただけである。

従って証明アーキテクチャ上では、

1. 0417 が最終仕様を定義する。
2. 0418–0419 が条件付き endpoint を公開する。
3. 0420 が最後の仮定を discharge して無条件 endpoint を得る。
4. 0421 がその endpoint を通常引数 theorem に展開する。

という最終公開層の一番外側に位置する。

## 直接依存する定義・補題

### `Fermat5Equation`

0001 で定義された中心的 proposition である。

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

0421 の結論

```lean
¬ Fermat5Equation x y z
```

は、まさにこの方程式の否定である。

### `FLT5Target`

0417 の `abbrev : Prop` である。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

0421 の引数列と結論は、この定義を外側から一段ずつ適用したものと完全に一致する。

### `flt5Target`

0420 の無条件 theorem である。

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

0421 の証明本体が直接使用する唯一の theorem はこれである。

## 証明または構築の流れ

証明本体は一行だけである。

```lean
flt5Target x y z hx hy hz
```

### 1. `flt5Target` を取得する

0420 より

```lean
flt5Target : FLT5Target
```

がある。

### 2. `FLT5Target` を関数型として展開する

`FLT5Target` は `abbrev` であり、その本体は

```lean
∀ x y z : ℕ,
  0 < x →
  0 < y →
  0 < z →
  ¬ Fermat5Equation x y z
```

である。

従って Lean は `flt5Target` を、まず `x`, `y`, `z` を受け取り、その後 `hx`, `hy`, `hz` を受け取る proof-producing function として適用できる。

### 3. 個別の否定命題を得る

六つの引数を順に適用すると

```lean
¬ Fermat5Equation x y z
```

が得られ、それがそのまま 0421 の結論になる。

追加の rewrite、case split、算術 tactic、降下議論は一切不要である。

## Lean 固有の処理

### `abbrev` の definitional transparency

ここで最も重要な Lean 固有の点は、`FLT5Target` が `def` ではなく `abbrev` で定義されていることである。

Lean は必要に応じて

```lean
flt5Target : FLT5Target
```

を、その定義本体である

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

として透明に扱える。

そのため

```lean
flt5Target x y z hx hy hz
```

という直接適用が成立する。

### Curry–Howard 対応

全称量化と implication は Lean では関数型として実現される。

したがって

```lean
∀ x : ℕ, P x
```

の proof は `x` を受け取って `P x` の proof を返す関数であり、

```lean
A → B
```

の proof は `A` の proof を受け取って `B` の proof を返す関数である。

0421 はこの仕組みをそのまま利用している。

### term-style proof

証明は tactic block を持たず、

```lean
:=
  flt5Target x y z hx hy hz
```

という term-style で完結する。

この形は依存が完全に解決された公開 wrapper として非常に読みやすい。

## 冗長・重複箇所

数学的には 0421 は 0420 と同値な内容を別の API 形状で公開しているので、情報量だけを見れば重複である。

例えば利用者は 0421 が無くても

```lean
exact flt5Target x y z hx hy hz
```

と直接書ける。

しかし public API としては、

```lean
fermatFive_no_positive_solution
```

という名前だけを見て定理の用途が明確であり、`FLT5Target` という内部的な仕様 alias を知らなくても利用できる利点がある。

また theorem statement 自体に `x y z` と positivity hypotheses が露出するため、検索性、補完候補、教材性も高い。

従ってこの重複は実装上の無駄というより **API facade として意図的な重複** と評価できる。

## 最適化候補

### 1. wrapper の削除

コード量だけを最小化するなら 0421 は削除できる。

利用者が常に

```lean
flt5Target x y z hx hy hz
```

を使えば数学的には十分である。

ただし公開 theorem 名の分かりやすさが失われるので、API 設計としては現行の wrapper を残す方が妥当である。

### 2. `simpa` や `exact` の追加は不要

例えば

```lean
by
  exact flt5Target x y z hx hy hz
```

とも書けるが、現行の term-style の方が短く直接的である。

また `simpa [FLT5Target] using ...` のような明示的 unfold も不要である。`abbrev` の透明性に任せる現在の実装が最も簡潔である。

### 3. 命名面

`fermatFive_no_positive_solution` は対象を自然言語に近い形で表しており、公開名として十分明確である。`FLT5Target` と役割を分離する現行命名に大きな改善余地は見当たらない。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし 0421 自身が直接利用する Lean 機能は theorem application と自然数の型・順序だけであり、特殊な tactic や Mathlib API を本体で直接呼んでいない。

実質的には、次の宣言が環境中にあれば theorem 本体は成立する。

- `Fermat5Equation`
- `FLT5Target`
- `flt5Target`

分割ソースではこれらを提供する FLT5 modules の import 推移閉包が必要になる。

### import 最適化候補

0421 単独のために `Mathlib` 全体を直接 import する必要性は低い。`Main.lean` が依存する FLT5 modules と、それらが必要とする Mathlib の推移依存だけで十分である可能性が高い。

ただし今回は Lean build を実施しておらず、最小 import closure を実測していない。従って具体的な Mathlib module 名の最小集合は未確認であり、推測として断定しない。

## Comparator challenge 化の可否

 **適しているが、単体では非常に低難度である。**

例えば challenge を

```lean
theorem challenge
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z := by
  ?_
```

とし、

```lean
flt5Target : FLT5Target
```

を利用可能にすれば、solver が `FLT5Target` の `abbrev` を透過的に展開し、六引数を適用できるかを検査できる。

これは数学探索 challenge というより、

- `abbrev` の unfold
- dependent function application
- proposition-as-function の認識
- public endpoint の利用

を確認する Lean API challenge である。

難度を上げるなら `flt5Target` を隠し、0419 `flt5Target_of_zeroArithmetic` と `goldenZeroSectorArithmeticExclusion` からまず `FLT5Target` を組み立て、その後に個別 `x y z` へ適用させる形にできる。

さらに 0418 まで戻せば unit-class provider も解決させる多段 dependency challenge にできる。

## 次に読むべき宣言

次は 0422 `signedGoldenFiniteUnitSectorCore`、種別は `theorem` である。

```lean
/-- Every stripped golden packet is unconditionally reduced to the five sectors. -/
theorem signedGoldenFiniteUnitSectorCore : SignedGoldenFiniteUnitSectorCore :=
  signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

0421 で FLT5 の最終公開 theorem wrapper は完成するが、`Main.lean` にはその後も内部構造を外部へ公開する facade theorem が続く。

0422 は `GoldenUnitClassesModFifth` の既証明 provider `goldenUnitClassesModFifth` を `signedGoldenFiniteUnitSectorCore_of_unitClasses` に適用し、stripped golden packet を五つの unit sector のいずれかへ無条件に分類する core proposition を公開する。

従って 0421 は FLT5 statement の public endpoint として一区切りであるが、依存順の宣言解説としてはまだ後続が存在する。
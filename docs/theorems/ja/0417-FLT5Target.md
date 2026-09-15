# 0417 `FLT5Target`

## 宣言種別

`abbrev`

## Lean の型

```lean
/-- No positive natural numbers satisfy `x^5 + y^5 = z^5`. -/
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

## 数学的主張・宣言の意味

`FLT5Target` は theorem ではなく、指数 5 の Fermat 方程式に正の自然数解が存在しないという最終命題を名前付きで固定する `abbrev` である。

`Fermat5Equation` は

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

なので、`FLT5Target` を数学的に展開すると

$$
\forall x,y,z\in\mathbb N,
\quad
x>0\to y>0\to z>0\to
x^5+y^5\ne z^5
$$

である。したがって通常の数学記法では

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5
$$

という指数 5 に限定した Fermat の最終定理そのものを表す。

重要なのは、この宣言自身はその命題を証明していないことである。`abbrev FLT5Target : Prop := ...` は「最終的に何を証明すればよいか」という target proposition に公開名を付けているだけであり、その inhabitant は後続の `flt5Target` で構築される。

また対象は正の自然数に限定されている。一般指数の FLT、任意の整数符号を含む方程式、あるいは一般環上の主張ではない。

## 証明全体での役割

`FLT5Target` は `Main.lean` の公開 endpoint 層の入口である。

直前までの証明では、内部 closure 型として

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

が使われていた。0417 `FLT5Target` はこれと論理的に同一の shape を、最終公開 API 用の名前で再び提示する。

その後の流れは次のようになっている。

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

まず unit-class classification と zero-sector arithmetic exclusion を仮定した conditional receiver が `FLT5Target` を供給する。

次に

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

で既証明の unit classification を埋め込み、最後に

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

で zero-sector arithmetic exclusion も実際の証明で満たす。

したがって証明全体の終端構造は

$$
\text{golden unit classification}
+
\text{zero-sector exclusion}
\Longrightarrow
\text{PositiveFermat5Refuter}
\Longrightarrow
\text{FLT5Target}
$$

と読める。

0417 はこの最終段に置かれた **公開 target interface** である。

## 直接依存する定義・補題

### `Fermat5Equation`

この宣言が直接参照する DkMath 固有定義は `Fermat5Equation` である。

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

従って

```lean
¬ Fermat5Equation x y z
```

は定義展開すれば

$$
x^5+y^5\ne z^5
$$

である。

### 正値条件

```lean
0 < x →
0 < y →
0 < z →
```

は `Fermat5Equation` の内部ではなく target 側に置かれている。

これは `Fermat5Equation` を純粋な方程式として再利用可能にしつつ、最終 FLT5 statement では零を除外する設計である。

### `PositiveFermat5Refuter`

0417 の定義文自体は `PositiveFermat5Refuter` を直接参照しない。しかし右辺の proposition は同一であり、直後の conditional receiver が `PositiveFermat5Refuter` を返す既存 theorem をそのまま `FLT5Target` の証明として利用できる。

これは `abbrev` の透過性を利用した module-boundary bridge である。

## 構築の流れ

`abbrev` なので proof script は存在しない。型の構造を順に読むとよい。

### 1. 三つの自然数を任意に取る

```lean
∀ x y z : ℕ,
```

最終公開 API なので binder は implicit ではなく explicit である。

### 2. 正値性を仮定する

```lean
0 < x → 0 < y → 0 < z →
```

これにより対象を $\mathbb N_{>0}$ に制限する。

### 3. Fermat 方程式を否定する

```lean
¬ Fermat5Equation x y z
```

Lean では `¬ P` は `P → False` なので、展開後の target は実質的に

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z →
  Fermat5Equation x y z → False
```

である。

この形は、正の候補解を受け取って primitive normalization、golden-order factorization、unit-class elimination、zero-sector descent を経て contradiction を返す証明全体の関数型と一致する。

## Lean 固有の処理

### `abbrev` の reducibility

`FLT5Target` は `def` ではなく `abbrev` であるため、Lean は型合わせの際に右辺へ透過的に展開しやすい。

このため直後の theorem では

```lean
: FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

と書くだけでよく、`change` や `unfold FLT5Target`、あるいは `simpa [FLT5Target, PositiveFermat5Refuter]` を明示する必要がない。

つまり、同じ proposition shape を持つ `PositiveFermat5Refuter` と `FLT5Target` の間で definitional equality が働いている。

### `¬ P` の関数型

Lean の否定

```lean
¬ P
```

は

```lean
P → False
```

である。

従って `flt5Target` は最終的に

```lean
flt5Target x y z hx hy hz hEq
```

のように適用すれば `False` を返す refuter として動作する。

後続の

```lean
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz
```

はこの curried structure をそのまま通常引数 theorem として公開する wrapper である。

### proposition alias と theorem inhabitant の分離

Lean では

```lean
abbrev FLT5Target : Prop := ...
```

と

```lean
theorem flt5Target : FLT5Target := ...
```

を別宣言にできる。

前者は specification、後者は proof object である。この分離により conditional receiver 群もすべて同じ target type を返す形で整理できる。

## 冗長・重複箇所

最も明確な重複は 0407 `PositiveFermat5Refuter` と右辺が同一であることだ。

両者は実質的に

$$
\mathrm{PositiveFermat5Refuter}
\equiv
\mathrm{FLT5Target}
$$

である。

コード量だけを見れば二重定義だが、役割は異なる。

- `PositiveFermat5Refuter` は `SignedGoldenClosure.lean` の内部 closure interface
- `FLT5Target` は `Main.lean` の最終公開 statement

したがって、同じ論理型を module boundary ごとに名前付けする設計と解釈できる。

また `FLT5Target` と直後の `fermatFive_no_positive_solution` も数学的内容は同じである。前者は proposition alias、後者は通常の theorem application に適した wrapper なので、これも API ergonomics のための意図的重複である。

## 最適化候補

### 1. `PositiveFermat5Refuter` への alias 化

重複を最小化するなら

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

とできる。

これなら最終命題の shape は一箇所だけになる。

ただし `Main.lean` を単独で読んだときに

$$
x^5+y^5\ne z^5
$$

という最終 statement がその場で見えなくなる。公開 endpoint の自己記述性を優先するなら現状の明示定義には十分な意味がある。

### 2. 共通 alias の導入

さらに一般化するなら `PositiveFermat5EquationRefuter` のような一つの alias を Basic 層で定義し、closure と Main の両方から参照する設計も可能である。

しかしこの規模では abstraction layer を一つ増やす方が読解コストを上げる可能性がある。

### 3. `FLT5Target` と ordinary wrapper の統合

最終 theorem を直接

```lean
theorem flt5Target
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z := ...
```

とすることもできる。

しかし現在の設計では conditional receiver 群が共通して `FLT5Target` を返せるため、target alias を独立させた方が proof pipeline の構造が明瞭である。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0417 自身が直接利用する Lean / Mathlib 要素は極めて基本的である。

- `ℕ`
- `<`
- `Prop`
- `¬`
- 全称量化と implication
- 先行定義 `Fermat5Equation`

高度な algebra、number theory、valuation、tactic はこの宣言自体には不要である。

分割ソース上では `Fermat5Equation` を提供する Basic 層への依存が本質である。

### import 最適化候補

この `abbrev` 単独のために `import Mathlib` 全体を要求する理由はない。

ただし Basic 層の実際の import closure を含めた最小 Mathlib module 名は、Lean build を行わない今回の条件では確認していない。従って、具体的な最小 import への削減案は未検証である。

確実に言えるのは、0417 自身には tactic import や valuation 固有 import は必要なく、依存の中心は `Fermat5Equation` の提供元であるという点までである。

## Comparator challenge 化の可否

**単独 challenge 化は可能だが、難度は非常に低い。**

`FLT5Target` は proof を含まない proposition alias なので、例えば

```lean
example : FLT5Target ↔
    (∀ x y z : ℕ,
      0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z) := by
  rfl
```

はほぼ definitional equality の確認だけで終わる。

より意味のある Comparator challenge にするなら、0418 `flt5Target_of_unitClasses_of_zeroArithmetic` と組み合わせ、

```lean
(hClasses : GoldenUnitClassesModFifth)
(hArithmetic : GoldenZeroSectorArithmeticExclusion)
```

から `FLT5Target` を構築させる方がよい。これなら内部 closure theorem と公開 target の接続を理解する必要がある。

さらに難度を上げるなら conditional receiver 群から unconditional `flt5Target` までを穴埋め対象にすると、proof architecture の最終合成を challenge 化できる。

## 次に読むべき宣言

次は 0418

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

である。

0417 が最終 target の **型** を定義したのに対し、0418 はその最初の **inhabitant constructor** である。

そこで初めて

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

という Main 層の conditional endpoint が構築される。

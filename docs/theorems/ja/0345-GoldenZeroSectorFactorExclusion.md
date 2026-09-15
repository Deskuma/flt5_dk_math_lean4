# 0345 — `GoldenZeroSectorFactorExclusion`

## 宣言種別

この宣言は **`abbrev`** である。

```lean
/-- Exclusion of every certified exact factor branch. -/
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

`theorem` や `def` ではなく、既存の命題型に短い名前を与える reducible な省略定義である。

## Lean の型

宣言そのものの型は

```lean
GoldenZeroSectorFactorExclusion : Prop
```

であり、展開すると

```lean
GoldenZeroSectorFactorPacket → False
```

である。

したがって `h : GoldenZeroSectorFactorExclusion` は、任意の

```lean
p : GoldenZeroSectorFactorPacket
```

を受け取って `False` を返す関数、すなわち certified exact factor packet が存在しないことの証明である。

## 数学的意味

`GoldenZeroSectorFactorPacket` は、zero-sector inversion packet と、それに従属する exact factor data を一つに束ねた構造である。その factor data は既に

- odd branch,
- even-left-low branch,
- even-right-low branch

の三つに完全分類されている。

したがって

$$
\operatorname{GoldenZeroSectorFactorPacket}\to\bot
$$

という命題は、これら三種類の certified exact factorization が **いずれも成立し得ない** ことを意味する。

この宣言自体は三分岐を排除する証明をまだ与えない。後続が満たすべき「排除契約」の型を命名しているだけである。

## 証明全体での役割

0344 `nonempty_goldenZeroSectorFactorPacket` までで、任意の raw zero-sector candidate から exact factor packet が少なくとも一つ得られることが確立された。

今回の 0345 は、その pipeline の向きを反転させる論理的な受け口を定義する。

前段は

$$
\text{raw candidate}
\longrightarrow
\operatorname{Nonempty}(\text{factor packet})
$$

を与え、後段は

$$
\text{factor packet}
\longrightarrow
\bot
$$

を与えることを目標とする。

両者を接続すれば、raw candidate 自体を排除できる。

したがってこの `abbrev` は、factorization 構築層と exclusion / closure 層の **論理インターフェース** である。

## 直接依存する定義・補題

直接依存するユーザー定義は

- 0337 `GoldenZeroSectorFactorPacket`

だけである。

Lean 基盤側では

- `Prop`
- `False`
- 関数型 `→`

だけを使用する。

0344 `nonempty_goldenZeroSectorFactorPacket` は証明全体では直前の重要な入力だが、この `abbrev` の定義本体から直接参照されてはいない。

また 0334 `GoldenZeroSectorFactorData` や三つの constructor も `GoldenZeroSectorFactorPacket` の内部に封じ込められているため、本宣言はそれらを直接知らない。

## 構築の流れ

この宣言には tactic proof は存在しない。

右辺

```lean
GoldenZeroSectorFactorPacket → False
```

を `GoldenZeroSectorFactorExclusion` という名前に結び付けるだけである。

概念的には次の一段だけである。

1. exact factor packet を仮定する。
2. その packet から矛盾を導ける、という命題型を定義する。

実際の「どのように矛盾を導くか」は後続 theorem の責務である。

## Lean 固有の処理

### `abbrev` の意味

`abbrev` は Lean では定義だが、通常の `def` より積極的に展開される reducible abbreviation として扱われる。

そのため

```lean
h : GoldenZeroSectorFactorExclusion
```

は多くの場面でそのまま関数として

```lean
h packet
```

と適用できる。

明示的に

```lean
show GoldenZeroSectorFactorPacket → False from h
```

のような変換を挟む必要は通常ない。

### `P → False` と否定

Lean では

```lean
Not P
```

は定義的に

```lean
P → False
```

である。

したがって本 contract は数学的には

```lean
¬ GoldenZeroSectorFactorPacket
```

と同じ否定構造を持つ。

ただし現行コードは `GoldenZeroSectorFactorExclusion` という専用名を与えることで、「単なる型の非存在」ではなく zero-sector factorization pipeline の exclusion interface であることを明示している。

## 冗長・重複箇所

コード量としての冗長性はない。

理論上は

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  ¬ GoldenZeroSectorFactorPacket
```

とも書ける。`¬ P` は `P → False` なので意味は同じである。

現行の

```lean
GoldenZeroSectorFactorPacket → False
```

という形は、後続で `hFactor packet` と関数適用する用途を視覚的に示しやすいという利点がある。

また専用 `abbrev` を作らず後続 theorem の引数に直接

```lean
hFactor : GoldenZeroSectorFactorPacket → False
```

と書くこともできる。しかし contract 名を付けることで module boundary と証明責務が明確になるため、重複というより API 設計上の命名である。

## 最適化候補

局所的な最適化はほぼ不要である。

候補を挙げるなら、否定であることを前面に出すため

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  ¬ GoldenZeroSectorFactorPacket
```

とする表記上の変更は可能である。

しかし後続コードが「packet を受け取って contradiction を返す contract」として扱うなら、現行の arrow form の方が operational な意味を読み取りやすい。

もう一つの設計候補は `class` や `structure` として exclusion evidence を包装することだが、この contract は単一命題しか持たないため過剰設計になる。現行 `abbrev` が最小で自然である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

しかし本宣言単体で Mathlib 固有の定理や tactic は使用していない。必要なのは Lean の基盤に属する

- `Prop`
- `False`
- implication / function type
- `abbrev`

と、プロジェクト側の `GoldenZeroSectorFactorPacket` だけである。

したがって本宣言自身を理由に `Mathlib` 全体を import する必要はない。

実際の module import 最適化では、`GoldenZeroSectorFactorPacket` を提供する signed golden factorization module の依存グラフを基準に最小化する必要がある。

具体的な最小 Mathlib import 名は Lean ビルドを行っていないため未確認であり、ここでは断定しない。

## Comparator challenge 化の可否

**可能だが、単独では極めて初級である。**

例えば

```lean
abbrev Challenge : Prop :=
  GoldenZeroSectorFactorPacket → False
```

という穴埋めは、`abbrev` と否定型の理解を確認するだけの問題になる。

より有用な Comparator challenge にするなら、0344 と組み合わせて

```lean
variable
  (hExists : Nonempty GoldenZeroSectorFactorPacket)
  (hExclude : GoldenZeroSectorFactorExclusion)

example : False := by
  -- fill here
```

とする方がよい。

ここでは `Nonempty` から packet witness を取り出し、`hExclude` に適用して contradiction を閉じる必要がある。factorization 層と exclusion contract の接続を理解しているかを確認できる。

## 次に読むべき宣言

次は

```lean
/-- The raw arithmetic contract, repeated here to preserve the acyclic dependency
 direction from inversion to factorization. -/
abbrev GoldenZeroSectorFactorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    ...
```

である。

宣言種別は **`abbrev`**。

0345 が certified factor packet を入力とする最も圧縮された exclusion contract だったのに対し、次の宣言は元の整数・自然数データとその算術条件を直接並べた **raw arithmetic exclusion contract** を定義する。

その後、この二つを接続する

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

へ進むことが Lean 正本で確認できる。

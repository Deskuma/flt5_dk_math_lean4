# 0407 `PositiveFermat5Refuter`

## 宣言種別

`abbrev`

## Lean の型

```lean
/-- A primitive-packet refuter is sufficient for all positive Fermat-five data. -/
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

## 数学的主張・宣言の意味

`PositiveFermat5Refuter` は theorem ではなく、正の自然数における FLT5 の最終的な否定命題を名前付きで公開する `abbrev` である。

展開すると

$$
\forall x,y,z\in\mathbb N,
\quad
x>0\to y>0\to z>0\to
\neg\bigl(x^5+y^5=z^5\bigr)
$$

である。

ここで `Fermat5Equation x y z` は

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

なので、`PositiveFermat5Refuter` はまさに

$$
x,y,z\in\mathbb N_{>0}
\Longrightarrow
x^5+y^5\ne z^5
$$

という指数 5 の正整数版 Fermat 命題を表す。

ただし、この宣言そのものは証明を与えない。「正の FLT5 解をすべて排除する証明はどの型を持つべきか」を interface として固定するだけである。

## 証明全体での役割

直前の 0406 `exists_counterexamplePack_of_positive_fermat5` は、任意の正整数解

$$
x^5+y^5=z^5
$$

から gcd normalization により primitive packet

$$
\mathrm{CounterexamplePack}(x',y',z')
$$

を構成できることを示した。

一方、0403 以降で構築してきた `CounterexamplePackRefuter` は

$$
\forall x',y',z',
\quad
\mathrm{CounterexamplePack}(x',y',z')\to\bot
$$

という primitive 層の refuter である。

`PositiveFermat5Refuter` は、この二層を接続した後に到達する **正整数 FLT5 の公開 closure 型** である。

実際、直後の theorem

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

は 0406 と primitive refuter を合成して、この `PositiveFermat5Refuter` の inhabitant を構築する。

したがって証明全体の大きな流れは

$$
\text{positive solution}
\longrightarrow
\text{primitive normalization}
\longrightarrow
\text{CounterexamplePack}
\longrightarrow
\bot
$$

であり、その最終的な関数型を `PositiveFermat5Refuter` が表している。

さらに `Main.lean` 側の

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

は論理的に同じ shape を持つため、`PositiveFermat5Refuter` は closure module と final public target の間をつなぐ内部 API と見ることもできる。

## 直接依存する定義・補題

### `Fermat5Equation`

この `abbrev` が直接参照する DkMath 固有定義である。

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

したがって

```lean
¬ Fermat5Equation x y z
```

は定義展開すれば

$$
x^5+y^5\ne z^5
$$

である。

### `ℕ`

対象領域は自然数である。signed integer や一般環上の FLT 命題ではない。

### positivity hypotheses

```lean
0 < x → 0 < y → 0 < z →
```

を命題の外側に明示している。

`Fermat5Equation` 自体には positivity が含まれていないため、0 を含む自明な等式と区別するためにこの三条件が必要である。

### `¬`

Lean では

```lean
¬ P
```

は定義上

```lean
P → False
```

である。

従って `PositiveFermat5Refuter` は、正の `x y z` と `hEq : Fermat5Equation x y z` を受け取り `False` を返す関数型としてそのまま利用できる。

この宣言自体は 0406 `exists_counterexamplePack_of_positive_fermat5` や `CounterexamplePackRefuter` を直接参照しない。それらは直後の theorem がこの interface の inhabitant を構築するときに用いる。

## 構築の流れ

`abbrev` なので証明スクリプトは存在しない。型を段階的に読むと構造が明快である。

### 1. 任意の三つの自然数を量化する

```lean
∀ x y z : ℕ,
```

ここでは `CounterexamplePackRefuter` と違い `x y z` は explicit binder である。

最終利用側で

```lean
flt5Target x y z hx hy hz
```

のように通常の引数として適用しやすい形になっている。

### 2. 正値条件を受け取る

```lean
0 < x → 0 < y → 0 < z →
```

指数 5 の正整数解だけを対象とする。

### 3. 方程式を否定する

```lean
¬ Fermat5Equation x y z
```

つまり仮に

```lean
hEq : Fermat5Equation x y z
```

が与えられたら `False` を返す。

依存関数型として書けば概念的には

$$
\prod_{x,y,z:\mathbb N}
\bigl(x>0\bigr)\to
\bigl(y>0\bigr)\to
\bigl(z>0\bigr)\to
\bigl(\mathrm{Fermat5Equation}(x,y,z)\to\bot\bigr)
$$

である。

## Lean 固有の処理

### `abbrev` の reducibility

`def` ではなく `abbrev` を使っているため、Lean は必要に応じて右辺の関数型へ容易に展開できる。

そのため直後の theorem は

```lean
(hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
```

と、`unfold PositiveFermat5Refuter` を明示せず証明を開始できる。

この用途では opaque な定義ではなく、interface alias として reducible な `abbrev` がよく合っている。

### `¬ P` は `P → False`

後続 proof の

```lean
intro ... hEq
```

で `hEq` まで導入できるのは、最終項 `¬ Fermat5Equation x y z` が関数型に展開されるためである。

### explicit binder

`CounterexamplePackRefuter` は

```lean
∀ {x y z : ℕ}, ...
```

と implicit binder を使っていたが、こちらは

```lean
∀ x y z : ℕ, ...
```

である。

最終 theorem の API として数値三つ組を明示的に渡す設計であり、`fermatFive_no_positive_solution x y z ...` のような ordinary-argument wrapper と自然に整合する。

### Curry 化された positivity

positivity は conjunction

```lean
0 < x ∧ 0 < y ∧ 0 < z
```

としてまとめず、三つの implication として並べている。

Lean の theorem 適用時に

```lean
h x y z hx hy hz
```

と直接使えるため、closure API として扱いやすい。

## 冗長・重複箇所

最大の重複は、後の `Main.lean` にある

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

と `PositiveFermat5Refuter` の右辺が事実上同一である点である。

したがって論理型としては

$$
\mathrm{PositiveFermat5Refuter}
\equiv
\mathrm{FLT5Target}
$$

である。

ただしこれは必ずしも悪い重複ではない。

- `PositiveFermat5Refuter` は `SignedGoldenClosure.lean` の内部 closure boundary
- `FLT5Target` は `Main.lean` の最終公開 target

という役割差があり、モジュール境界を名前で明示するために同じ shape を別名で持つ設計には意味がある。

また 0403 `CounterexamplePackRefuter` とも「refuter を名前付き `Prop` として固定する」という設計パターンが重複する。

## 最適化候補

### 1. `FLT5Target` への alias 化

コード量だけを減らすなら、後の `FLT5Target` を

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

とすることは可能である。

これなら最終 target の shape を一箇所に集約できる。

一方で `Main.lean` 単体を読んだ際に最終命題がその場で見えなくなるため、可読性とのトレードオフがある。

現状の数行程度の重複なら、公開 theorem の self-contained 性を優先して残す判断も十分合理的である。

### 2. positivity bundle 化

例えば

```lean
structure PositiveTriple where
  x y z : ℕ
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
```

のようにまとめる設計も可能だが、この証明では既存 theorem が `x y z hx hy hz` 形式を多用するため、bundle 化は projection と再梱包を増やす可能性が高い。

現状の curried API の方が軽量である。

### 3. `¬` と `→ False` の統一

`CounterexamplePackRefuter` は

```lean
CounterexamplePack x y z → False
```

と書き、こちらは

```lean
¬ Fermat5Equation x y z
```

と書いている。

論理的には同一表現だが、前者は refuter 関数として、後者は「方程式が成り立たない」という数学的 statement として読みやすい。それぞれの文脈に適した表記なので、無理に統一する必要はない。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

しかし `PositiveFermat5Refuter` 自身が直接必要とするものは非常に少ない。

- `ℕ`
- `<`
- `Prop`
- `¬`
- 全称量化と関数型
- 先行定義 `Fermat5Equation`

のみである。

`Fermat5Equation` は `DkMath/FLT/Five/Basic.lean` 由来なので、分割モジュール側では基本的には Basic module への依存だけで意味が完結する。

### import 最適化候補

この `abbrev` 単独のために `import Mathlib` 全体は不要である。

ただし実際の最小 import は `Fermat5Equation` を定義する Basic module 全体の依存を含めて決める必要がある。今回は Lean build を行わないため、`Mathlib` のどの細分 module まで削れるかは確認していない。

従って確実に言えるのは、

- standalone は `import Mathlib`
- 0407 の宣言自身には高度な Mathlib theorem/tactic 依存はない
- 最小 import の具体名は未検証

までである。

## Comparator challenge 化の可否

**単独 challenge としては可能だが、難度は極めて低い。**

`abbrev` 自体は proof を含まないため、例えば

```lean
example : PositiveFermat5Refuter ↔
    (∀ x y z : ℕ,
      0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z) := by
  rfl
```

は reducibility の確認だけで解ける。

従って数論 challenge としては弱い。

Comparator 用には直後の

```lean
positiveFermat5Refuter_of_counterexamplePackRefuter
```

と組み合わせる方が有益である。そこでは

1. positive solution を仮定する。
2. 0406 で primitive `CounterexamplePack` を抽出する。
3. `CounterexamplePackRefuter` を適用して矛盾を得る。

という proof architecture が明確に現れる。

評価すると、

- definitional equality challenge: 可
- proof search challenge: ほぼ無し
- closure architecture challenge の interface として: 重要

である。

## 次に読むべき宣言

次は

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

である。

0407 は「正整数 FLT5 を否定する証明」の **型だけを定義** した。

次の theorem は、0406 の normalization theorem と 0403 系統の primitive refuter を実際に合成し、その型の inhabitant を構築する。

証明の流れは

$$
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

であり、さらに展開すれば

$$
\text{positive FLT5 solution}
\Longrightarrow
\text{primitive packet}
\Longrightarrow
\bot
$$

となる。

ここは primitive proof から unrestricted positive target へ戻る normalization closure の最終橋である。
